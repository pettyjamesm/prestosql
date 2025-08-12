/*
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package io.trino.operator;

import com.google.common.cache.CacheBuilder;
import com.google.common.cache.CacheLoader;
import com.google.common.cache.LoadingCache;
import com.google.common.collect.ImmutableList;
import io.airlift.bytecode.BytecodeBlock;
import io.airlift.bytecode.ClassDefinition;
import io.airlift.bytecode.DynamicClassLoader;
import io.airlift.bytecode.FieldDefinition;
import io.airlift.bytecode.MethodDefinition;
import io.airlift.bytecode.Parameter;
import io.airlift.bytecode.Scope;
import io.airlift.bytecode.Variable;
import io.airlift.bytecode.control.ForLoop;
import io.airlift.bytecode.control.IfStatement;
import io.airlift.bytecode.expression.BytecodeExpression;
import io.trino.operator.scalar.CombineHashFunction;
import io.trino.spi.block.Block;
import io.trino.spi.block.RunLengthEncodedBlock;
import io.trino.spi.type.ArrayType;
import io.trino.spi.type.CharType;
import io.trino.spi.type.Type;
import io.trino.spi.type.TypeOperators;
import io.trino.spi.type.VarbinaryType;
import io.trino.spi.type.VarcharType;
import io.trino.sql.gen.Binding;
import io.trino.sql.gen.CallSiteBinder;
import jakarta.inject.Inject;

import java.util.Arrays;
import java.util.List;
import java.util.Objects;

import static com.google.common.base.Preconditions.checkArgument;
import static io.airlift.bytecode.Access.FINAL;
import static io.airlift.bytecode.Access.PRIVATE;
import static io.airlift.bytecode.Access.PUBLIC;
import static io.airlift.bytecode.Access.a;
import static io.airlift.bytecode.Parameter.arg;
import static io.airlift.bytecode.ParameterizedType.type;
import static io.airlift.bytecode.expression.BytecodeExpressions.add;
import static io.airlift.bytecode.expression.BytecodeExpressions.and;
import static io.airlift.bytecode.expression.BytecodeExpressions.constantInt;
import static io.airlift.bytecode.expression.BytecodeExpressions.constantLong;
import static io.airlift.bytecode.expression.BytecodeExpressions.invokeDynamic;
import static io.airlift.bytecode.expression.BytecodeExpressions.invokeStatic;
import static io.airlift.bytecode.expression.BytecodeExpressions.lessThan;
import static io.trino.cache.SafeCaches.buildNonEvictableCache;
import static io.trino.spi.function.InvocationConvention.InvocationArgumentConvention.BLOCK_POSITION_NOT_NULL;
import static io.trino.spi.function.InvocationConvention.InvocationReturnConvention.FAIL_ON_NULL;
import static io.trino.spi.function.InvocationConvention.simpleConvention;
import static io.trino.spi.type.TypeUtils.NULL_HASH_CODE;
import static io.trino.spi.type.VarbinaryType.VARBINARY;
import static io.trino.spi.type.VarcharType.VARCHAR;
import static io.trino.sql.gen.Bootstrap.BOOTSTRAP_METHOD;
import static io.trino.sql.gen.BytecodeUtils.loadConstant;
import static io.trino.util.CompilerUtils.defineClass;
import static io.trino.util.CompilerUtils.makeClassName;
import static java.util.Objects.requireNonNull;

public final class HashGeneratorCompiler
{
    private static final CharType NORMALIZED_CHAR = CharType.createCharType(1);

    private final TypeOperators typeOperators;
    private final LoadingCache<Type, ColumnHasher> columnHashers;

    @Inject
    public HashGeneratorCompiler(TypeOperators typeOperators)
    {
        this.typeOperators = requireNonNull(typeOperators, "typeOperators is null");
        this.columnHashers = buildNonEvictableCache(
                CacheBuilder.newBuilder()
                        .recordStats()
                        .maximumSize(1000),
                CacheLoader.from(this::createColumnHasherInternal));
    }

    public ColumnHasher getColumnHasher(Type type)
    {
        return columnHashers.getUnchecked(normalizeType(type));
    }

    // Simplify trivial parameterized types to values that are equivalent for the purposes of hash code calculations to increase the cache hit rate
    private static Type normalizeType(Type type)
    {
        requireNonNull(type, "type is null");
        return switch (type) {
            case VarbinaryType _ -> VARBINARY;
            case VarcharType _ -> VARCHAR;
            case CharType _ -> NORMALIZED_CHAR;
            case ArrayType arrayType -> {
                Type normalizedElementType = normalizeType(arrayType.getElementType());
                if (normalizedElementType == arrayType.getElementType()) {
                    yield arrayType; // no change after normalization
                }
                yield new ArrayType(normalizedElementType);
            }
            default -> type;
        };
    }

    private ColumnHasher createColumnHasherInternal(Type type)
    {
        CallSiteBinder callSiteBinder = new CallSiteBinder();
        ClassDefinition definition = new ClassDefinition(
                a(PUBLIC, FINAL),
                makeClassName("ColumnHasher_" + type),
                type(Object.class),
                type(ColumnHasher.class));
        // the 'types' field is not used, but it makes debugging easier
        // this is an instance field because a static field doesn't seem to show up in the IntelliJ debugger
        FieldDefinition typeField = definition.declareField(a(PRIVATE, FINAL), "type", type(Type.class));
        MethodDefinition constructor = definition.declareConstructor(a(PUBLIC));
        constructor
                .getBody()
                .append(constructor.getThis())
                .invokeConstructor(Object.class)
                .append(constructor.getThis().setField(typeField, loadConstant(callSiteBinder, type, Type.class)))
                .ret();

        Binding hashBlock = callSiteBinder.bind(typeOperators.getHashCodeOperator(type, simpleConvention(FAIL_ON_NULL, BLOCK_POSITION_NOT_NULL)));
        generateHashBlockMethod(definition, hashBlock, true);
        generateHashBlockMethod(definition, hashBlock, false);

        DynamicClassLoader classLoader = new DynamicClassLoader(HashGeneratorCompiler.class.getClassLoader(), callSiteBinder.getBindings());
        try {
            return defineClass(definition, ColumnHasher.class, classLoader)
                    .getConstructor()
                    .newInstance();
        }
        catch (ReflectiveOperationException e) {
            throw new RuntimeException(e);
        }
    }

    private static MethodDefinition generateHashBlockMethod(ClassDefinition definition, Binding hashBlock, boolean firstColumn)
    {
        Parameter block = arg("block", type(Block.class));
        Parameter hashes = arg("hashes", type(long[].class));
        Parameter offset = arg("offset", type(int.class));
        Parameter length = arg("length", type(int.class));

        MethodDefinition methodDefinition = definition.declareMethod(
                a(PUBLIC, FINAL),
                firstColumn ? "hashFirst" : "hashAndCombine",
                type(void.class),
                block,
                hashes,
                offset,
                length);

        Scope scope = methodDefinition.getScope();
        BytecodeBlock body = methodDefinition.getBody();

        Variable index = scope.declareVariable(int.class, "index");
        Variable position = scope.declareVariable(int.class, "position");
        Variable mayHaveNull = scope.declareVariable(boolean.class, "mayHaveNull");
        Variable hash = scope.declareVariable(long.class, "hash");

        body.append(position.set(invokeStatic(Objects.class, "checkFromToIndex", int.class, offset, add(offset, length), block.invoke("getPositionCount", int.class))));
        body.append(invokeStatic(Objects.class, "checkFromIndexSize", int.class, constantInt(0), length, hashes.length()).pop());

        BytecodeExpression computeHashNonNull = invokeDynamic(
                BOOTSTRAP_METHOD,
                ImmutableList.of(hashBlock.getBindingId()),
                "hash",
                long.class,
                block,
                position);

        BytecodeBlock rleHandling = new BytecodeBlock()
                .append(new IfStatement("hash = block.isNull(position) ? NULL_HASH_CODE : hash(block, position)")
                        .condition(block.invoke("isNull", boolean.class, position))
                        .ifTrue(hash.set(constantLong(NULL_HASH_CODE)))
                        .ifFalse(hash.set(computeHashNonNull)));
        if (firstColumn) {
            // Arrays.fill(hashes, 0, length, hash)
            rleHandling.append(invokeStatic(Arrays.class, "fill", void.class, hashes, constantInt(0), length, hash));
        }
        else {
            // CombineHashFunction.combineAllHashesWithConstant(hashes, 0, length, hash)
            rleHandling.append(invokeStatic(CombineHashFunction.class, "combineAllHashesWithConstant", void.class, hashes, constantInt(0), length, hash));
        }

        BytecodeExpression setHashExpression;
        if (firstColumn) {
            // hashes[index] = hash;
            setHashExpression = hashes.setElement(index, hash);
        }
        else {
            // hashes[index] = CombineHashFunction.getHash(hashes[index], hash);
            setHashExpression = hashes.setElement(index, invokeStatic(CombineHashFunction.class, "getHash", long.class, hashes.getElement(index), hash));
        }

        BytecodeBlock computeHashLoop = new BytecodeBlock()
                .append(mayHaveNull.set(block.invoke("mayHaveNull", boolean.class)))
                .append(new ForLoop("for (int index = 0; index < length; index++)")
                        .initialize(index.set(constantInt(0)))
                        .condition(lessThan(index, length))
                        .update(index.increment())
                        .body(new BytecodeBlock()
                                .append(new IfStatement("if (mayHaveNull && block.isNull(position))")
                                        .condition(and(mayHaveNull, block.invoke("isNull", boolean.class, position)))
                                        .ifTrue(hash.set(constantLong(NULL_HASH_CODE)))
                                        .ifFalse(hash.set(computeHashNonNull)))
                                .append(setHashExpression)
                                .append(position.increment())));

        body.append(new IfStatement("if (block instanceof RunLengthEncodedBlock)")
                        .condition(block.instanceOf(RunLengthEncodedBlock.class))
                        .ifTrue(rleHandling)
                        .ifFalse(computeHashLoop))
                .ret();

        return methodDefinition;
    }

    public interface ColumnHasher
    {
        void hashFirst(Block block, long[] hashes, int offset, int length);

        void hashAndCombine(Block block, long[] hashes, int offset, int length);
    }

    public static final class ColumnarHashGenerator
    {
        private final ColumnHasher[] columnHashers;

        public ColumnarHashGenerator(List<ColumnHasher> columnHashers)
        {
            this.columnHashers = requireNonNull(columnHashers, "columnHashers is null").toArray(ColumnHasher[]::new);
        }

        public void hash(Block[] blocks, long[] hashes, int offset, int length)
        {
            checkArgument(blocks.length == columnHashers.length, "invalid block count");
            columnHashers[0].hashFirst(blocks[0], hashes, offset, length);
            for (int i = 1; i < columnHashers.length; i++) {
                columnHashers[i].hashAndCombine(blocks[i], hashes, offset, length);
            }
        }
    }
}
