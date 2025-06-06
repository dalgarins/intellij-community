// Copyright 2000-2025 JetBrains s.r.o. and contributors. Use of this source code is governed by the Apache 2.0 license.

package org.jetbrains.kotlin.idea.completion.test.handlers;

import com.intellij.testFramework.TestDataPath;
import org.jetbrains.kotlin.idea.base.plugin.KotlinPluginMode;
import org.jetbrains.kotlin.idea.base.test.TestRoot;
import org.jetbrains.kotlin.idea.test.JUnit3RunnerWithInners;
import org.jetbrains.kotlin.idea.test.KotlinTestUtils;
import org.jetbrains.kotlin.test.TestMetadata;
import org.junit.runner.RunWith;

/**
 * This class is generated by {@link org.jetbrains.kotlin.testGenerator.generator.TestGenerator}.
 * DO NOT MODIFY MANUALLY.
 */
@SuppressWarnings("all")
@TestRoot("completion/tests-k1")
@TestDataPath("$CONTENT_ROOT")
@RunWith(JUnit3RunnerWithInners.class)
@TestMetadata("../testData/handlers/keywords")
public class KeywordCompletionHandlerTestGenerated extends AbstractKeywordCompletionHandlerTest {
    @java.lang.Override
    @org.jetbrains.annotations.NotNull
    public final KotlinPluginMode getPluginMode() {
        return KotlinPluginMode.K1;
    }

    private void runTest(String testDataFilePath) throws Exception {
        KotlinTestUtils.runTest(this::doTest, this, testDataFilePath);
    }

    @TestMetadata("AddCompanionToObject.kt")
    public void testAddCompanionToObject() throws Exception {
        runTest("../testData/handlers/keywords/AddCompanionToObject.kt");
    }

    @TestMetadata("AutoIndentGetter.kt")
    public void testAutoIndentGetter() throws Exception {
        runTest("../testData/handlers/keywords/AutoIndentGetter.kt");
    }

    @TestMetadata("AutoIndentGetter2.kt")
    public void testAutoIndentGetter2() throws Exception {
        runTest("../testData/handlers/keywords/AutoIndentGetter2.kt");
    }

    @TestMetadata("AutoIndentGetter3.kt")
    public void testAutoIndentGetter3() throws Exception {
        runTest("../testData/handlers/keywords/AutoIndentGetter3.kt");
    }

    @TestMetadata("AutoIndentGetterAndModifier.kt")
    public void testAutoIndentGetterAndModifier() throws Exception {
        runTest("../testData/handlers/keywords/AutoIndentGetterAndModifier.kt");
    }

    @TestMetadata("AutoIndentGetterAndModifier2.kt")
    public void testAutoIndentGetterAndModifier2() throws Exception {
        runTest("../testData/handlers/keywords/AutoIndentGetterAndModifier2.kt");
    }

    @TestMetadata("AutoIndentGetterAndModifier3.kt")
    public void testAutoIndentGetterAndModifier3() throws Exception {
        runTest("../testData/handlers/keywords/AutoIndentGetterAndModifier3.kt");
    }

    @TestMetadata("AutoIndentSetter.kt")
    public void testAutoIndentSetter() throws Exception {
        runTest("../testData/handlers/keywords/AutoIndentSetter.kt");
    }

    @TestMetadata("AutoIndentSetter2.kt")
    public void testAutoIndentSetter2() throws Exception {
        runTest("../testData/handlers/keywords/AutoIndentSetter2.kt");
    }

    @TestMetadata("AutoIndentSetter3.kt")
    public void testAutoIndentSetter3() throws Exception {
        runTest("../testData/handlers/keywords/AutoIndentSetter3.kt");
    }

    @TestMetadata("AutoIndentSetterAndModifier.kt")
    public void testAutoIndentSetterAndModifier() throws Exception {
        runTest("../testData/handlers/keywords/AutoIndentSetterAndModifier.kt");
    }

    @TestMetadata("AutoIndentSetterAndModifier2.kt")
    public void testAutoIndentSetterAndModifier2() throws Exception {
        runTest("../testData/handlers/keywords/AutoIndentSetterAndModifier2.kt");
    }

    @TestMetadata("AutoIndentSetterAndModifier3.kt")
    public void testAutoIndentSetterAndModifier3() throws Exception {
        runTest("../testData/handlers/keywords/AutoIndentSetterAndModifier3.kt");
    }

    @TestMetadata("Break.kt")
    public void testBreak() throws Exception {
        runTest("../testData/handlers/keywords/Break.kt");
    }

    @TestMetadata("Catch.kt")
    public void testCatch() throws Exception {
        runTest("../testData/handlers/keywords/Catch.kt");
    }

    @TestMetadata("CompanionObject.kt")
    public void testCompanionObject() throws Exception {
        runTest("../testData/handlers/keywords/CompanionObject.kt");
    }

    @TestMetadata("Constructor.kt")
    public void testConstructor() throws Exception {
        runTest("../testData/handlers/keywords/Constructor.kt");
    }

    @TestMetadata("ConstructorPrimary.kt")
    public void testConstructorPrimary() throws Exception {
        runTest("../testData/handlers/keywords/ConstructorPrimary.kt");
    }

    @TestMetadata("Context.kt")
    public void testContext() throws Exception {
        runTest("../testData/handlers/keywords/Context.kt");
    }

    @TestMetadata("ContextWithoutDeclaration.kt")
    public void testContextWithoutDeclaration() throws Exception {
        runTest("../testData/handlers/keywords/ContextWithoutDeclaration.kt");
    }

    @TestMetadata("Do.kt")
    public void testDo() throws Exception {
        runTest("../testData/handlers/keywords/Do.kt");
    }

    @TestMetadata("FileKeyword.kt")
    public void testFileKeyword() throws Exception {
        runTest("../testData/handlers/keywords/FileKeyword.kt");
    }

    @TestMetadata("Finally.kt")
    public void testFinally() throws Exception {
        runTest("../testData/handlers/keywords/Finally.kt");
    }

    @TestMetadata("For.kt")
    public void testFor() throws Exception {
        runTest("../testData/handlers/keywords/For.kt");
    }

    @TestMetadata("Getter1.kt")
    public void testGetter1() throws Exception {
        runTest("../testData/handlers/keywords/Getter1.kt");
    }

    @TestMetadata("Getter2.kt")
    public void testGetter2() throws Exception {
        runTest("../testData/handlers/keywords/Getter2.kt");
    }

    @TestMetadata("If.kt")
    public void testIf() throws Exception {
        runTest("../testData/handlers/keywords/If.kt");
    }

    @TestMetadata("IfLParenth.kt")
    public void testIfLParenth() throws Exception {
        runTest("../testData/handlers/keywords/IfLParenth.kt");
    }

    @TestMetadata("IfParansOnNextLine.kt")
    public void testIfParansOnNextLine() throws Exception {
        runTest("../testData/handlers/keywords/IfParansOnNextLine.kt");
    }

    @TestMetadata("IfSpace.kt")
    public void testIfSpace() throws Exception {
        runTest("../testData/handlers/keywords/IfSpace.kt");
    }

    @TestMetadata("Init.kt")
    public void testInit() throws Exception {
        runTest("../testData/handlers/keywords/Init.kt");
    }

    @TestMetadata("NoSpaceAfterNull.kt")
    public void testNoSpaceAfterNull() throws Exception {
        runTest("../testData/handlers/keywords/NoSpaceAfterNull.kt");
    }

    @TestMetadata("QualifiedReturnNonUnit.kt")
    public void testQualifiedReturnNonUnit() throws Exception {
        runTest("../testData/handlers/keywords/QualifiedReturnNonUnit.kt");
    }

    @TestMetadata("QualifiedReturnNonUnitExplicit.kt")
    public void testQualifiedReturnNonUnitExplicit() throws Exception {
        runTest("../testData/handlers/keywords/QualifiedReturnNonUnitExplicit.kt");
    }

    @TestMetadata("QualifiedReturnUnit.kt")
    public void testQualifiedReturnUnit() throws Exception {
        runTest("../testData/handlers/keywords/QualifiedReturnUnit.kt");
    }

    @TestMetadata("ReturnEmptyList.kt")
    public void testReturnEmptyList() throws Exception {
        runTest("../testData/handlers/keywords/ReturnEmptyList.kt");
    }

    @TestMetadata("ReturnInEmptyType.kt")
    public void testReturnInEmptyType() throws Exception {
        runTest("../testData/handlers/keywords/ReturnInEmptyType.kt");
    }

    @TestMetadata("ReturnInProperty.kt")
    public void testReturnInProperty() throws Exception {
        runTest("../testData/handlers/keywords/ReturnInProperty.kt");
    }

    @TestMetadata("ReturnInTypeFunction.kt")
    public void testReturnInTypeFunction() throws Exception {
        runTest("../testData/handlers/keywords/ReturnInTypeFunction.kt");
    }

    @TestMetadata("ReturnInUnit.kt")
    public void testReturnInUnit() throws Exception {
        runTest("../testData/handlers/keywords/ReturnInUnit.kt");
    }

    @TestMetadata("ReturnNull.kt")
    public void testReturnNull() throws Exception {
        runTest("../testData/handlers/keywords/ReturnNull.kt");
    }

    @TestMetadata("Setter1.kt")
    public void testSetter1() throws Exception {
        runTest("../testData/handlers/keywords/Setter1.kt");
    }

    @TestMetadata("Setter2.kt")
    public void testSetter2() throws Exception {
        runTest("../testData/handlers/keywords/Setter2.kt");
    }

    @TestMetadata("SpaceAfterImport.kt")
    public void testSpaceAfterImport() throws Exception {
        runTest("../testData/handlers/keywords/SpaceAfterImport.kt");
    }

    @TestMetadata("Try.kt")
    public void testTry() throws Exception {
        runTest("../testData/handlers/keywords/Try.kt");
    }

    @TestMetadata("UseSiteAnnotationTarget1.kt")
    public void testUseSiteAnnotationTarget1() throws Exception {
        runTest("../testData/handlers/keywords/UseSiteAnnotationTarget1.kt");
    }

    @TestMetadata("UseSiteAnnotationTarget2.kt")
    public void testUseSiteAnnotationTarget2() throws Exception {
        runTest("../testData/handlers/keywords/UseSiteAnnotationTarget2.kt");
    }

    @TestMetadata("UseSiteAnnotationTarget3.kt")
    public void testUseSiteAnnotationTarget3() throws Exception {
        runTest("../testData/handlers/keywords/UseSiteAnnotationTarget3.kt");
    }

    @TestMetadata("While.kt")
    public void testWhile() throws Exception {
        runTest("../testData/handlers/keywords/While.kt");
    }
}
