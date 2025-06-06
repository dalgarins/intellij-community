// Copyright 2000-2025 JetBrains s.r.o. and contributors. Use of this source code is governed by the Apache 2.0 license.
package com.intellij.refactoring.changeSignature;

import com.intellij.lang.java.JavaLanguage;
import com.intellij.openapi.util.Comparing;
import com.intellij.psi.*;
import com.intellij.psi.impl.light.LightRecordCanonicalConstructor;
import com.intellij.psi.impl.light.LightRecordMethod;
import com.intellij.psi.javadoc.PsiDocTagValue;
import com.intellij.psi.search.GlobalSearchScope;
import com.intellij.psi.search.searches.FunctionalExpressionSearch;
import com.intellij.psi.search.searches.MethodReferencesSearch;
import com.intellij.psi.search.searches.OverridingMethodsSearch;
import com.intellij.psi.search.searches.ReferencesSearch;
import com.intellij.psi.util.JavaPsiPatternUtil;
import com.intellij.psi.util.JavaPsiRecordUtil;
import com.intellij.psi.xml.XmlElement;
import com.intellij.refactoring.RefactoringBundle;
import com.intellij.refactoring.rename.JavaUnresolvableLocalCollisionDetector;
import com.intellij.refactoring.rename.UnresolvableCollisionUsageInfo;
import com.intellij.refactoring.util.MoveRenameUsageInfo;
import com.intellij.refactoring.util.RefactoringUIUtil;
import com.intellij.usageView.UsageInfo;
import com.intellij.usageView.UsageViewUtil;
import com.intellij.util.containers.ContainerUtil;
import com.siyeh.ig.psiutils.VariableAccessUtils;
import org.jetbrains.annotations.NotNull;

import java.util.*;

/**
 * @author Maxim.Medvedev
 */
final class JavaChangeSignatureUsageSearcher {
  private final JavaChangeInfo myChangeInfo;

  JavaChangeSignatureUsageSearcher(JavaChangeInfo changeInfo) {
    this.myChangeInfo = changeInfo;
  }

  public UsageInfo[] findUsages() {
    ArrayList<UsageInfo> result = new ArrayList<>();
    final PsiMethod method = myChangeInfo.getMethod();

    findSimpleUsages(method, result);

    final UsageInfo[] usageInfos = result.toArray(UsageInfo.EMPTY_ARRAY);
    return UsageViewUtil.removeDuplicatedUsages(usageInfos);
  }


  private void findSimpleUsages(final PsiMethod method, final ArrayList<? super UsageInfo> result) {
    PsiMethod[] overridingMethods = findSimpleUsagesWithoutParameters(method, result, true, true, true);
    findUsagesInCallers(result);

    final ArrayList<PsiMethod> methods = new ArrayList<>(Arrays.asList(overridingMethods));
    methods.add(method);

    for (PsiMethod psiMethod : methods) {
      for (PsiFunctionalExpression functionalExpression : FunctionalExpressionSearch.search(psiMethod).asIterable()) {
        result.add(new FunctionalInterfaceChangedUsageInfo(functionalExpression, method));
      }
    }

    PsiDeconstructionPattern[] deconstructions = findDeconstructionUsages(method, result);

    //Parameter name changes are not propagated
    findParametersUsage(method, result, overridingMethods, deconstructions);
  }

  private static PsiDeconstructionPattern[] findDeconstructionUsages(final PsiMethod method, final ArrayList<? super UsageInfo> result) {
    if (!(JavaPsiRecordUtil.isCompactConstructor(method) ||
          JavaPsiRecordUtil.isExplicitCanonicalConstructor(method) ||
          method instanceof LightRecordCanonicalConstructor)) {
      return PsiDeconstructionPattern.EMPTY_ARRAY;
    }
    PsiClass aClass = method.getContainingClass();
    if (aClass == null) {
      return PsiDeconstructionPattern.EMPTY_ARRAY;
    }
    PsiParameter[] parameters = method.getParameterList().getParameters();
    List<PsiDeconstructionPattern> deconstructions = new ArrayList<>();
    GlobalSearchScope projectScope = GlobalSearchScope.projectScope(method.getProject());
    for (PsiReference reference : ReferencesSearch.search(aClass, projectScope).asIterable()) {
      PsiElement element = reference.getElement();
      PsiElement parent = element.getParent();
      if (!(parent instanceof PsiTypeElement)) {
        continue;
      }
      PsiElement grandParent = parent.getParent();
      if (grandParent instanceof PsiDeconstructionPattern) {
        if (isSuitableDeconstruction((PsiDeconstructionPattern)grandParent, parameters)) {
          result.add(new DeconstructionUsageInfo((PsiDeconstructionPattern)grandParent));
          deconstructions.add((PsiDeconstructionPattern)grandParent);
        }
      }
    }
    return deconstructions.toArray(PsiDeconstructionPattern.EMPTY_ARRAY);
  }

  private static boolean isSuitableDeconstruction(PsiDeconstructionPattern deconstruction, PsiParameter[] parameters) {
    PsiPattern[] components = deconstruction.getDeconstructionList().getDeconstructionComponents();
    if (components.length != parameters.length) {
      return false;
    }
    return true;
  }

  private void findUsagesInCallers(final ArrayList<? super UsageInfo> usages) {
    if (myChangeInfo instanceof JavaChangeInfoImpl changeInfo) {
      for (PsiMethod caller : changeInfo.propagateParametersMethods) {
        usages.add(new CallerUsageInfo(caller, true, changeInfo.propagateExceptionsMethods.contains(caller)));
      }
      for (PsiMethod caller : changeInfo.propagateExceptionsMethods) {
        usages.add(new CallerUsageInfo(caller, changeInfo.propagateParametersMethods.contains(caller), true));
      }
      Set<PsiMethod> merged = new HashSet<>();
      merged.addAll(changeInfo.propagateParametersMethods);
      merged.addAll(changeInfo.propagateExceptionsMethods);
      for (final PsiMethod method : merged) {
        findSimpleUsagesWithoutParameters(method, usages, changeInfo.propagateParametersMethods.contains(method),
                                          changeInfo.propagateExceptionsMethods.contains(method), false);
      }
    }
  }

  private void detectLocalsCollisionsInMethod(final PsiMethod method, final ArrayList<? super UsageInfo> result, boolean isOriginal) {
    if (!JavaLanguage.INSTANCE.equals(method.getLanguage())) return;

    final PsiParameter[] parameters = method.getParameterList().getParameters();
    final Set<PsiParameter> deletedOrRenamedParameters = new HashSet<>();
    if (isOriginal) {
      ContainerUtil.addAll(deletedOrRenamedParameters, parameters);
      for (ParameterInfo parameterInfo : myChangeInfo.getNewParameters()) {
        if (parameterInfo.getOldIndex() >= 0 && parameterInfo.getOldIndex() < parameters.length) {
          final PsiParameter parameter = parameters[parameterInfo.getOldIndex()];
          if (parameterInfo.getName().equals(parameter.getName())) {
            deletedOrRenamedParameters.remove(parameter);
          }
        }
      }
    }

    for (ParameterInfo parameterInfo : myChangeInfo.getNewParameters()) {
      final int oldParameterIndex = parameterInfo.getOldIndex();
      final String newName = parameterInfo.getName();
      if (oldParameterIndex >= 0 ) {
        if (isOriginal && oldParameterIndex < parameters.length && !newName.equals(myChangeInfo.getOldParameterNames()[oldParameterIndex])) {
          //Name changes take place only in primary method when name was actually changed
          final PsiParameter parameter = parameters[oldParameterIndex];
          if (!newName.equals(parameter.getName())) {
            JavaUnresolvableLocalCollisionDetector.visitLocalsCollisions(
              parameter, newName, method.getBody(), null,
              new JavaUnresolvableLocalCollisionDetector.CollidingVariableVisitor() {
                @Override
                public void visitCollidingElement(final PsiVariable collidingVariable) {
                  if (!deletedOrRenamedParameters.contains(collidingVariable)) {
                    result.add(new RenamedParameterCollidesWithLocalUsageInfo(parameter, collidingVariable, method));
                  }
                }
              });
          }
        }
      }
      else {
        JavaUnresolvableLocalCollisionDetector.visitLocalsCollisions(
          method, newName, method.getBody(), null,
          new JavaUnresolvableLocalCollisionDetector.CollidingVariableVisitor() {
            @Override
            public void visitCollidingElement(PsiVariable collidingVariable) {
              if (!deletedOrRenamedParameters.contains(collidingVariable)) {
                result.add(new NewParameterCollidesWithLocalUsageInfo(
                  collidingVariable, collidingVariable, method));
              }
            }
          });
      }
    }
  }

  private void findParametersUsage(final PsiMethod method,
                                   ArrayList<? super UsageInfo> result,
                                   PsiMethod[] overriders,
                                   PsiDeconstructionPattern[] deconstructions) {
    if (JavaLanguage.INSTANCE.equals(myChangeInfo.getLanguage())) {
      PsiClass aClass = method.getContainingClass();
      PsiRecordComponent[] components = null;
      if (aClass != null && JavaPsiRecordUtil.isCanonicalConstructor(method)) {
        components = aClass.getRecordComponents();
      } 
      PsiParameter[] parameters = method.getParameterList().getParameters();
      for (ParameterInfo info : myChangeInfo.getNewParameters()) {
        if (info.getOldIndex() >= 0) {
          PsiParameter parameter = parameters[info.getOldIndex()];
          boolean nameChanged = !info.getName().equals(parameter.getName());
          if (nameChanged) {
            addParameterUsages(parameter, result, info);
            for (PsiMethod overrider : overriders) {
              PsiParameter parameter1 = overrider.getParameterList().getParameters()[info.getOldIndex()];
              if (parameter1 != null && Comparing.strEqual(parameter.getName(), parameter1.getName())) {
                addParameterUsages(parameter1, result, info);
              }
            }
            for (PsiDeconstructionPattern deconstruction : deconstructions) {
              PsiPattern[] component = deconstruction.getDeconstructionList().getDeconstructionComponents();
              PsiPatternVariable patternVariable = JavaPsiPatternUtil.getPatternVariable(component[info.getOldIndex()]);
              if (patternVariable != null && Comparing.strEqual(parameter.getName(), patternVariable.getName())) {
                addParameterUsages(patternVariable, result, info);
              }
            }
          }
          if (components != null && components.length > info.getOldIndex()) {
            PsiRecordComponent component = components[info.getOldIndex()];
            if (nameChanged) {
              PsiField field = JavaPsiRecordUtil.getFieldForComponent(component);
              if (field != null) {
                for (PsiReferenceExpression reference : VariableAccessUtils.getVariableReferences(field, aClass)) {
                  UsageInfo usageInfo = new ChangeSignatureParameterUsageInfo(reference, parameter.getName(), info.getName());
                  result.add(usageInfo);
                }
              }
            }
            PsiMethod explicitGetter = ContainerUtil
              .find(aClass.findMethodsByName(parameter.getName(), false), m -> m.getParameterList().isEmpty());
            if (explicitGetter != null) {
              if (nameChanged) {
                addParameterUsages(explicitGetter, result, info);
              }
              if (!(explicitGetter instanceof LightRecordMethod) && 
                  (nameChanged || !parameter.getType().equalsToText(info.getTypeText()))) {
                result.add(new RecordGetterDeclarationUsageInfo(explicitGetter, info.getName(), info.getTypeText()));
              }
            }
          }
        }
      }
    }
  }

  private PsiMethod[] findSimpleUsagesWithoutParameters(final PsiMethod method,
                                                        final ArrayList<? super UsageInfo> result,
                                                        boolean isToModifyArgs,
                                                        boolean isToThrowExceptions,
                                                        boolean isOriginal) {

    GlobalSearchScope projectScope = GlobalSearchScope.projectScope(method.getProject());
    PsiMethod[] overridingMethods = OverridingMethodsSearch.search(method).toArray(PsiMethod.EMPTY_ARRAY);

    for (PsiMethod overridingMethod : overridingMethods) {
      ChangeSignatureUsageProvider provider = getProvider(overridingMethod);
      result.add(provider.createOverrideUsageInfo(myChangeInfo, overridingMethod, method, isOriginal, isToModifyArgs, isToThrowExceptions, result));
    }

    boolean needToChangeCalls =
      !myChangeInfo.isGenerateDelegate() && (myChangeInfo.isNameChanged() ||
                                             myChangeInfo.isParameterSetOrOrderChanged() ||
                                             myChangeInfo.isExceptionSetOrOrderChanged() ||
                                             myChangeInfo.isVisibilityChanged()/*for checking inaccessible*/);
    if (needToChangeCalls) {

      PsiReference[] refs = MethodReferencesSearch.search(method, projectScope, true).toArray(PsiReference.EMPTY_ARRAY);
      for (PsiReference ref : refs) {
        ChangeSignatureUsageProvider provider = getProvider(ref.getElement());
        ContainerUtil.addIfNotNull(result, provider.createUsageInfo(myChangeInfo, ref, method, isToModifyArgs, isToThrowExceptions));
      }

      //if (method.isConstructor() && parameterCount == 0) {
      //    RefactoringUtil.visitImplicitConstructorUsages(method.getContainingClass(),
      //                                                   new DefaultConstructorUsageCollector(result));
      //}
    }
    else if (myChangeInfo.isParameterTypesChanged()) {
      PsiReference[] refs = MethodReferencesSearch.search(method, projectScope, true).toArray(PsiReference.EMPTY_ARRAY);
      for (PsiReference reference : refs) {
        final PsiElement element = reference.getElement();
        if (element instanceof PsiDocTagValue) {
          result.add(new UsageInfo(reference));
        }
        else if (element instanceof XmlElement) {
          result.add(new MoveRenameUsageInfo(reference, method));
        }
        else if (element instanceof PsiMethodReferenceExpression) {
          result.add(new UsageInfo(reference));
        }
      }
    }

    // Conflicts
    detectLocalsCollisionsInMethod(method, result, isOriginal);
    for (final PsiMethod overridingMethod : overridingMethods) {
      detectLocalsCollisionsInMethod(overridingMethod, result, isOriginal);
    }

    return overridingMethods;
  }

  private static @NotNull ChangeSignatureUsageProvider getProvider(PsiElement element) {
    ChangeSignatureUsageProvider provider = ChangeSignatureUsageProviders.findProvider(element.getLanguage());
    if (provider == null) {
      provider = ChangeSignatureUsageProviders.findProvider(JavaLanguage.INSTANCE);
    }
    return Objects.requireNonNull(provider);
  }


  private static void addParameterUsages(PsiNamedElement parameter, ArrayList<? super UsageInfo> results, ParameterInfo info) {
    PsiManager manager = parameter.getManager();
    GlobalSearchScope projectScope = GlobalSearchScope.projectScope(manager.getProject());
    for (PsiReference psiReference : ReferencesSearch.search(parameter, projectScope, false).asIterable()) {
      PsiElement parmRef = psiReference.getElement();
      UsageInfo usageInfo = new ChangeSignatureParameterUsageInfo(parmRef, parameter.getName(), info.getName());
      results.add(usageInfo);
    }
  }

  private static class RenamedParameterCollidesWithLocalUsageInfo extends UnresolvableCollisionUsageInfo {
    private final PsiElement myCollidingElement;
    private final PsiMethod myMethod;

    RenamedParameterCollidesWithLocalUsageInfo(PsiParameter parameter, PsiElement collidingElement, PsiMethod method) {
      super(parameter, collidingElement);
      myCollidingElement = collidingElement;
      myMethod = method;
    }

    @Override
    public String getDescription() {
      return RefactoringBundle.message("there.is.already.a.0.in.the.1.it.will.conflict.with.the.renamed.parameter",
                                       RefactoringUIUtil.getDescription(myCollidingElement, true),
                                       RefactoringUIUtil.getDescription(myMethod, true));
    }
  }
}
