// "Create property 'foo'" "true"
// ERROR: Property must be initialized
// K2_AFTER_ERROR: Property must be initialized.

interface FaceToDelegateTo
class DelegatedClass : FaceToDelegateTo by fo<caret>o

// FUS_QUICKFIX_NAME: org.jetbrains.kotlin.idea.quickfix.createFromUsage.createCallable.CreateCallableFromUsageFix
// FUS_K2_QUICKFIX_NAME: org.jetbrains.kotlin.idea.k2.codeinsight.quickFixes.createFromUsage.K2CreatePropertyFromUsageBuilder$CreatePropertyFromUsageAction