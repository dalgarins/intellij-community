// "Remove variable 'a'" "true"
var cnt = 5
fun getCnt() = cnt++
fun f() {
    var <caret>a = getCnt()
}
// FUS_QUICKFIX_NAME: org.jetbrains.kotlin.idea.quickfix.RemovePsiElementSimpleFix$RemoveVariableFactory$doCreateQuickFix$removePropertyFix$1
// IGNORE_K2
// Task for K2: KTIJ-29591