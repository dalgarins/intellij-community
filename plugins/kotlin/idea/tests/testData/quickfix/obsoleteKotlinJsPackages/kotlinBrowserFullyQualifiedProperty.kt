// "Fix 'kotlin.browser' package usage" "true"
// JS_WITH_DOM_API_COMPAT
// This test broke with the Update to Kotlin 2.1.10
// We do not update these tests because they are only for K1 and for a legacy inspection
// IGNORE_K1

package test

fun use(a: Any) {}

fun usage() {
    use(kotlin.<caret>browser.localStorage.toString())
}

// FUS_QUICKFIX_NAME: org.jetbrains.kotlin.idea.inspections.migration.ObsoleteKotlinBrowserUsageFix