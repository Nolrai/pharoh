import Lake
open System Lake DSL

package Pharoh {
dependencies := #[
    { name := `mathlib, src := Source.path (FilePath.mk "/home" / "nolrai" / "Lean4" / "mathlib4") }
   ]
}
