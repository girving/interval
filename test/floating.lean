import Interval

open Floating

/-!
### Unit tests

For now we only test `Floating.log2`, not prove it correct.  We can add the
proofs if we start using it in trusted settings.
-/

example : log2 (ofNat (2^157) false) == 157 := by native_decide
example : log2 (ofInt (-2^157) false) == 157 := by native_decide
example : log2 (ofNat (2^157 + 1) true) == 157 := by native_decide
example : log2 (ofInt (-1 - 2^157) false) == 157 := by native_decide
example : log2 (ofNat (2^157 - 1) false) == 156 := by native_decide
example : log2 (ofInt (1 - 2^157) true) == 156 := by native_decide
example : log2 (ofRat (2^(-157 : ℤ)) false) == -157 := by native_decide
example : log2 (ofRat (-2^(-157 : ℤ)) false) == -157 := by native_decide
