import ThresholdLeanXmss.Statement.Theorems
import ThresholdLeanXmss.Statement.SigningBudgets

/-!
# Threshold leanXMSS security statement

This module imports every file of the statement layer. `Statement/Theorems.lean` is the entry file.
It holds the bundle of the end claims and the model. `Statement/SigningBudgets.lean` holds the forms
of the signing claim that the proofs use, and no field of the bundle is in it.
-/

set_option autoImplicit false
