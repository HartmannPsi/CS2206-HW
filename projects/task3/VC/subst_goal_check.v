Require Import subst_goal subst_proof_auto subst_proof_manual.

Module VC_Correctness : VC_Correct.
  Include subst_proof_auto.
  Include subst_proof_manual.
End VC_Correctness.
