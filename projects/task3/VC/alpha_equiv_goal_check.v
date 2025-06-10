Require Import alpha_equiv_goal alpha_equiv_proof_auto alpha_equiv_proof_manual.

Module VC_Correctness : VC_Correct.
  Include alpha_equiv_proof_auto.
  Include alpha_equiv_proof_manual.
End VC_Correctness.
