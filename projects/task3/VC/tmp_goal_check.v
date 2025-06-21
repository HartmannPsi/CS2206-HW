Require Import tmp_goal tmp_proof_auto tmp_proof_manual.

Module VC_Correctness : VC_Correct.
  Include tmp_proof_auto.
  Include tmp_proof_manual.
End VC_Correctness.
