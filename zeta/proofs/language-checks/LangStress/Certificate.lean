import LangStress.CertData
/-!
# Certificate

Every theorem below is checked when this file is built. `tally f = (n, d)` says: the embedded result file `f` holds `n` programs,
and on exactly `d` of them the answer the runtime gave differs from the Lean reference semantics.
`before` = the runtimes as they stood before the fixes of 2026-11-22; `after` = the fixed runtimes.
-/
namespace LangStress.Cert

theorem warrant_before_A_tally : tally warrant_before_A = (2000, 495) := by native_decide
theorem warrant_after_A_tally : tally warrant_after_A = (2000, 0) := by native_decide
theorem caselog_before_A_tally : tally caselog_before_A = (2000, 494) := by native_decide
theorem caselog_after_A_tally : tally caselog_after_A = (2000, 0) := by native_decide
theorem spectra_before_A_tally : tally spectra_before_A = (2000, 580) := by native_decide
theorem spectra_after_A_tally : tally spectra_after_A = (2000, 0) := by native_decide
theorem concord_after_A_tally : tally concord_after_A = (2000, 0) := by native_decide
theorem warrant_before_B_tally : tally warrant_before_B = (10000, 2338) := by native_decide
theorem warrant_after_B_tally : tally warrant_after_B = (10000, 0) := by native_decide
theorem caselog_before_B_tally : tally caselog_before_B = (10000, 2366) := by native_decide
theorem caselog_after_B_tally : tally caselog_after_B = (10000, 0) := by native_decide
theorem spectra_before_B_tally : tally spectra_before_B = (10000, 2809) := by native_decide
theorem spectra_after_B_tally : tally spectra_after_B = (10000, 0) := by native_decide
theorem concord_after_B_tally : tally concord_after_B = (10000, 0) := by native_decide
theorem warrant_before_C_tally : tally warrant_before_C = (10000, 2291) := by native_decide
theorem warrant_after_C_tally : tally warrant_after_C = (10000, 0) := by native_decide
theorem caselog_before_C_tally : tally caselog_before_C = (10000, 2371) := by native_decide
theorem caselog_after_C_tally : tally caselog_after_C = (10000, 0) := by native_decide
theorem spectra_before_C_tally : tally spectra_before_C = (10000, 2800) := by native_decide
theorem spectra_after_C_tally : tally spectra_after_C = (10000, 0) := by native_decide
theorem concord_after_C_tally : tally concord_after_C = (10000, 0) := by native_decide
theorem warrant_after_D_tally : tally warrant_after_D = (10000, 0) := by native_decide
theorem caselog_after_D_tally : tally caselog_after_D = (10000, 0) := by native_decide
theorem spectra_after_D_tally : tally spectra_after_D = (10000, 0) := by native_decide
theorem concord_after_D_tally : tally concord_after_D = (10000, 0) := by native_decide
/-- 200 answers that originally agreed, each corrupted in one place: every one is rejected -/
theorem negative_controls_all_rejected : tally negative_controls = (200, 200) := by native_decide

end LangStress.Cert

open LangStress
#print axioms Cert.warrant_before_A_tally
#print axioms Cert.warrant_after_A_tally
#print axioms Cert.caselog_before_A_tally
#print axioms Cert.caselog_after_A_tally
#print axioms Cert.spectra_before_A_tally
#print axioms Cert.spectra_after_A_tally
#print axioms Cert.concord_after_A_tally
#print axioms Cert.warrant_before_B_tally
#print axioms Cert.warrant_after_B_tally
#print axioms Cert.caselog_before_B_tally
#print axioms Cert.caselog_after_B_tally
#print axioms Cert.spectra_before_B_tally
#print axioms Cert.spectra_after_B_tally
#print axioms Cert.concord_after_B_tally
#print axioms Cert.warrant_before_C_tally
#print axioms Cert.warrant_after_C_tally
#print axioms Cert.caselog_before_C_tally
#print axioms Cert.caselog_after_C_tally
#print axioms Cert.spectra_before_C_tally
#print axioms Cert.spectra_after_C_tally
#print axioms Cert.concord_after_C_tally
#print axioms Cert.warrant_after_D_tally
#print axioms Cert.caselog_after_D_tally
#print axioms Cert.spectra_after_D_tally
#print axioms Cert.concord_after_D_tally
#print axioms Cert.negative_controls_all_rejected
#print axioms Concord.allOf_comm
#print axioms Concord.anyOf_comm
#print axioms Concord.allOf_assoc
#print axioms Concord.anyOf_assoc
#print axioms Concord.allOf_idem
#print axioms Concord.anyOf_idem
#print axioms Concord.conflict_poisons_all
#print axioms Concord.conflict_poisons_any
#print axioms Concord.all_le_any
#print axioms Concord.allOf_mono
#print axioms Concord.anyOf_mono
#print axioms Concord.allOf_stands
#print axioms CaseLog.truth_knowledge_mono
#print axioms CaseLog.truth_both_iff
#print axioms CaseLog.truth_neither_iff
