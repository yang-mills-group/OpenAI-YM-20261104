import YM.Integration.WilsonOriginalNullRelocation
import YM.Integration.WilsonThermometerWeakReflectedRows
import YM.Integration.WilsonThermometerHostedLamp

/-! The two separate letters of the actual translated public report at the
common grid date. The marked barcode keeps its genuine Wilson key permutation. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixCanonicalSingleton
open Function Finset Set MeasureTheory Lattice Wilson RG Marker Source Labels
open Extra.Histories Motion MergeProof MergeProof.Accent RG05Readout RG05Readout.Address
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{d:ℕ}{F:Frame G d} (S:SectionData F) {P:Rep G n}
    (t:Site n) (move:P.activities.Moves 1 t) (q:Coefficient F n)

theorem regular (U:Config G n) :
    (Drift.stamp t move q).exponentialEntry t S P U = q.exponentialEntry 0 S P (translate t U) := by
  let Z:=Drift.stamp t move q
  have per i : Z.maskedTerm P i U=q.maskedTerm P i (translate t U):=by
    unfold Coefficient.maskedTerm
    by_cases hu:Healthy P.p.threshold (q.support i) (translate t U) <;> simp [Z,Drift.stamp,hu,Drift.clean t P.p]
  have root: t=(0:Site n)+t:=by simp
  change Z.exponentialEntry t S P U=_
  unfold Coefficient.exponentialEntry
  rw [root]
  simp_rw [per,show Z.x=q.x from rfl, ←Drift.reloc_foot]
  by_cases hu:Healthy P.p.threshold (S.footprint 0) (translate t U) <;> simp [Drift.clean t P.p,hu]

theorem original {Z:Three G n} (book:View.Signpost P (1,false) t (invoice q 0 S P) Z)
    {A:Hol G}{κ B:ℝ}(form:q.Format 0 A P)(fee:q.remBound 0 P κ B):
    (Drift.stamp t move q).Format t A P ∧ (Drift.stamp t move q).remBound t P κ B ∧
    Z.2.1=(Drift.stamp t move q).exponentialEntry t S P ∧
    profile P.activities Z.2.2=profile P.activities (Drift.stamp t move q).forced := by
  refine ⟨by simpa only [zero_add] using Drift.stamp_format t move q form,
    by simpa only [zero_add] using Drift.stamp_rem t move q fee,?_,?_⟩
  · rw [book.gate]
    funext U
    rw [regular S t move q U]
    change Motion.scalar (1,false) (q.exponentialEntry 0 S P (pull 1 t U))=_
    rw [pull_one];rfl
  · let stage:=invoice q 0 S P
    have right:View.Signpost P (1,false) t stage (View.spin (1,false) move stage):=View.spin_at ..
    rw [book.lens,←right.lens]
    congr 1

end YM.Integration.WilsonSeparatedPrefixCanonicalSingleton
end
