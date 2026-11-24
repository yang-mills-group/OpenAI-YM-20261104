import YM.Integration.WilsonTrueProjectedLocatedFunded

/-! Combine the two true null portfolios at the reporting site separately.
Projection and density are additive inside each original inventory. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonTrueProjectedLocatedMerge
open Filter MeasureTheory Lattice RG Wilson Extra.Histories Source Labels
open Extra.Histories.Relay Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open QuadraticLocal QuadraticLocal.Advent AllOrder AllOrder.Floe AllOrder.Transit WheelP WilsonOriginalNullCorridor
open scoped Classical Topology BigOperators

open FormalBulk08 City Pose RemainderComparison ConnectedActivityE6
open WilsonTrueProjectedPointProgram WilsonTrueProjectedPointInverse
open WilsonTrueProjectedLocatedBasis WilsonTrueProjectedLocatedHistory
open WilsonPinnedWidthTransport WilsonTrueProjectedNaturalFee WilsonTrueProjectedCourse
open scoped Classical BigOperators

open WilsonTrueProjectedLocatedFunded Push.Local Extra.Histories.Relay
variable {G : Gauge} {d : ℕ} {n : Side} (F : Frame G d) (A : Hol G)

def tPrice (W : Rep G n) : ℝ :=
  (((F.extra+1 : ℕ) : ℝ)*(Germ.germ_close F A).choose)*Germ.wraps W.p n

theorem raw (W : Rep G n) (o : Site n) (q : Coefficient F n) {κ B : ℝ}
    (hf : q.Format o A W) (hr : q.remBound o W κ B)
    (dw : d≤W.p.order) (pw : d≤W.p.power) (zero : projection F A W.p.threshold o q=0) :
    F.coeffSize q.x ≤ tPrice F A W*B := by
  have h := (germ_close F A).choose_spec.2 W q hf hr dw pw
  rw [zero,zero_sub,norm_neg] at h
  exact (size_le_norm F q.x).trans ((mul_le_mul_of_nonneg_left h (by positivity)).trans_eq (by
    dsimp [tPrice];ring))

theorem collect {T : Type*} (W : Rep G n) (o : Site n) (S : SectionData F)
    {σ C Λ δ w : ℝ} (law : W.Lawful σ C Λ δ w) {κ : ℝ} (kp : 0<κ)
    (dw : d≤W.p.order) (pw : d≤W.p.power) (q : T → Coefficient F n) (b : T → ℝ)
    (s : Finset T) (fund : ∀ j∈s,(q j).Format o A W ∧ (q j).remBound o W κ (b j) ∧
      projection F A W.p.threshold o (q j)=0) :
    ∃ h : Coefficient F n, h.Format o A W ∧ h.remBound o W κ (∑j∈s,b j) ∧
      projection F A W.p.threshold o h=0 ∧ h.density o S W=∑j∈s,(q j).density o S W := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨Extra.Histories.primary o 0,primary_format 0,?_,?_,?_⟩
    · simpa only [Finset.sum_empty] using primary_rem (R:=W) (o:=o) (0 : F.Coeff) kp
    · exact WilsonOriginalNullCalibrated.raw_page F A W o 0 dw pw
    · funext U
      simp only [primary_density,map_zero,mul_zero,Finset.sum_empty,Pi.zero_apply]
  | @insert t s hs ih =>
    have ht:=fund t (Finset.mem_insert_self ..)
    obtain ⟨r,fr,br,zr,er⟩ := ih (fun j hj=>fund j (Finset.mem_insert_of_mem hj))
    refine ⟨beside (q t) r,(presentation ht.1 ht.2.1 fr br).1,?_,?_,?_⟩
    · rw [Finset.sum_insert hs]
      exact (presentation ht.1 ht.2.1 fr br).2
    · have hz := add_projection d (q t) r ht.1 fr dw pw ⟨κ,b t,ht.2.1⟩ ⟨κ,_,br⟩
      simpa only [ht.2.2,zr,add_zero] using hz
    · rw [plus law ht.2.1 br S,er,Finset.sum_insert hs]

end YM.Integration.WilsonTrueProjectedLocatedMerge
