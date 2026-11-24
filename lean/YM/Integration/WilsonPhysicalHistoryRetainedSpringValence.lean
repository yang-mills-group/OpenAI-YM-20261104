import YM.Integration.WilsonPhysicalHistoryRetainedSpringSite
import YM.AnalyticNext.CUBIC_MATCH.Terms.Slots

/-! The angular valuation of the actual previous curvature series at a single
site, before summing its translations or taking a connected expectation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Filter Function Lattice RG Wilson Precision Tree Work.F03 Bid CubicMatch
open WilsonCoeffUV.Bank.Mosaic
open scoped Classical ContDiff BigOperators Topology
variable {G : Gauge} {n : Side} {k : ℕ}

theorem site_coefficient (A : ℕ→Atom G k) {σ C : ℝ} (pos : 0<σ)
    (paid : SumBudget (fun i=>(A i).budget σ) C) (x : Site n) (z : Dir G n) (r : ℕ) :
    CubicMatch.term r (fun t : ℝ=>sitePacket A x (represent (t • z))) =
      Patch.average (fun s : Signed=>∑' i,CubicMatch.term r (fun t : ℝ=>
        (A i).unmasked (represent (t • pulled z s)) x)) := by
  let f (s : Signed) (t : ℝ):=∑' i,(A i).unmasked (represent (t • pulled z s)) x
  have smooth (s : Signed) : ContDiffAt ℝ ω (f s) 0:=
    CubicMatch.atom_sum_smooth pos paid x (CubicMatch.test_ray (pulled z s))
  have written : (fun t : ℝ=>sitePacket A x (represent (t • z))) =
      fun t=>((Fintype.card Signed:ℝ)⁻¹) • ∑ s,f s t := by
    funext t
    simp only [sitePacket,Patch.average,f,Work.F03.represent_pulled,smul_eq_mul]
  rw [written,CubicMatch.term_scaled _ (ContDiffAt.sum fun s _ => smooth s)]
  unfold Patch.average
  rw [CubicMatch.term_sum (fun s _ => (smooth s).of_le le_top)]
  apply congrArg (((Fintype.card Signed:ℝ)⁻¹)*·)
  apply Finset.sum_congr rfl
  intro s _
  exact (CubicMatch.atom_story (j:=r) pos paid x (CubicMatch.test_ray (pulled z s))).tsum_eq.symm

theorem site_initial (A : ℕ→Atom G k) {σ C : ℝ} (pos : 0<σ)
    (paid : SumBudget (fun i=>(A i).budget σ) C) (x : Site n) (z : Dir G n) :
    CubicMatch.term k (fun t : ℝ=>sitePacket A x (represent (t • z))) =
      Patch.average (fun s : Signed=>∑' i,(A i).poly (fun h=>
        faceCurl (slotFace ((A i).leg h) x) (pulled z s))) ∧
    ∀ r<k,CubicMatch.term r (fun t : ℝ=>sitePacket A x (represent (t • z)))=0 := by
  constructor
  · rw [site_coefficient A pos paid]
    apply congrArg Patch.average
    funext s
    exact tsum_congr fun i=>(CubicMatch.slot_first (A i) x (pulled z s)).1
  · intro r hr
    rw [site_coefficient A pos paid]
    have zero (s : Signed) (i : ℕ) :=
      (CubicMatch.slot_first (A i) x (pulled z s)).2 r hr
    simp [zero,Patch.average]

end YM.Integration.OriginalMarkedRunAction
