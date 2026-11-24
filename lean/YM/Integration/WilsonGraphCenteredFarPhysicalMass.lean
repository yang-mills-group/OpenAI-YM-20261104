import YM.Integration.WilsonGraphCenteredFarWindowReadings

set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar.AppointedCenteredPhysicalMass

open Filter Real Growth Continuation
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open MS MS.Book MS.Land Scale Register O O.Enh O.Score Dframe
open YangMills YangMills.Matching YM.Answer.ContinuumLimit YM.Integration
open WilsonGraphCenteredFarReplacement (atFar)
open scoped Topology BigOperators Classical

universe u

/-- The sum of public monomial coefficients is bounded on the complete filed basis ball. -/
private theorem basisBudget {σ ι : Type*} [Fintype ι] (V : Submodule ℂ (MvPolynomial σ ℂ))
    (b : Module.Basis ι ℂ V) : ∃ C : ℝ, 0 ≤ C ∧ ∀ v : V,
      (∑ m ∈ v.val.support, ‖MvPolynomial.coeff m v.val‖) ≤ C * ‖b.equivFun v‖ := by
  classical
  let support := Finset.univ.biUnion fun i : ι => (b i).val.support
  let bill (m : σ →₀ ℕ) := ∑ i, ‖MvPolynomial.coeff m (b i).val‖
  have expand (v : V) : v.val = ∑ i, b.repr v i • (b i).val := by
    calc v.val = V.subtype (∑ i, b.repr v i • b i) := congrArg V.subtype (b.sum_repr v).symm
         _ = _ := by rw [map_sum]; simp
  have included (v : V) : v.val.support ⊆ support := by
    intro m hm
    by_contra missing
    have zero (i : ι) : MvPolynomial.coeff m (b i).val = 0 :=
      MvPolynomial.notMem_support_iff.mp fun present =>
        missing (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,present⟩)
    apply (MvPolynomial.mem_support_iff.mp hm)
    rw [expand v,MvPolynomial.coeff_sum]
    exact Finset.sum_eq_zero fun i _ => by simp [MvPolynomial.coeff_smul,zero i]
  have billNonnegative (m : σ →₀ ℕ) : 0 ≤ bill m := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨∑ m ∈ support, bill m, Finset.sum_nonneg fun m _ => billNonnegative m,?_⟩
  intro v
  have perMonomial (m : σ →₀ ℕ) : ‖MvPolynomial.coeff m v.val‖ ≤ bill m * ‖b.equivFun v‖ := by
    rw [expand v,MvPolynomial.coeff_sum]
    calc _ ≤ ∑ i, ‖MvPolynomial.coeff m (b.repr v i • (b i).val)‖ := norm_sum_le _ _
         _ ≤ ∑ i, ‖MvPolynomial.coeff m (b i).val‖ * ‖b.equivFun v‖ := by
           apply Finset.sum_le_sum
           intro i _
           rw [MvPolynomial.coeff_smul,smul_eq_mul,norm_mul,mul_comm]
           exact mul_le_mul_of_nonneg_left (norm_le_pi_norm (b.equivFun v) i) (norm_nonneg _)
         _ = _ := (Finset.sum_mul ..).symm
  calc _ ≤ ∑ m ∈ support, ‖MvPolynomial.coeff m v.val‖ :=
          Finset.sum_le_sum_of_subset_of_nonneg (included v) (fun _ _ _ => norm_nonneg _)
       _ ≤ ∑ m ∈ support, bill m * ‖b.equivFun v‖ :=
          Finset.sum_le_sum fun m _ => perMonomial m
       _ = _ := (Finset.sum_mul ..).symm

theorem onChart (g : GaugeGroup) (h : ℕ) : ∃ E : ℝ, 0 ≤ E ∧ ∀ a : Sec g.core h,
    sectorMass (B := _root_.IssuedMaxwell.Reports.B g) a ≤ E * ‖chair g.core h a‖ :=
  basisBudget _ (MS.Theater.Daylight (Press.portDeck g.core) h)

variable (g : GaugeGroup) (hg : g.IsSimple) (periods : ℕ → ℕ) (strict : StrictMono periods)

/-- The same finite basis bill prices the transferred and unchanged far input on the
original full distance window, before either input is supplied. -/
theorem onWindow (h : ℕ) {C B : ℝ} (hC : 0 < C) (hB : 0 < B) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ s ≥ 0, exp s ≤ C * (gYM g.core r)^(-B) →
      ∀ a : Sec g.core h,
        sectorMass (B := _root_.IssuedMaxwell.Reports.B g)
          (atFar.{u} g hg periods strict h r (r * exp s) a) ≤ E * (2 * ‖chair g.core h a‖) ∧
        sectorMass (B := _root_.IssuedMaxwell.Reports.B g) a ≤ E * ‖chair g.core h a‖ := by
  obtain ⟨E,hE,paid⟩ := onChart g h
  have caps := ((AppointedPhysicalWindowAndPhase.earned.{u} g hg periods strict).main 0 h hC hB).2
  refine ⟨E,hE,?_⟩
  filter_upwards [caps] with r hr
  intro s hs admitted a
  let L := AppointedCenteredReverse.transfer.{u} g hg periods strict h r (r * exp s)
  have back : ‖chairs g.core h L‖ ≤ 2 := by
    change ‖chairs g.core h (AppointedCenteredReverse.transfer.{u} g hg periods strict h r (r * exp s))‖ ≤ 2
    rw [← (AppointedCenteredWindow.fields.{u} g hg periods strict h r s).2]
    exact (hr s hs admitted).2
  have coords : ‖chair g.core h (L a)‖ ≤ 2 * ‖chair g.core h a‖ := by
    rw [← Growth.appointed]
    exact ((chairs g.core h L).le_opNorm _).trans (mul_le_mul_of_nonneg_right back (norm_nonneg _))
  exact ⟨(paid (L a)).trans (mul_le_mul_of_nonneg_left coords hE),paid a⟩

end YM.FVA2.GradedFar.AppointedCenteredPhysicalMass
