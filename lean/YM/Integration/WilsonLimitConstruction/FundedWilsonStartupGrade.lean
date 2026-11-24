import YM.Integration.WilsonLimitConstruction.FundedWilsonStartupJets
import YM.Integration.ActualGradedVacuum
import YM.Integration.ActualStartupInvoice
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Pane.Null

/-! The joint coupling and field germ of the original paid ultraviolet album
uses its actual powers, ranks and rooted Wilson remainders. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedWilsonStartupGrade

open Function Filter Finset Lattice Wilson RG Work Exterior Precision
open PhysicalNext.Repeat.Legato WilsonStartup WilsonStartup.Start WilsonStartup.IterationFour
open YM.IterationFour YM.IterationFour.Vacuum Progress.DirectedRecipe
open Comparison.RG02 Comparison.RG02.Assembly LocalComparison.Global
open scoped Classical Topology BigOperators ContDiff
variable {G : Gauge} {n : Side}

theorem restored (P : BudgetPoint) (S : Stage) (r : ℕ) (width g : ℝ) (U : Config G n) :
    ActualGradedVacuum.restored (ActualStartupInvoice.paidAlbum G n P S r width) g U =
      unmaskedLayers (album G n P S r) 1 U := by
  have h (i : ℕ) : 3+i+2-(5+i) = 0 := by omega
  simp [ActualGradedVacuum.restored,ActualStartupInvoice.paidAlbum,ActualStartupInvoice.repriceLayers,
    ActualStartupInvoice.reprice,album,unmaskedLayers,Function.comp_def,top_terms,Render.prefactor,h]

theorem healthy (P : BudgetPoint) (S : Stage) (hc : S.clip.direct ≤ 1) (r : ℕ) (hr : 2 ≤ r)
    (width g : ℝ) (U : Config G n) (hz : flags P.threshold U = ∅) :
    Wilson.energy U - mainTerm S.clip (Design.top G S.clip) U -
      ActualGradedVacuum.restored (ActualStartupInvoice.paidAlbum G n P S r width) g U =
      FundedWilsonStartup.residual S r U := by
  have h := FundedWilsonStartup.stored P S hc r hr 1 zero_lt_one U hz
  have hkin := PhysicalNext.Repeat.Pane.crystalline (Design.top G S.clip) S.clip P 1 U hz
  have hloop : Precision.loop (Design.top G S.clip) U = 0 := by
    have he (V : Config G n) : uncut (Design.top G S.clip).loop V = 0 := by
      simp only [uncut,Design.top,Design.extract_unmasked,Tensor.diagonal,
        zero_apply,tsum_zero,Finset.sum_const_zero]
    simp only [Precision.loop,he,Patch.average,Finset.sum_const_zero,mul_zero]
  rw [hkin,hloop] at h
  rw [restored]
  have hg : Currency.gain (1:ℝ) = 1 := by simp [Currency.gain]
  rw [hg] at h
  linarith only [h]

theorem clear (P : BudgetPoint) : ∀ᶠ z : ℝ × fieldDir G n 1 in 𝓝 0,
    flags P.threshold (represent z.2) = ∅ := by
  have h₀ : represent (0 : fieldDir G n 1) = (1 : Config G n) := by
    funext e
    simp [represent,increment,collect]
  have h (j : Cell n) : ∀ᶠ z : ℝ × fieldDir G n 1 in 𝓝 0,
      G.chord (faceValue (represent z.2) j) < P.threshold := by
    have hc : Continuous (fun z : ℝ × fieldDir G n 1 => G.chord (faceValue (represent z.2) j)) := by
      unfold represent collect faceValue increment
      fun_prop
    have hz : G.chord (faceValue (represent (0 : fieldDir G n 1)) j) = 0 := by
      rw [h₀]
      unfold faceValue
      change G.chord (travel _ _ [_,_,_,_]) = _
      simp [travel,Step.read,G.chord_one]
    have ht : Tendsto (fun z : ℝ × fieldDir G n 1 => G.chord (faceValue (represent z.2) j))
        (𝓝 (0,(0 : fieldDir G n 1))) (𝓝 0) := by
      simpa only [hz] using hc.tendsto (0,(0 : fieldDir G n 1))
    exact ht (Iio_mem_nhds P.threshold_pos)
  filter_upwards [eventually_all.mpr h] with z hz
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨j,_,hj⟩ := (flags_spec ..).mp hx
  exact (hz j).not_ge hj.le

theorem unspent (S : Stage) (r : ℕ) :
    GradeAt (r+3) (Bulk.projected (fun (_ : ℝ) (U : Config G n) => FundedWilsonStartup.residual S r U)) := by
  let f := fun z : ℝ × fieldDir G n 1 => collect G z.2
  have hf : ContDiffAt ℝ ω f 0 := by
    apply ContDiff.contDiffAt
    apply contDiff_pi.mpr
    intro e
    change ContDiff ℝ ω (fun z : ℝ × fieldDir G n 1 => z.2 (e.1,coord e.2))
    fun_prop
  have hzero : f 0 = 0 := rfl
  have hrow (p : Cell n) : GradeAt (r+3) (fun z : ℝ × fieldDir G n 1 =>
      leftOver (r+2) p (represent z.2)) := by
    have hg : GradeAt (r+3) (leftOver (G:=G) (r+2) p ∘ increment 1) :=
      ⟨(leftOver_smooth (r+2) p 1).contDiffAt,leftOver_flat (r+2) p⟩
    exact hg.coarse hf hzero
  have hsum (s : Finset (Key n)) : GradeAt (r+3) (fun z : ℝ × fieldDir G n 1 =>
      ∑ i ∈ s, leftOver (r+2) i.positive (represent z.2)) := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using (GradeAt.grade_zero (X:=ℝ × fieldDir G n 1) (Y:=ℝ) (r+3))
    | insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (hrow i.positive).add ih
  have hc : GradeAt 0 (fun _ : ℝ × fieldDir G n 1 => WilsonStartup.share * Design.bulk S.clip) :=
    GradeAt.unchecked contDiffAt_const
  change GradeAt (r+3) (fun z : ℝ × fieldDir G n 1 => WilsonStartup.share * Design.bulk S.clip *
    ∑ i : Key n,leftOver (r+2) i.positive (represent z.2))
  simpa only [Nat.zero_add,smul_eq_mul] using hc.scale (hsum Finset.univ)

theorem purchase (R : Run G) (T : Campaign R) (N p r : ℕ) (hr : 2 ≤ r) (P : BudgetPoint) (width : ℝ) :
    let X := R.family.path.rep N p N
    let S := R.family.path.levels.params N
    GradeAt (r+3) (Bulk.projected (fun (g : ℝ) (U : Config G (R.family.side N p)) =>
      (Wilson.energy U-mainTerm X.clip X.path U)-
        ActualGradedVacuum.restored (ActualStartupInvoice.paidAlbum G _ P S r width) g U)) := by
  dsimp only
  let S := R.family.path.levels.params N
  have hp := ActualRunStartupInput.represented_path R T N p
  have hc : (R.family.path.rep N p N).clip = S.clip := (R.makes.wilson.represents N p N le_rfl).clip
  have hd := Push.PriceCompiler.Canonical.direct_le_one (R.alloy.B.support.cap N N le_rfl).metric
  apply (unspent (G:=G) (n:=R.family.side N p) S r).depends
  filter_upwards [clear (G:=G) (n:=R.family.side N p) P] with z hz
  change FundedWilsonStartup.residual S r (represent z.2) =
    (Wilson.energy (represent z.2) - mainTerm _ _ (represent z.2)) - _
  rw [hp,hc]
  exact (healthy P S hd r hr width z.1 (represent z.2) hz).symm

end YM.Integration.WilsonLimitConstruction.FundedWilsonStartupGrade
end
