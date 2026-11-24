import YM.Integration.WilsonOriginalProjectedCurvatureSalary
import YM.Integration.ActualOriginalQLayout

/-! The compensation degree and the elected positive finite salary are attached
to the real source enumeration. An unpaid entry has zero registered test. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalProjectedCurvatureBudget
open Function Finset Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open Comparison.Density.RenderM MergeProof.Accent FVA1
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open WilsonOriginalProjectedCurvatureRoster WilsonOriginalProjectedCurvatureSalary
open scoped Classical BigOperators

variable {G : Gauge} {R : Run G} {B : MS.Local.Physical.Deck G}
  {p L n : ℕ} {hn : n ≤ L} {V : Type} [DecidableEq V] [Fintype V]
  (Q : MS.Land.Prescription B) (D : ActualRunQlocalNativeTuple.Datum R p L n hn V)
  (u : V → MS.Rake.Label B) (μ : ℝ) (orders : V → ℕ) (N : ℕ) (s : Row (R:=R) u) (σ : ℝ)

def grade := ActualRunKernelPackets.tokenRank R (degree u) s -
  ActualRunKernelPackets.fieldRank R (degree u) s

omit [DecidableEq V] [Fintype V] in
theorem phase : (grade u s : ℤ) - (ActualRunKernelPackets.tokenRank R (degree u) s : ℤ) =
    -(ActualRunKernelPackets.fieldRank R (degree u) s : ℤ) := by
  have := ActualRunKernelPackets.term_grade R (degree u) s
  unfold grade
  omega

private theorem atRank {X : Type} {k : ℕ} (e : Fin k ≃ X) (f : X → ℕ) (x : X) :
    f x ≤ Finset.univ.sup (fun j => f (e j)) := by
  simpa only [Equiv.apply_symm_apply] using
    (Finset.le_sup (f:=fun j => f (e j)) (Finset.mem_univ (e.symm x)))

omit [DecidableEq V] in
theorem limit : ActualRunKernelPackets.tokenRank R (degree u) s ≤
    ActualOriginalQLayout.rankCap R u := by
  unfold ActualOriginalQLayout.rankCap
  exact atRank _ _ s

omit [DecidableEq V] [Fintype V] in
theorem substantial (h : 0 < wallet Q D u μ orders N s σ) : 0 < (placed u s).budget σ := by
  suffices hz : (placed u s).magnitude ≠ 0 by
    exact mul_pos (lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => abs_nonneg _) (Ne.symm hz))
      (Real.exp_pos _)
  intro hzero
  have ht := (charges u s).2.symm.trans hzero
  have hm : (ActualOriginalQPackets.token Q D u μ orders N s).coin = 0 := by
    change ActualOriginalQCharges.tensorMass u s * _ = 0
    rw [ht, zero_mul]
  simp only [wallet,hm,zero_mul,lt_self_iff_false] at h

omit [DecidableEq V] [Fintype V] in
theorem unfunded (h : wallet Q D u μ orders N s σ ≤ 0)
    (x : tastes D) (U : Config G (R.family.side L p)) :
    (ActualOriginalQPackets.token Q D u μ orders N s).read
      (testInclusion (ActualRunQlocalNativeTuple.orbit D) x) U = 0 := by
  by_cases hb : 0 < (placed u s).budget σ
  · rw [← work Q D u μ orders N s σ x U hb]
    have hv := norm_le_zero_iff.mp (le_trans (bound Q D u μ orders N s σ x) h)
    rw [hv, mul_zero]
  · have hz := (not_lt.mp hb).antisymm (amount _ _)
    have hm := (mul_eq_zero.mp hz).resolve_right (Real.exp_ne_zero _)
    have hc (k) : (placed u s).coeff k = 0 := by
      apply abs_eq_zero.mp
      apply le_antisymm _ (abs_nonneg _)
      rw [← hm]
      exact Finset.single_le_sum (fun j _ => abs_nonneg ((placed u s).coeff j)) (Finset.mem_univ k)
    rw [actual Q D u μ orders s N]
    simp [Atom.unmasked,Atom.poly,hc]

theorem commissioned (hL : L ≤ N) (w : V → ℝ) :
    Poly.toll w ((Stock.census V).fire s.1.1) *
      ‖(Pert.Asymptotics.regulatorRun R.family N p L : ℂ) ^
        ((grade u s : ℤ) - (ActualRunKernelPackets.tokenRank R (degree u) s : ℤ))‖ *
      wallet Q D u μ orders N s σ =
    ‖fee Q u μ orders s.1‖ * ActualOriginalQCharges.rowPrice D u w σ s := by
  rw [phase]
  have hf : (ActualOriginalQPackets.token Q D u μ orders N s).fall = ActualOriginalQCharges.rowFall u s := rfl
  simpa only [wallet, hf, mul_assoc] using ActualOriginalQCharges.token_charge D u Q μ orders N hL w σ s

end YM.Integration.WilsonOriginalProjectedCurvatureBudget
