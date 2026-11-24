import YM.Integration.QLocalPhysicalBirthWeights

/-! Price of the genuine physical section at arbitrary original coordinates. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.WilsonOriginalCoordinateExposure
open Finset Filter Lattice Wilson RG Extra.Multi FVA1 PhysicalNext.Repeat.Legato
open scoped BigOperators Classical

variable {G : Gauge} (R : Run G) {V : Type} [Fintype V] (d : V → ℕ)

def pole := 1 + ∑ i, BasisCost.slots (R.family.labels.level (d i))

def stencil (C : ℝ) := ∑ i, (BasisCost.price (R.family.localSection (d i)) + 1) * Real.exp (100*C)

theorem threshold (L : ℕ) :
    (min (R.family.path.levels.budget L).threshold 1)⁻¹ ≤
      R.family.path.levels.clock.hatBeta L := by
  let b := R.family.path.levels.clock.hatBeta L
  have hb : 1 ≤ b := (R.family.path.levels.fits.delayed L).le
  have h0 : 0 < b := zero_lt_one.trans_le hb
  have hs : Real.sqrt b ≤ b := by
    nlinarith [Real.sq_sqrt h0.le, Real.one_le_sqrt.mpr hb]
  have ht : b⁻¹ ≤ (R.family.path.levels.budget L).threshold := by
    calc b⁻¹ ≤ (Real.sqrt b)⁻¹ := inv_anti₀ (Real.sqrt_pos.mpr h0) hs
         _ ≤ (Real.sqrt b)⁻¹ * Real.exp ((Real.log (Real.log b))^2) :=
           le_mul_of_one_le_right (inv_nonneg.mpr (Real.sqrt_nonneg _))
             (Real.one_le_exp (sq_nonneg _))
         _ = _ := rfl
  have hm : b⁻¹ ≤ min (R.family.path.levels.budget L).threshold 1 :=
    le_min ht (inv_le_one_of_one_le₀ hb)
  exact (inv_anti₀ (inv_pos.mpr h0) hm).trans_eq (inv_inv b)

omit [Fintype V] in
private theorem positive_size (i : V) (v : R.family.label (d i)) :
    0 ≤ (R.family.labels.level (d i)).coeffSize v := Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem cost [DecidableEq V] (L : ℕ) (C M : ℝ) (v : ∀ i, R.family.label (d i))
    (fixed : (R.family.path.levels.budget L).supportExponent = 100)
    (column : (R.family.path.levels.params L).columns ≤ R.family.path.levels.clock.hatBeta L)
    (size : ∀ i, (R.family.labels.level (d i)).coeffSize (v i) ≤ M) :
    ∑ i, QLocalPhysicalBirthWeights.exposure R L d v C i ≤
      stencil R d C * (R.family.path.levels.clock.hatBeta L)^(pole R d) * M := by
  let b := R.family.path.levels.clock.hatBeta L
  have hb : 1 ≤ b := (R.family.path.levels.fits.delayed L).le
  have hp : (R.family.path.rep L 0 L).p = (R.family.path.levels.budget L) := (R.makes.wilson.represents L 0 L le_rfl).vac
  rw [stencil, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  let n := BasisCost.slots (R.family.labels.level (d i))
  let q := BasisCost.price (R.family.localSection (d i))
  let s := (R.family.labels.level (d i)).coeffSize (v i)
  let g := (min (R.family.path.levels.budget L).threshold 1)⁻¹
  have hq : 0 ≤ q := zero_le_one.trans (BasisCost.price_pos _)
  have hs : 0 ≤ s := positive_size R d i (v i)
  have hn : n ≤ pole R d := by
    have h := Finset.single_le_sum (f := fun j => BasisCost.slots (R.family.labels.level (d j)))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    change n ≤ 1 + ∑ j, BasisCost.slots (R.family.labels.level (d j))
    exact h.trans (Nat.le_add_left _ _)
  have hg : 0 ≤ g := inv_nonneg.mpr (le_min (R.family.path.levels.budget L).threshold_pos.le zero_le_one)
  have power : g^n ≤ b^(pole R d) :=
    (pow_le_pow_left₀ hg (threshold R L) n).trans (pow_le_pow_right₀ hb hn)
  have paid : (R.family.path.levels.params L).columns ≤ b^(pole R d) := by
    apply column.trans
    simpa only [pow_one] using pow_le_pow_right₀ (a := b) hb (show 1 ≤ pole R d by unfold pole; omega)
  have amount : q*g^n + (R.family.path.levels.params L).columns ≤ (q+1)*b^(pole R d) := by
    rw [add_mul,one_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left power hq) paid
  have cost₀ := mul_le_mul amount (size i) hs (mul_nonneg (by linarith : 0 ≤ q+1) (pow_nonneg (zero_le_one.trans hb) _))
  unfold QLocalPhysicalBirthWeights.exposure ActualRunUnmaskedPartners.globalPrice ActualRunPhysicalPages.price
  rw [hp,fixed]
  change (q*g^n*s+(R.family.path.levels.params L).columns*s)*Real.exp (100*C) ≤
    ((q+1)*Real.exp (100*C))*b^(pole R d)*M
  calc _ = ((q*g^n+(R.family.path.levels.params L).columns)*s)*Real.exp (100*C) := by ring
       _ ≤ (((q+1)*b^(pole R d))*M)*Real.exp (100*C) :=
         mul_le_mul_of_nonneg_right cost₀ (Real.exp_nonneg _)
       _ = _ := by ring

end YM.Integration.WilsonOriginalCoordinateExposure
