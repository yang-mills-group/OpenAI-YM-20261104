import YM.Integration.WilsonRootedGermFlagMass

/-! The intensive rough sector of the once-divided original packet on any finite period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedGermDenseIncome
open Function Finset Filter MeasureTheory Lattice Wilson RG PhysicalNext.Repeat.Legato
open OPE.Therm Trace.Terrace IterationFour
open WilsonMatrixOriginalGermOccupancy WilsonRootedGermFlagTariff WilsonRootedGermFlagMass
open scoped BigOperators Classical Topology
variable {G : Gauge} (R : Run G)

def load (e i p : ℕ) : ℕ := Nat.ceil ((Fintype.card (Site (R.family.side i p)):ℝ)/(Lyra R.family.path.levels i)^e)

/-- A single clock is used before the cutoff, the period, the old root and the submitted covariate. -/
theorem purchased (hG : G.Simple) (theta : Poetry R.family.path.levels) (e target : ℕ) :
    ∀ᶠ i : ℕ in atTop, ∀ N p, i≤N → ∀ o : Site (R.family.side i p),
      ∀ D : Config G (R.family.side i p) → ℂ, Envelope D → ∀ M : ℝ, (∀ U, ‖D U‖≤M) →
      (∫ U, rent R i N p o U * ‖slice R i p (load R e i p) D U‖ ∂scene R.family.path N p i) ≤
        M*Real.exp (-(target:ℝ)*Lyra R.family.path.levels i) := by
  let L := R.family.path.levels
  filter_upwards [WilsonRootedGermFlagTariff.purchased R hG theta e target, (lrate L hG).eventually_ge_atTop 1]
    with i booked one
  intro N p live o D hd M cap
  let b := Lyra L i
  let w := b^e
  let V := (Fintype.card (Site (R.family.side i p)):ℝ)
  let q := load R e i p
  let k := siteRate R i N p
  let h := heat R i N p
  change 1≤b at one
  have wp : 0<w := pow_pos (zero_lt_one.trans_le one) _
  have vp : 0<V := by dsimp only [V];exact_mod_cast (Fintype.card_pos : 0<Fintype.card (Site (R.family.side i p)))
  have qp : 0<q := Nat.ceil_pos.mpr (div_pos vp wp)
  have q1 : (1:ℝ)≤q := by exact_mod_cast Nat.succ_le_of_lt qp
  have contain : V≤(q:ℝ)*w := (div_le_iff₀ wp).mp (Nat.le_ceil (V/w))
  have cleared : V*k - (q:ℝ)*h ≤ (q:ℝ)*(-(target:ℝ)*b) := by
    by_cases positive : 0≤k
    · have vw := mul_le_mul_of_nonneg_right contain positive
      have cash : w*k-h ≤ -(target:ℝ)*b := booked N p live w wp.le le_rfl
      have many := mul_le_mul_of_nonneg_left cash (Nat.cast_nonneg q : (0:ℝ)≤q)
      nlinarith only [vw,many]
    · have vk := mul_nonpos_of_nonneg_of_nonpos vp.le (le_of_not_ge positive)
      have cash : 0*k-h ≤ -(target:ℝ)*b := booked N p live 0 le_rfl wp.le
      have many := mul_le_mul_of_nonneg_left cash (Nat.cast_nonneg q : (0:ℝ)≤q)
      nlinarith only [vk,many]
  have loss : -(target:ℝ)*b≤0 := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) (zero_le_one.trans one)
  have oneLoss : (q:ℝ)*(-(target:ℝ)*b) ≤ -(target:ℝ)*b := by simpa only [one_mul] using mul_le_mul_of_nonpos_right q1 loss
  exact (WilsonRootedGermFlagMass.original R live q o D hd cap).trans
    (mul_le_mul_of_nonneg_left (Real.exp_monotone (cleared.trans oneLoss)) ((norm_nonneg _).trans (cap 1)))

end YM.Integration.WilsonRootedGermDenseIncome
