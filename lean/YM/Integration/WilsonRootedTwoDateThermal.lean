import YM.Integration.WilsonRootedTwoDateProduct
import YM.Integration.WilsonPhysicalHistoryKioskHeatOrder
import YM.Integration.WilsonRootedPhysicalPointAdmission

/-! All-order price of a complete actual old–fresh OPE product on one localized
forced event. The physical positive law and its thermal selection belong to the same run. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedTwoDateProduct
open Filter Finset MeasureTheory Lattice Wilson RG Marker Precision
open PhysicalNext.Repeat.Legato LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep IterationFour IterationFour.Vacuum MergeProof
open WilsonLimitConstruction OPE.Therm RG.Shoot Push.AbsoluteSums.Animals Pert.Asymptotics
open private rent from YM.Integration.WilsonPhysicalHistoryKioskHeatOrder
open scoped Classical Topology BigOperators
universe u
variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] [Nonempty V] {B : MS.Local.Physical.Deck G}
    (R : Run G) (hG : G.Simple) {T : Campaign R} (W : Campaign.Pillars R T) {ε : ℝ}
    (paid : FundedOriginalProperties.{u} hG ε W)
local notation "g" => regulatorRun R.family
local notation "κ" => R.family.path.levels.clock.forcedAllowance

include paid in
/-- The cutoff is set before the period, the two independent normalized tests,
their forests, field directions, all remaining cutoff, and the named plaquettes.
Each exceptional configuration is charged by the probability of one union. -/
theorem hot (u v : V→MS.Rake.Label B) (d q : ℕ) {δ ρ : ℝ} (price : 0<δ) (threshold : 0<ρ) :
    ∀ᶠ m : ℕ in atTop, ∀ (N p : ℕ) (old : Seed R B V N p (m+1)) (fresh : Seed R B V N p m),
      old.labels=u → fresh.labels=v → ∀ (w : V→ℝ), (∀i,0<w i) → (∀i,w i ≤ 1) →
      ∀ F : Finset (Face (Per (R.family.side (m+1) p))), (F.card:ℝ) ≤ ((g N p (m+1))^d)⁻¹ →
       (∫ U in (House.chilly F (ρ*(R.family.path.rep N p (m+1)).p.threshold))ᶜ,
         Poly.price w (integrand old fresh hG U) ∂(scene R.family.path N p (m+1))) ≤ δ*(g N p (m+1))^q := by
  let C := MarkedPackets.uniformModelCost (ActualOriginalQLayout.rankCap R u) (Fintype.card V) 1 *
    MarkedPackets.uniformModelCost (ActualOriginalQLayout.rankCap R v) (Fintype.card V) 1
  let K := |C|+1
  have hk : 0 ≤ K := by dsimp [K]; positivity
  let D : ℝ := 625*(Fintype.card PlaqAxes:ℝ)
  have axes : 0 < Fintype.card PlaqAxes := Fintype.card_pos
  have axis1 : (1:ℝ) ≤ (Fintype.card PlaqAxes:ℝ) := by exact_mod_cast axes
  have d1 : (1:ℝ) ≤ D := by dsimp [D]; linarith
  have temperature : Poetry R.family.path.levels := paid.2.1.paid.stoves
  filter_upwards [(tendsto_add_atTop_nat 1).eventually (PhysicalWilsonHotAllowance.faces (H:=R.family.path) temperature hG
      R.makes.wilson threshold 1), (tendsto_add_atTop_nat 1).eventually (rent R hG d q hk price),
    eventually_ge_atTop (ActualOriginalQLayout.referenceLevel R u),
    eventually_ge_atTop (ActualOriginalQLayout.referenceLevel R v)] with m thermal calendar oldRef freshRef N p old fresh ho hf w hw hu F count
  have hr : old.visible := by unfold Seed.visible; rw [ho]; omega
  have hf' : fresh.visible := by unfold Seed.visible; rw [hf]; omega
  have costs : old.cost*fresh.cost=C := by unfold Seed.cost; rw [ho,hf]
  have cap := measured old fresh hG hr hf' w hw hu (House.chilly F (ρ*(R.family.path.rep N p (m+1)).p.threshold))ᶜ
  have mass := thermal N fresh.below p F
  have real0 : 0 ≤ (scene R.family.path N p (m+1)).real
      (House.chilly F (ρ*(R.family.path.rep N p (m+1)).p.threshold))ᶜ := ENNReal.toReal_nonneg
  have kpos : 0 ≤ κ (m+1) := (Real.exp_pos _).le
  have gp : 0<g N p (m+1) := Currency.g_pos R.makes _ _ _ fresh.below
  have count' : (F.card:ℝ) ≤ D*((g N p (m+1))^d)⁻¹ := count.trans <|
    le_mul_of_one_le_left (inv_nonneg.mpr (pow_nonneg gp.le _)) d1
  have charge : (scene R.family.path N p (m+1)).real
      (House.chilly F (ρ*(R.family.path.rep N p (m+1)).p.threshold))ᶜ ≤ (D*((g N p (m+1))^d)⁻¹)*κ (m+1) :=
    (by simpa only [pow_one] using mass : _ ≤ (F.card:ℝ)*κ (m+1)).trans (mul_le_mul_of_nonneg_right count' kpos)
  rw [costs] at cap
  have ck : C ≤ K := (le_abs_self C).trans (by dsimp [K]; linarith)
  exact cap.trans <| (mul_le_mul_of_nonneg_left ck real0).trans <|
    (mul_le_mul_of_nonneg_right charge hk).trans <| calc
      (D*((g N p (m+1))^d)⁻¹*κ (m+1))*K = (K/(g N p (m+1))^d)*D*κ (m+1) := by ring
      _ ≤ δ*(g N p (m+1))^q := calendar N fresh.below p

end YM.Integration.WilsonRootedTwoDateProduct
