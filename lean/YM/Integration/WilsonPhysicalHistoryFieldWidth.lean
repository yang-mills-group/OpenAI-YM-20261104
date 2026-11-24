import YM.Integration.WilsonPhysicalHistoryFieldSpread
import YM.Integration.WilsonPhysicalHistoryFormalPayoff
import YM.MSbar.Mosaic.Index

/-! The actual formal periodized field's radius and its fixed spatial word
moment are admitted by the single living temperature of the existence run. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonPhysicalHistoryFieldWidth
open Filter Finset Lattice RG Precision Wilson FormalBulk08
open Next.Free Reef Exterior Stationary Lotus Mesa Gorge City Cork Rift Lava Kemp
open Pose Glide Bank Dawn Wine Rial Roof Dove Series Trellis Aster Borough Elm
open PhysicalNext.Repeat.Legato RG16 RG16.Literal RG16.Guarding
open Pert.Asymptotics Trace.Physical Next.Foundations
open WilsonPhysicalHistoryAperture WilsonPhysicalHistoryFieldSpread
open scoped Classical Topology
variable {G : Gauge} (R : Run G)

/-- The genuine `MSbar.Mosaic.αm` evaluated at the original stage's predicted
temperature fits inside the half-width paid for the ordered physical words. -/
theorem physical (simple : G.Simple) {u : ℕ→ℕ} (grant : WilsonWindowFormalPurchase.Canonical u R.kit) :
    ∀ᶠ i : ℕ in atTop, MSbar.Mosaic.αm (R.family.path.levels.clock.hatBeta i) ≤
      width R.family i/2 := by
  filter_upwards [(lambda_leads R.family simple).eventually_ge_atTop 4] with i hp
  let b := width R.family i
  let β := R.family.path.levels.clock.hatBeta i
  let T := Real.log β
  have b0 : 0<b := width_pos R.family i
  have big : 2≤T := by
    change (4:ℝ) ≤ 2+Real.log (R.family.path.levels.clock.hatBeta i) at hp
    dsimp [T,β];linarith only [hp]
  have t0 : 0<T := by linarith only [big]
  have ageBound : Borough.ageZ β ≤ T := by
    change 1+Real.log T ≤ T
    linarith only [Real.log_le_sub_one_of_pos t0]
  have binv : b⁻¹≤T := (width_paid R grant i).trans ageBound
  have p : (2:ℝ)≤T^5 :=
    (by norm_num : (2:ℝ)≤2^5).trans (pow_le_pow_left₀ (by norm_num) big 5)
  have q : 2*b⁻¹ ≤ T^6 := by
    calc
      _ ≤ 2*T := mul_le_mul_of_nonneg_left binv (by norm_num)
      _ ≤ T^5*T := mul_le_mul_of_nonneg_right p t0.le
      _ = _ := by ring
  calc
    _ = (T^6)⁻¹ := by
      change (T^2)^(-3:ℤ)=(T^6)⁻¹
      rw [zpow_neg]
      exact congrArg (fun x : ℝ => x⁻¹) (pow_mul T 2 3).symm
    _ ≤ (2*b⁻¹)⁻¹ := inv_anti₀ (mul_pos (by norm_num) (inv_pos.mpr b0)) q
    _ = _ := by change (2*b⁻¹)⁻¹=b/2; rw [mul_inv_rev,inv_inv,div_eq_mul_inv]

/-- All rank and spatial moment constants are bought by any fixed loss in the
real regulated coupling on the original history. -/
theorem bought (simple : G.Simple) {u : ℕ→ℕ} (grant : WilsonWindowFormalPurchase.Canonical u R.kit)
    (r s m : ℕ) {B η : ℝ} (B0 : 0≤B) (η0 : 0<η) :
    ∀ᶠ i : ℕ in atTop, ∀ N n : ℕ, i≤N →
      ((r.factorial:ℝ)*fee (width R.family i) s)*
        (B*(Borough.ageZ (R.family.path.levels.clock.hatBeta i))^m) ≤
      (regulatorRun R.family N n i)^(-η) := by
  let bill := (r.factorial:ℝ) * (3:ℝ)^s * ((s.factorial:ℝ)*Real.exp 1) * B
  have bill0 : 0≤bill := by dsimp [bill];positivity
  filter_upwards [WilsonPhysicalHistoryFormalPayoff.polynomial R simple bill bill0 (s+m) η0] with i market
  intro N n hN
  let b := width R.family i
  let A := Borough.ageZ (R.family.path.levels.clock.hatBeta i)
  let T := RG16.Lambda R.family.path.levels i
  have b0 : 0<b := width_pos R.family i
  have age0 : 0≤A := zero_le_one.trans (Borough.progZ ((WilsonWindowFormalAnnouncement.on_run R grant).power.beta i))
  have AT : A≤T := age R.family i
  have T1 : 1≤T := (Borough.progZ ((WilsonWindowFormalAnnouncement.on_run R grant).power.beta i)).trans AT
  have T0 : 0≤T := zero_le_one.trans T1
  have invB : b⁻¹≤A := width_paid R grant i
  have hw : 1+(b/2)⁻¹≤3*T := by
    rw [inv_div,div_eq_mul_inv];linarith only [T1,AT,invB]
  have hpow := pow_le_pow_left₀ (by positivity : 0≤1+(b/2)⁻¹) hw s
  have hage := pow_le_pow_left₀ age0 AT m
  apply le_trans _ (market N n hN)
  change ((r.factorial:ℝ)*((1+(b/2)⁻¹)^s*((s.factorial:ℝ)*Real.exp 1)))*(B*A^m) ≤ bill*T^(s+m)
  calc
    _ ≤ ((r.factorial:ℝ)*((3*T)^s*((s.factorial:ℝ)*Real.exp 1)))*(B*T^m) := by
      gcongr
    _ = _ := by rw [mul_pow,pow_add]; unfold bill; ring
end YM.Integration.WilsonPhysicalHistoryFieldWidth

