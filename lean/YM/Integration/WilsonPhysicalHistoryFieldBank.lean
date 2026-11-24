import YM.Integration.WilsonPhysicalHistoryFieldVault
import YM.Integration.WilsonPhysicalHistoryFieldWidth

/-! The independent torus bank retains the fixed perturbative degree and
is paid in the actual original history's prescribed temperature. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonPhysicalHistoryFieldBank
open Function Filter Finset Lattice Laurent RG Precision Wilson FormalBulk08
open Next.Free Reef Flat Exterior Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp
open Pose Glide Bank Dawn Wine Rial Roof Dove Series Trellis Aster Borough Elm Dove.Lab
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels PowerSeries
open PhysicalNext.Repeat.Legato WilsonRunFormalMarkedStep RG16 RG16.Literal RG16.Guarding
open Pert.Asymptotics Trace.Physical Next.Foundations
open MSbar MSbar.Whisk Push.Uniform WilsonPhysicalHistoryFieldDerivatives
open WilsonPhysicalHistoryAperture
open scoped Classical Topology BigOperators
variable {G : Gauge} {d D : ℕ}

def primary (n : Side) (Y : PowerSeries (MvPolynomial (wire G n) ℝ)) :
    PowerSeries (MvPolynomial (Primary n G) ℝ) :=
  PowerSeries.map (MvPolynomial.rename (R:=ℝ) (coordinates G n).symm).toRingHom Y

/-- The independently filed torus coefficient has degree at most the field
degree plus its coupling grade, independently of the number of stages. -/
theorem degree (n : Side) (Q : Mesa.Pot G) (d e : ℕ) :
    (PowerSeries.coeff e (primary n (Kemp.banner d Q n))).totalDegree ≤ d+e := by
  rw [primary,PowerSeries.coeff_map]
  apply (MvPolynomial.totalDegree_rename_le (coordinates G n).symm _).trans
  rw [Kemp.banner,PowerSeries.coeff_mk]
  apply (MvPolynomial.totalDegree_finsetSum _ _).trans
  exact Finset.sup_le fun j hj=> (Lava.facade_grade j _).totalDegree_le.trans
    (Nat.le_of_lt_succ (Finset.mem_range.mp hj))

variable (R : Run G) (L : ∀ i, Lodge ((R.family.path.levels.clock.op i 0).patch))
variable (a : hue G) (depth : d<D)

private theorem high (simple : G.Simple) {δ : ℝ} (δ0 : 0<δ) :
    ∀ᶠ i : ℕ in atTop, ∀ N per : ℕ, i≤N →
      (regulatorRun R.family N per i)^(-δ) ≤ (R.family.path.levels.clock.hatBeta i)^δ := by
  filter_upwards [(lambda_leads R.family simple).eventually_ge_atTop 4] with i hT
  intro N per room
  let β := R.family.path.levels.clock.hatBeta i
  let T := Real.log β
  have β0 : 0<β := zero_lt_one.trans (R.family.path.levels.fits.delayed i)
  have big : 2≤T := by
    change 4≤2+Real.log (R.family.path.levels.clock.hatBeta i) at hT
    dsimp [T,β];linarith only [hT]
  have two : 2≤Real.exp 1 := by linarith only [Real.add_one_le_exp (1:ℝ)]
  have cp : 2*Real.exp (-T) ≤ Real.exp (1+(-1/2)*(2+T)) := by
    calc
      _ ≤ Real.exp 1*Real.exp (-T) := mul_le_mul_of_nonneg_right two (Real.exp_pos _).le
      _ = Real.exp (1+(-T)) := (Real.exp_add ..).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [big])
  have temp : β⁻¹ ≤ regulatorRun R.family N per i := by
    apply le_trans _ (g_band R.family R.makes (p:=per) room).1
    change β⁻¹ ≤ (Real.exp 1 * Real.exp ((-1/2)*(2+T)))/2
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    rw [mul_comm _ 2,← Real.exp_add, ← Real.exp_log β0,← Real.exp_neg]
    exact cp
  calc
    _ ≤ (β⁻¹)^(-δ) := Real.rpow_le_rpow_of_nonpos (inv_pos.mpr β0) temp (neg_nonpos.mpr δ0.le)
    _ = β^δ := by rw [Real.inv_rpow β0.le,Real.rpow_neg β0.le,inv_inv]

private theorem one (simple : G.Simple) {u : ℕ→ℕ} (grant : WilsonWindowFormalPurchase.Canonical u R.kit)
    (o : Loc G 1) (s p r : ℕ) (w : Letter (R.family.labels.level d)) {δ : ℝ} (δ0 : 0<δ) :
    ∀ᶠ i : ℕ in atTop, ∀ (N _per : ℕ), i≤N → ∀ (f : Studio D) (e : ℕ), e≤p → ∀ n : Side,
      let β := R.family.path.levels.clock.hatBeta i
      let P := PowerSeries.coeff e (primary n (Kemp.banner d (graph R L a depth N i w f) n))
      Whisk.lump (Measuring.chart n G) {(Lotus.drip n (0,o)).1} (Mosaic.αm β) s r 0 P ≤
        β^δ * ‖Annex.compress D f‖ := by
  obtain ⟨B,m,B0,archive⟩ := WilsonPhysicalHistoryFieldVault.all_fields R L a depth simple grant o p w r
  filter_upwards [archive, WilsonPhysicalHistoryFieldWidth.physical R simple grant,
    WilsonPhysicalHistoryFieldWidth.bought R simple grant r s m B0 δ0,high R simple δ0] with i field radi paid temp
  intro N per room f e he n
  dsimp only
  rw [primary,PowerSeries.coeff_map]
  have capital := WilsonPhysicalHistoryFieldVault.order (Lotus.drip n (0,o)) (width_pos R.family i)
    radi s (PowerSeries.coeff e (Kemp.banner d (graph R L a depth N i w f) n)) (field N room f e he n)
  apply capital.trans
  rw [←mul_assoc]
  exact mul_le_mul_of_nonneg_right ((paid N per room).trans (temp N per room)) (norm_nonneg _)

/-- The genuine paid bank on the original run. The common scale is chosen
before all letters, ranks, coefficients, periods and later cutoffs. -/
theorem same_run (simple : G.Simple) {u : ℕ→ℕ} (grant : WilsonWindowFormalPurchase.Canonical u R.kit)
    (o : Loc G 1) (s p : ℕ) {δ : ℝ} (δ0 : 0<δ) :
    ∀ᶠ i : ℕ in atTop, ∀ (w : Letter (R.family.labels.level d)) (N : ℕ), i≤N →
      ∀ (f : Studio D), ‖Annex.compress D f‖≤1 → ∀ n : Side,
      let β := R.family.path.levels.clock.hatBeta i
      let Q := primary n (Kemp.banner d (graph R L a depth N i w f) n)
      ∀ e ≤ p, (PowerSeries.coeff e Q).totalDegree ≤ d+p ∧
        Whisk.Vault (Measuring.chart n G) {(Lotus.drip n (0,o)).1} (Mosaic.αm β)
          s (d+p) 0 (PowerSeries.coeff e Q) (β^δ) := by
  have each (w : Letter (R.family.labels.level d)) (r : Fin (d+p+1)) :=
    one R L a depth simple grant o s p r.val w δ0
  filter_upwards [eventually_all.mpr (fun w=> eventually_all.mpr (each w))] with i all
  intro w N room f hunit n
  dsimp only
  intro e he
  have β0 : 0≤R.family.path.levels.clock.hatBeta i :=
    zero_le_one.trans (R.family.path.levels.fits.delayed i).le
  have cash := Real.rpow_nonneg β0 δ
  refine ⟨(degree n _ d e).trans (Nat.add_le_add_left he d),cash,?_⟩
  intro r hr
  have field := all w (⟨r,Nat.lt_succ_of_le hr⟩ : Fin (d+p+1)) N 0 room f e he n
  exact field.trans ((mul_le_mul_of_nonneg_left hunit cash).trans_eq (mul_one _))

end YM.Integration.WilsonPhysicalHistoryFieldBank

