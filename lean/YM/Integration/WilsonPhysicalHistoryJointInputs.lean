import YM.Integration.WilsonPhysicalHistoryBlockInputs
import YM.Integration.WilsonPhysicalHistoryJointProduct
import YM.Integration.WilsonPhysicalHistoryOffsetFare

/-! The complete mixed formal input product through one authentic RG16
block, simultaneously for all masks and real child displacements. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonPhysicalHistoryJointInputs
open Filter Function Finset Lattice RG Precision Wilson FormalBulk08
open Next.Free Reef Flat Exterior Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp
open Pose Glide Bank Dawn Wine Rial Roof Dove Series Trellis Aster Borough Elm
open Planned.PrimaryIntegral295 Place Film Source Source.Drops Labels PowerSeries
open PhysicalNext.Repeat.Legato WilsonRunFormalMarkedStep RG16.Literal RG16.Guarding
open MSbar MSbar.Whisk Push.Uniform WilsonPhysicalHistoryBlockInputs
open scoped Classical Topology BigOperators
variable {G : Gauge} {d D : ℕ}

private theorem enlarge {σ : Type} [Fintype σ] {n : Side} {U : σ→Site n} {z : Site n}
    {a B C : ℝ} {s m : ℕ} {P : Cacao.Pot σ}
    (h : Whisk.Vault U {z} a s m 0 P B) (hc : B≤C) : Whisk.Vault U {z} a s m 0 P C :=
  ⟨h.1.trans hc,fun j hj=>(h.2 j hj).trans hc⟩

private theorem fuse {β : ℝ} (β1 : 1≤β) (p H q b : ℕ) (sizes : b≤q) {δ : ℝ} (δ0 : 0<δ) :
    let ζ := δ/(3*((q:ℝ)+1))
    ((p+1:ℕ):ℝ)*(2:ℝ)^H ≤ β^ζ →
    (WilsonPhysicalHistoryJointProduct.factor p H (β^(2*ζ)))^b ≤ β^δ := by
  intro ζ cash
  have β0 : 0<β := zero_lt_one.trans_le β1
  have ζ0 : 0<ζ := div_pos δ0 (by positivity)
  have mult : WilsonPhysicalHistoryJointProduct.factor p H (β^(2*ζ)) ≤ β^(3*ζ) := by
    calc
      _ ≤ β^ζ*β^(2*ζ) := mul_le_mul_of_nonneg_right cash (Real.rpow_nonneg β0.le _)
      _ = _ := by rw [←Real.rpow_add β0];congr 1;ring
  have denom : 3*ζ*((q:ℝ)+1)=δ := by
    dsimp [ζ];field_simp
  have bal : 3*ζ*(b:ℝ)≤δ := by
    apply le_trans _ denom.le
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact (Nat.cast_le.mpr sizes).trans (by linarith)
  calc
    _ ≤ (β^(3*ζ))^b := pow_le_pow_left₀
      (mul_nonneg (by positivity) (Real.rpow_nonneg β0.le _)) mult b
    _ = β^(3*ζ*(b:ℝ)) := by rw [Real.rpow_mul β0.le (3*ζ) (b:ℝ),Real.rpow_natCast]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le β1 bal

/-- At any fixed perturbative order and number of labels, one stage is chosen
before all later cutoffs, slots, masks, actual block offsets, finite tori and
unit test profiles. The true joint incoming product uses one common anchor. -/
theorem on_run (R : Run G) (L : ∀ i, Lodge ((R.family.path.levels.clock.op i 0).patch))
    (a : hue G) (depth : d<D) (simple : G.Simple) {u : ℕ→ℕ}
    (grant : WilsonWindowFormalPurchase.Canonical u R.kit) (pace : WilsonWindowReportingPace.Slow R.kit)
    (o : Loc G 1) (s p q : ℕ) {δ : ℝ} (δ0 : 0<δ) :
    ∀ᶠ i : ℕ in atTop, ∀ (N : ℕ), i+1≤N → ∀ (n : Side) (base : Site (R.family.S.block i))
      (w : Fin q → Letter (R.family.labels.level d)) (x : Fin q → Site (R.family.S.block i))
      (f : Fin q → Studio D), (∀ j, ‖f j‖≤1) → ∀ mask : Finset (Fin q),
      let β := R.family.path.levels.clock.hatBeta (i+1)
      let Z := ∏ j∈mask, incoming R L a depth N i n (x j) (w j) (f j)
      FVA1Physical.Wilson.BankPaid (wrap n (lift base)) β s p (q*(d+p)) δ Z ∧
      ∀ e ≤ p, (PowerSeries.coeff e Z).totalDegree ≤ mask.card*(d+p) := by
  let H := q*(d+p)
  let ζ := δ/(3*((q:ℝ)+1))
  have ζ0 : 0<ζ := div_pos δ0 (by positivity)
  let C := ((p+1:ℕ):ℝ)*(2:ℝ)^H
  have C0 : 0≤C := by dsimp [C];positivity
  obtain ⟨start,buffer⟩ := eventually_atTop.mp
    (WilsonPhysicalHistoryOffsetFare.temperature R simple C C0 0 ζ0)
  filter_upwards [placed R L a depth simple grant o s p ζ0,
    WilsonPhysicalHistoryOffsetFare.paid R simple pace s ζ0,eventually_ge_atTop start] with i bank travel late
  intro N room n base w x f unit mask
  let β := R.family.path.levels.clock.hatBeta (i+1)
  have β1 : 1≤β := (R.family.path.levels.fits.delayed _).le
  have β0 : 0<β := zero_lt_one.trans_le β1
  let z := wrap n (lift base)
  let T := fun j : Fin q => incoming R L a depth N i n (x j) (w j) (f j)
  have capital : C≤β^ζ := by simpa only [pow_zero,mul_one] using buffer (i+1) (late.trans (Nat.le_succ i))
  have leaf (j : Fin q) (e : ℕ) (he : e≤p) :
      Whisk.Vault (Measuring.chart n G) {z} (Mosaic.αm β) s H 0 (PowerSeries.coeff e (T j))
        (β^(2*ζ)) ∧ (PowerSeries.coeff e (T j)).totalDegree ≤d+p := by
    have h := bank N room (w j) n (x j) (f j) (unit j)
    have relocated := WilsonPhysicalHistoryFieldAnchors.move (Measuring.chart n G)
      (wrap n (lift (x j))) z (WilsonPhysicalHistoryOffsetFare.nonneg β) s H
      (PowerSeries.coeff e (T j)) (h.through H he)
    have shift := travel n base (x j)
    refine ⟨enlarge relocated ?_,(h e he).1⟩
    calc
      _ ≤ β^ζ*β^ζ := mul_le_mul_of_nonneg_right shift (Real.rpow_nonneg β0.le _)
      _ = β^(2*ζ) := by rw [←Real.rpow_add β0];congr 1;ring
  have fund := WilsonPhysicalHistoryJointProduct.finite (Measuring.chart n G) z
    (WilsonPhysicalHistoryOffsetFare.nonneg β) s H p (d+p) T mask (fun j _ => leaf j)
  have mq : mask.card≤q := by simpa using Finset.card_le_univ mask
  have currency := fuse β1 p H q mask.card mq δ0 capital
  constructor
  · intro e he
    exact ⟨(fund e he).2.trans (Nat.mul_le_mul_right _ mq),enlarge (fund e he).1 currency⟩
  · exact fun e he => (fund e he).2

end YM.Integration.WilsonPhysicalHistoryJointInputs

