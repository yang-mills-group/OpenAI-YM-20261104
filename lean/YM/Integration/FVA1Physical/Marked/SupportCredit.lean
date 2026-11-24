import YM.Integration.FVA1Physical.Marked.AllPhysicalHosts

/-! The physical M7a schedule already pays a polynomial bound for the
one-tile exponential support weight. One grade-three vacuum entry in
the purchased tariff suffices. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.FVA1Physical.Marked
open Filter Lattice RG Wilson Pressure Finset PhysicalNext PhysicalNext.Repeat
open ConnectedActivityE6 AnalyticBridge VerifiedReset Next.Scheduling
open Push Push.Uniform Height Roof Input Org Supply Pane Slide
open PriceCompiler ThroughLaunch Opera Boulevard Trio Lantern Roost AllOrder
open Transit WheelP Floe Floe.Step.PlanV Burn Quay Tilt Till Extra.Trajectories RG3.Script.Picnic
open Progress.DirectedRecipe
open scoped BigOperators Classical Topology

/-- The grade-three, two-legged entry has rate exactly g. The tariff
contains the square of the small-field threshold multiplying that entry. -/
theorem support_credit {G : Gauge} (p : BudgetPoint) {y : ℝ} (hy : 1 ≤ y)
    (ht : p.threshold = Pressure.temp y) (ticket : Burn.Capacity G p y 1) :
    Real.exp p.supportExponent ≤ y^3 := by
  let i : Age := ⟨0,0,by decide⟩
  let g := Coat.gStep y
  have hp : 0 < y := zero_lt_one.trans_le hy
  have hg : 0 < g := inv_pos.mpr (Real.sqrt_pos.mpr hp)
  have hgth : g ≤ p.threshold := by
    rw [ht]
    exact le_mul_of_one_le_right hg.le (Real.one_le_exp (sq_nonneg _))
  have hturn : 1 ≤ Push.Local.turnCost p.order p.power :=
    one_le_pow₀ (one_le_mul_of_one_le_of_one_le one_le_two (one_le_pow₀ one_le_two))
  have htwo : 1 ≤ (2:ℝ)^p.order := one_le_pow₀ one_le_two
  have hstartup (v : Age) : 1 ≤ Wages.startup G v.r p.power p.order :=
    one_le_mul_of_one_le_of_one_le htwo (one_le_pow₀
      (one_le_mul_of_one_le_of_one_le htwo (Wages.slot_ge G p.power p.order 0)))
  have ha (v : Age) : 1 ≤ authority (horizon 1) v (strengthP y) :=
    one_le_pow₀ (le_add_of_nonneg_right (abs_nonneg _))
  have hgeom (v : Age) : 1 ≤ (1+(p.B:ℝ))^(Wages.grade v.r p.power p.order) :=
    one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg _))
  have hbill (v : Age) : p.threshold^v.r ≤ Tilt.bill G p p.B v.r (authority (horizon 1) v (strengthP y)) := by
    unfold Tilt.bill
    have h0 := pow_nonneg p.threshold_pos.le v.r
    have h1 := mul_nonneg (zero_le_one.trans (hstartup v)) h0
    have h2 := mul_nonneg h1 (zero_le_one.trans (hgeom v))
    calc
      p.threshold^v.r ≤ Wages.startup G v.r p.power p.order * p.threshold^v.r := le_mul_of_one_le_left h0 (hstartup v)
      _ ≤ _ * (1+(p.B:ℝ))^(Wages.grade v.r p.power p.order) := le_mul_of_one_le_right h1 (hgeom v)
      _ ≤ authority (horizon 1) v (strengthP y) * _ := le_mul_of_one_le_left h2 (ha v)
      _ ≤ _ := le_mul_of_one_le_left (mul_nonneg (zero_le_one.trans (ha v)) h2) hturn
  have htix := ticket.near y (show Burn.Near y y by constructor <;> linarith)
  have hi : i ∈ Age.scope (horizon 1 + 2) := Age.in_scope.mpr (by decide)
  have hi0 : Tilt.rates g i = g := by
    change g^3 * (g^2)⁻¹ = g
    field_simp
  have H : g^3 ≤ Till.Tilt.price p G (horizon 1) p.B (strengthP y) g (Age.scope (horizon 1 + 2)) := by
    apply le_trans _ (single_le_sum (f:=fun v : Age => |Tilt.rates g v| * Tilt.bill G p p.B v.r (authority (horizon 1) v (strengthP y)))
      (fun v _ => mul_nonneg (abs_nonneg _) ((pow_nonneg p.threshold_pos.le _).trans (hbill v))) hi)
    rw [hi0,abs_of_pos hg]
    have hith : g^2 ≤ p.threshold^2 := pow_le_pow_left₀ hg.le hgth _
    rw [pow_succ]
    exact mul_comm (g^2) g ▸ mul_le_mul_of_nonneg_left (hith.trans (hbill i)) hg.le
  have hone : Real.exp p.supportExponent * g^3 ≤ 1 :=
    ((mul_le_mul_of_nonneg_left H (Real.exp_pos _).le).trans htix).trans
      (Real.rpow_le_one_of_one_le_of_nonpos hy (by norm_num))
  have hr : 0 < Real.sqrt y := Real.sqrt_pos.mpr hp
  have hs : (Real.sqrt y) ≤ y := by
    exact (Real.sqrt_le_left hp.le).mpr (by nlinarith)
  have scaled : Real.exp p.supportExponent ≤ (Real.sqrt y)^3 := by
    apply (le_div_iff₀ (pow_pos hg 3)).mpr at hone
    simpa only [g, Coat.gStep, one_div, ← inv_pow, inv_inv] using hone
  exact scaled.trans (pow_le_pow_left₀ hr.le hs _)

/-- The purchase's actual all-order tariff gives the support invoice
on its own schedule without imposing extra hypotheses on stage widths. -/
theorem schedule_support_credit {G : Gauge} (X : PhysicalNext.Repeat.Legato.Run G)
    {R : Roots (G:=G) X.metals.p.profile X.metals.K X.metals.p.kernel} {Q : R.Tab X.rolls}
    (hK : TicketP X.alloy X.kit R Q) :
    ∀ᶠ m in atTop, Real.exp (X.alloy.B.a.budget m).supportExponent ≤ (X.alloy.B.a.clock.hatBeta m)^3 := by
  let A := X.alloy
  filter_upwards [A.B.a.fits.deep.eventually_ge_atTop 1] with m hm
  let y := A.B.a.clock.hatBeta m
  have hy := A.B.a.fits.delayed m
  have H : Quay.BandTar G (A.B.a.params m) 1 y := by
    rw [PriceCompiler.params_eq A.B.valid m]
    exact hK.head' _ _ _ hm (step_paid A.B.a m) _ (A.B.valid.pays m)
  have W := H (A.B.a.budget m) rfl rfl ⟨rfl,rfl,rfl⟩ y (hK.pledge.formal.terra.startup m).clip
    (show y/2 ≤ y by linarith) (show y ≤ 2*y by linarith)
  exact support_credit _ hy.le rfl W.ticket

end YM.Integration.FVA1Physical.Marked
