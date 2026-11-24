import YM.Integration.WilsonUniformUnmarkedReclosure
import YM.Integration.WilsonPhysicalHistoryFormalPayoff

/-! The independent finite Wilson action inherits the original anchored
spatial sums through finite coupling order, uniformly in the upper
cutoff. Its differentiated anchor removes the computed scalar exactly. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonUniformUnmarkedFiniteStrip
open Filter Real Function PowerSeries Lattice RG Wilson Tree Stationary Push.Uniform Bloch Exterior Precision
open FormalBulk08 Jets Flat Reef Mesa Lava Shore Lotus Wine Bank Orb Next.Free Series
open PhysicalNext.Repeat.Legato MSbar MSbar.Heath MSbar.Rolling MSbar.Cacao MSbar.Midpoint MSbar.Bakery
open WilsonConditionalTaylorCourseAttachment WilsonConditionalTaylorFieldBalance
open RG16 RG16.Literal Pert.Asymptotics
open scoped Classical Topology BigOperators

variable {G : Gauge} {n : Side} {p : ℕ}

theorem unchanged {A B : Nesting G n} (h : Fields p A B) {E : ℕ → ℕ} {w a : ℝ} {s : ℕ}
    (original : Alto.Wedge A E w a s p) : Alto.Wedge B E w a s p := by
  constructor
  intro e he
  obtain ⟨positive,anchor⟩:=original.shares e he
  refine ⟨positive,?_⟩
  intro r hr i
  have same : MvPolynomial.pderiv i (coeff e A)=MvPolynomial.pderiv i (coeff e B) := by
    rw [WilsonUniformUnmarkedReclosure.coefficient h he]
    simp
  simpa only [CrossH.cog,same] using anchor r hr i

variable (R : Run G) (simple : G.Simple) (u : G.ColorIndex) (V : Voice G)
variable (bought : WilsonConditionalTaylorPurchase.Inventory u V R.kit)
variable (wood : ∀ j,Lodge (R.family.path.levels.clock.op j 0).patch)
variable (tags : ∀ j n,(primary (R.family.path.levels.clock.op j 0).patch R.family.path.levels.clock.kernel n).Choices)

include simple bought in
theorem wedge (s p : ℕ) (hs : 6 ≤ s) :
    ∀ᶠ k : ℕ in atTop, ∀ N per, k ≤ N → ∀ j, k ≤ j → j ≤ N →
      Alto.Wedge (placed R u wood tags N per j) Alto.Dean (Alto.hat R.family.path.levels j)
        (Alto.candles R.family.path.levels j) s p := by
  have docket:=(Qlocal.Schedule.docket_of_invoice simple R u V bought.2.2).1
  filter_upwards [docket.purse s p (p+4) hs (by omega) (by omega)] with k budget N per kN j lo hi
  obtain ⟨⟨S,law⟩,paid⟩:=budget N per kN
  exact unchanged (WilsonUniformUnmarkedCourse.issued R simple u V bought wood tags N per k p S law j lo hi).1
    ((paid S law).2.2 j lo hi)

include simple bought in
theorem anchored (s p : ℕ) (hs : 6 ≤ s) {η : ℝ} (fee : 0<η) :
    ∀ᶠ k : ℕ in atTop, ∀ N per, k ≤ N → ∀ j, k ≤ j → j ≤ N →
      ∀ e, e ≤ p → ∀ r, r ≤ e+1 → ∀ i : Primary (R.family.side j per) G,
        CrossH.cog (Measuring.chart (R.family.side j per) G) (Alto.candles R.family.path.levels j) s
          (coeff e (placed R u wood tags N per j)) r i ≤ (regulatorRun R.family N per j)^(-η) := by
  let C:=R.family
  have wGrow:=Alto.broad.comp (Multi.Wage.hat_tend simple C.path.levels)
  obtain ⟨start,positive⟩:=eventually_atTop.mp (wGrow.eventually_ge_atTop 1)
  obtain ⟨K,earn⟩:=eventually_atTop.mp
    (WilsonPhysicalHistoryFormalPayoff.polynomial R simple 1 zero_le_one (2*Alto.Dean p) fee)
  filter_upwards [wedge R simple u V bought wood tags s p hs,eventually_ge_atTop start,eventually_ge_atTop K]
    with k pay early late N per kN j lo hi e eh r cap i
  let w:=Alto.hat C.path.levels j
  have w1 : 1 ≤ w := positive j (early.trans lo)
  have w0:=zero_le_one.trans w1
  have β:= C.path.levels.fits.delayed j
  have log0:=Real.log_nonneg β.le
  have pre : w^(Alto.Dean p) ≤ (RG16.Lambda C.path.levels j)^(2*Alto.Dean p) := by
    unfold w Alto.hat Alto.flurry
    rw [←pow_mul]
    apply pow_le_pow_left₀ log0
    unfold RG16.Lambda;linarith
  have full:=((pay N per kN j lo hi).shares e eh).fan r cap i
  have price : w^(Alto.Dean e) / w^(r+1) ≤ w^(Alto.Dean p) :=
    (div_le_self (pow_nonneg w0 _) (one_le_pow₀ w1)).trans (pow_le_pow_right₀ w1 (Alto.ranked eh))
  exact full.trans (price.trans (pre.trans (by simpa only [one_mul] using earn j (late.trans lo) N per hi)))

end YM.Integration.WilsonUniformUnmarkedFiniteStrip
