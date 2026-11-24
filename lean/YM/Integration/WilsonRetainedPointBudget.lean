import YM.Integration.QLocalRadialBudget
import YM.Integration.WilsonRootedTwoDatePointGallery
import YM.Integration.LocalComparisonFunctionalRetains

/-! The native divided budget of the true deposited signed source before choosing its tests. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section

namespace YM.Integration.WilsonRetainedPointBudget
open Filter Function Finset Lattice Wilson RG Marker Overlay Push.AbsoluteSums
open RG3.Held RG3.Script.Picnic LocalComparison ComparisonDensity.Address PhysicalNext.Repeat.Legato
open Pert.Asymptotics
open scoped BigOperators Classical Topology

variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V] [Fintype V]
variable {P : Rep G n} (D : V→Orbit) (a : Bands (Stock.census V) P)

def table : Taste (IndependentTests D) a.origins P (Stock.census V) :=
  QLocalRadialBudget.taste a (fun (x : IndependentTests D) v=>(x v).val 0)
    a.rays a.support (fun _ _=>0)

theorem divided {w : V→ℝ} {c d b : ℝ} (hb : 0<b) (ha : a.Active)
    (hr : a.Radial w 0 c d b) :
    Nonempty (FullBudget P.p (table D a) w b (Real.exp 1*c) d) := by
  have cap (v : V) : w v * 1 ≤ w v := by simp
  have signs (x : IndependentTests D) :
      ((table D a).leaf x).captions.Sound a.origins := ⟨ha.proper,ha.pins⟩
  have zero (v : V) : SumBudget (fun i : ℕ => if v∈(a.rays i).val then
      Poly.toll w (a.rays i) * P.p.mass (a.support i) 0 else 0) 0 := by
    simp [SumBudget,BudgetPoint.mass]
  have all := QLocalRadialBudget.budget a ha hr.pure (fun _ : V => zero_le_one)
    cap hr (fun (x : IndependentTests D) v=>(x v).val 0) (WilsonOriginalPointModes.root_bound D)
    a.rays a.support (fun _ _=>0) (fun _=>0) (fun _=>le_rfl) (by simp) signs hb zero
  have cancel : d*b/b=d := by field_simp
  simpa only [zero_add,add_zero,cancel,table] using all

theorem retains (ha : a.Active) :
    FunctionalRetains (table D a) (fun v=>{a.origins v}) := by
  apply FunctionalRetains.of_active
  intro x
  exact ⟨QLocalRadialPublication.active a ha (fun v=>(x v).val 0),⟨ha.proper,ha.pins⟩⟩

theorem eventually_divided {R : Run G} (hG : G.Simple) {room : ℝ} (pos : 0<room) :
    ∀ᶠ m : ℕ in atTop, ∀ N p, m+2 ≤ N → ∀ prev : ℕ,
      (Real.sqrt 2 * regulatorRun R.family N p (m+2))^(prev+1) ≤ room := by
  let cap := min 1 room / Real.sqrt 2
  have two : 0 < Real.sqrt 2 := by positivity
  have hcap : 0<cap := div_pos (lt_min zero_lt_one pos) two
  obtain ⟨start,bought⟩ := eventually_atTop.mp (IterationFour.Currency.g_small hG R.makes cap hcap)
  filter_upwards [eventually_ge_atTop start] with m hm N p before prev
  let g := regulatorRun R.family N p (m+2)
  have hg : 0≤g := (IterationFour.Currency.g_pos R.makes N p (m+2) before).le
  have hcost : g < cap := bought (m+2) (by omega) N p before
  have bound : Real.sqrt 2 * g ≤ min 1 room := by
    rw [mul_comm]
    exact ((lt_div_iff₀ two).mp hcost).le
  calc
    _ = (Real.sqrt 2*g)^prev * (Real.sqrt 2*g) := pow_succ _ _
    _ ≤ 1 * (Real.sqrt 2*g) := mul_le_mul_of_nonneg_right
      (pow_le_one₀ (mul_nonneg two.le hg) (bound.trans (min_le_left _ _))) (mul_nonneg two.le hg)
    _ ≤ room := (one_mul _).le.trans (bound.trans (min_le_right _ _))

end YM.Integration.WilsonRetainedPointBudget

