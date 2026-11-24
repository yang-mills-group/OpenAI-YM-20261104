import YM.Integration.WilsonMaxwellThermometerShiftedPanel
import YM.Integration.WilsonMaxwellThermometerFirstPosition

/-! The formal signed first coefficient with the actual test integrated over
each independent child cell of the original reporting mesh. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerFirstCells
open Function Set Filter Finset Metric Lattice Extraction MeasureTheory
open Maxwell XSpace XSpace.Normalize XSpace.Structure1 XSpace.Rose XSpace.Cirrus XSpace.Photo
open WilsonMaxwellThermometerFirstDetector WilsonMaxwellThermometerShiftedPanel
open WilsonSeparatedOriginalThermometerCells
open scoped Topology BigOperators Classical

variable {G : Gauge} (W : Initialize G) {V : Normalize.Store G} (K : Rose.Pick V)

def panel (m : Mesh) : Point G 6 3 :=
  ∑ o : m.Tuple (n:=3),weight (Rose.test K) (cell m) o • atSites W (V:=V) m o

theorem exact_test (m : Mesh) (p : Tags G 6 3) :
    panel W K m p=(Rose.test K).applyTo (fun x=>atSites W (V:=V) m (cell m x) p) := by
  rw [WilsonSeparatedOriginalThermometerCells.tested _ _ (measurable_cell m) (fun o=>atSites W (V:=V) m o p)]
  simp only [panel,_root_.sum_apply,_root_.smul_apply,smul_eq_mul]

private theorem payable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (χ : Points 3→S) (hc : Measurable χ) (φ : Test 3) (Y : S→ℂ) :
    Integrable (fun x=>φ x*Y (χ x)) := by
  have φb : Integrable (fun x:Points 3=>φ x) := φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  obtain ⟨b,cap⟩ := (Set.finite_range (fun o=>‖Y o‖)).bddAbove
  have y := (measurable_of_countable Y).comp hc
  refine (φb.norm.mul_const b).mono' (φ.continuous.aestronglyMeasurable.mul y.aestronglyMeasurable) ?_
  exact Eventually.of_forall fun x=> by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (cap (Set.mem_range_self (χ x))) (norm_nonneg _)

theorem test_price {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (χ : Points 3→S) (hc : Measurable χ) (Y : S→ℂ) (p : Tags G 6 3) (δ : ℝ)
    (ready : ∀ x∈tsupport (Rose.test K),dist (Y (χ x)) (continuum W (V:=V) x p) ≤ δ) :
    ‖(Rose.test K).applyTo (fun x=>Y (χ x))-(Rose.test K).applyTo (fun x=>continuum W (V:=V) x p)‖ ≤
      (∫ x : Points 3,‖Rose.test K x‖)*δ := by
  let φ := Rose.test K
  let f := fun x=>continuum W (V:=V) x p
  have target : Integrable (fun x=>φ x *f x) := Cirrus.can_pay φ f (conf_open _)
    (sensed W (V:=V) p).priced φ.tsupport_subset (Subset.refl _)
  have test : Integrable (fun x:Points 3=>φ x) := φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  change ‖(∫ x,φ x*Y (χ x))-(∫ x,φ x*f x)‖ ≤ _
  rw [← integral_sub (payable χ hc φ Y) target]
  have point (x : Points 3) : ‖φ x *Y (χ x)-φ x*f x‖ ≤ ‖φ x‖*δ := by
    rw [←mul_sub,norm_mul]
    by_cases hx : x∈tsupport φ
    · have close : dist (Y (χ x)) (f x) ≤ δ := ready x hx
      rw [dist_eq_norm] at close
      exact mul_le_mul_of_nonneg_left close (norm_nonneg _)
    · simp only [image_eq_zero_of_notMem_tsupport hx,norm_zero,zero_mul,le_refl]
  refine (norm_integral_le_integral_norm _).trans ?_
  exact (integral_mono ((payable χ hc φ Y).sub target).norm (test.norm.mul_const δ) point).trans_eq
    (integral_mul_const _ _)

theorem fixed (p : Tags G 6 3) : Tendsto (fun m=>panel W K m p) Front
    (𝓝 ((Rose.test K).applyTo fun x=>continuum W (V:=V) x p)) := by
  let M := ∫ x : Points 3,‖Rose.test K x‖
  have nonneg : 0≤M := integral_nonneg fun _=>norm_nonneg _
  apply Metric.tendsto_nhds.mpr
  intro ε he
  let δ := ε/(M+1)
  have pos : 0<δ := div_pos he (by positivity)
  filter_upwards [WilsonMaxwellThermometerShiftedPanel.placed W K p pos] with m ready
  rw [dist_eq_norm,exact_test]
  refine (test_price W K (cell m) (measurable_cell m) (fun o=>atSites W (V:=V) m o p) p δ ready).trans_lt ?_
  change M*(ε/(M+1))<ε
  rw [←mul_div_assoc,div_lt_iff₀ (by positivity)]
  nlinarith

theorem moving {I : Type*} {l : Filter I} (m : I→Mesh) (geometry : Tendsto m l Front)
    (v : I→Tags G 6 3) (fit : ∀ i,Reads 6 (F:=l) (fun z=>v z i) (Rose.tag G i))
    (simple : G.Simple) :
    Tendsto (fun z=>panel W K (m z) (v z)) l (𝓝 ((Rose.c_T K:ℝ):ℂ)) := by
  rw [←WilsonMaxwellThermometerFirstDetector.normalized W K simple]
  exact lights 6 _ v fit (fun z=>panel W K (m z)) (smeared W K)
    fun p=>(fixed W K p).comp geometry

end YM.Integration.WilsonMaxwellThermometerFirstCells
