import YM.RegulatorIR.Halo.Wall
import YM.RegulatorIR.Ward.Eddy

/-! Plant a new gauge-invariant measuring word in a previously evolved held
Wilson law. The hidden variables, action, quadratic kernel and scalar normalizer
are those of the existing finite-period range. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
noncomputable section
namespace YM.Integration.WilsonIndependentFreshWardBirth
open RegulatorIR RegulatorIR.Laplace RegulatorIR.Binding RegulatorIR.Prim
open RegulatorIR.Diagram RegulatorIR.Budget RegulatorIR.Halo RegulatorIR.Ledger.Sky
open RegulatorIR.Quadratic RegulatorIR.Geometry PertExtension Series Series.Radial Series.Tested MeasureTheory
open Chart Lattice Gauge Filter PowerSeries
open scoped BigOperators Topology ContDiff PowerSeries
variable {G : Gauge} {f : Side} {E I : Type} [Fintype I] [Fintype E]

def hold (A : Hook G Empty I) : Hook G E I := fun t u _ => A t u 1

theorem tune (A : Hook G Empty I) (h : Tune A) : Tune (hold (E := E) A) := by
  constructor
  · exact h.view.comp ((continuous_fst).prodMk ((continuous_fst.comp continuous_snd).prodMk continuous_const))
  · have map_ : ContDiffAt ℝ ∞ (fun z : Meadow G E × ℝ × Meadow G I =>
        ((0 : Meadow G Empty),z.2)) 0 := contDiffAt_const.prodMk contDiffAt_snd
    have hp := h.smooth.comp (f := fun z : Meadow G E × ℝ × Meadow G I => ((0 : Meadow G Empty),z.2)) 0 map_
    change ContDiffAt ℝ ∞ (fun z : Meadow G E × ℝ × Meadow G I => A z.2.1 (expLinks G I z.2.2) 1) 0
    simpa [priceMap,Function.comp_def,expOrigin] using hp

omit [Fintype I] in
theorem cash (V : Hook G E I) (A : Hook G Empty I) (t : ℝ) (u : RoomK G I) :
    scan V (hold A) t u = A t u 1 * scan V 1 t u := by
  unfold scan Laplace.tilt hold
  simp only [Pi.one_apply,one_mul,integral_const_mul]

private theorem printed (V A : Hook G E I) (paid : Bundle V A) (x : Meadow G I) :
    Script (manuscript V A x) (fun t => normalized V A t x) := by
  intro n
  obtain ⟨c,hc,h⟩ := paid.beats ‖x‖ (norm_nonneg _) n
  refine ⟨c,hc,h.mono fun t ht => ?_⟩
  have coeffs : term (manuscript V A x) = tomorrow V A x := funext fun i => coeff_mk ..
  change ‖normalized V A t x - peval (term (manuscript V A x)) n t‖ ≤ _
  rw [coeffs]
  exact ht x le_rfl

theorem single (A : Hook G Empty I) (h : Tune A) (x : Meadow G I) :
    Script (inscription (priceMap A) (0,1,x)) (fun t => A t (expLinks G I (t • x)) 1) := by
  let y : Meadow G Empty × ℝ × Meadow G I := (0,1,x)
  have smooth : ContDiffAt ℝ ∞ (fun t : ℝ => priceMap A (t • y)) 0 := by
    apply h.smooth.comp_of_eq (f := fun t : ℝ => t • y) 0 (contDiffAt_id.smul contDiffAt_const)
    · simp
    · exact zero_smul ℝ y
  have stamp := Script.actual smooth
  rw [lore h.smooth y] at stamp
  simpa [y,priceMap,expOrigin,smul_eq_mul] using stamp

theorem joined (V : Hook G E I) {shape : Viewport G I} (prior : Stead shape V)
    (A : Hook G Empty I) (h : Tune A) (x : Meadow G I) :
    manuscript V (hold A) x = manuscript V 1 x * inscription (priceMap A) (0,1,x) := by
  have left := printed V (hold A) (prior.allows (tune A h)) x
  have right := Script.mul (printed V 1 (prior.allows shapeOne) x) (single A h x)
  have same : (fun t => normalized V (hold A) t x) =
      (fun t => normalized V 1 t x) * (fun t => A t (expLinks G I (t • x)) 1) := by
    funext t
    simp only [Pi.mul_apply,normalized,cash]
    ring
  rw [same] at left
  exact PowerSeries.ext (fun i => congrFun (Aspiration.unique left right) i)

theorem issued {m₀ s₀ m s : ℕ} {κ : Horizon G f → ℝ} {g : ℝ → ℝ}
    {prior old : Orders (Book G f)} (R : RangeR G f κ g s₀ m₀ prior old)
    {B : Portrait G} {field : Orders (Foot G)} (stamp : BasisT m s B field)
    (ceiling : ∀ e, Within (e+m) (field e)) {l P : ℝ} (even : Even f.val) (period : l*f.val=P) :
    let D := Carto G l P even period
    let A := hold (E := R.E) (vital f B)
    Nonempty (RangeR G f κ (fun t => rightSum R.Val A t / rightSum R.Val 1 t)
      s m prior (fun e r => D.scroll (field e r))) := by
  classical
  intro D A
  have plan := gifted f stamp.origin
  refine ⟨{
    E := R.E
    slots := R.slots
    Val := R.Val
    Mark := A
    scalar := R.scalar
    basis := R.basis
    inscription := tune _ plan.tune
    marks := ?_
    archive1 := R.archive1
    archive2 := ?_
    turn := fun _ => rfl }⟩
  · refine ⟨R.marks.bare,?_,R.marks.awake,R.marks.vacuum,R.marks.faces,?_,
      grade_s stamp even period⟩
    · intro y
      rw [joined R.Val R.basis (vital f B) plan.tune y, ← script stamp even period y, mul_assoc]
      rfl
    · intro e r hr
      by_contra high
      have hz : field e r = 0 := by_contra fun hn => high (ceiling e r hn)
      exact hr (by change D.scroll (field e r) = 0; rw [hz,D.scroll_zero])
  · intro k hk u t
    rw [show scan R.Val A = scan R.Val (hold (vital f B)) from rfl]
    rw [cash,cash,R.archive1 k hk u t]
    exact congrArg (fun a => a * scan R.Val 1 t u) (plan.law k hk u t)

end YM.Integration.WilsonIndependentFreshWardBirth
