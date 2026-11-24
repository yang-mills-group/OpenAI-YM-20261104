import YM.Extraction.Round
import YM.XSpace.Uniform

/-!
# Uniform center shifts and integrator for k-regulated graphs

Use Lebesgue average and relative profile on Points n. Shift cells into those
coordinates before comparisons, right-closed convention as baseline Extraction.
Everything finite. Coverage required ONLY on the shape support and a spacing
collar. Can use these center costs (e.g. number of smear weights) before any
graph evaluation. Test derivatives handled thereafter.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Mesh
open Filter Function Set Lattice Expense MeasureTheory Metric
open scoped Topology BigOperators ENNReal ContDiff Classical
variable (p : Mesh) {n : ℕ}

abbrev Tuple := Fin n → p.p.Sites
def back (x : p.Tuple (n:=n)) := lift ∘ x
lemma back_injective : Function.Injective (back p (n:=n)) := fun x y h=> by funext i; rw [← wrap_lift (x i),← wrap_lift (y i),show lift (x i)=lift (y i) from congr_fun h i]

variable (c : Four ℝ)

def room : Points n := points fun _=>WithLp.toLp 2 c
def cell (x : Fin n → Cover) := (fun z : Points n=> z + room c) ⁻¹' Extraction.segment p.spacing x
lemma open_cell (x) : MeasurableSet (p.cell (n:=n) c x) := Continuous.measurable (by fun_prop) (Extraction.measurable_segment p.positive x)
lemma area (x : Fin n → Cover) : volume (p.cell c x) = ENNReal.ofReal (p.spacing^(4*n)):= by
  unfold cell; rw [(measurePreserving_add_right (μ:=volume) (room c)).measure_preimage (Extraction.measurable_segment p.positive x|>.nullMeasurableSet), Extraction.cell_volume p.positive]
lemma rel_eq (x : Fin n → Cover) : p.rel x c= Extraction.tag p.spacing x-room c:=rfl
lemma upper_corner {x : Fin n→ Cover} {z : Points n} (hz : z∈ p.cell c x): dist (p.rel x c) z ≤ (4*n:ℝ)*p.spacing:=by
  rw [rel_eq,dist_eq_norm,sub_sub]; rw [add_comm (room c) z,← dist_eq_norm]; rw [← (show Extraction.address _ _ = x from hz)]; exact Extraction.approximate p.positive (z+room c)

-- Pay a fixed compact collar even if n=0.
variable {p} in
lemma norm_near (hp : p.spacing ≤ 1) {r:ℝ} {z w : Points n} (h : ‖w‖≤r) (ht : dist z w ≤ (4*n:ℝ)*p.spacing):‖z‖≤r+(4*n:ℝ):= by
  rw [dist_eq_norm] at ht; apply le_trans (le_of_eq (congr_arg norm (sub_add_cancel z w).symm)) ((norm_add_le ..).trans _); linarith [mul_le_mul_of_nonneg_left hp (show 0≤ (4*n:ℝ) by positivity)]
lemma gained {r : ℝ} (hp : p.spacing ≤ 1) (hc : c∈p.Box) (h : p.Fits (closedBall (0:Points n) (r+4*n))) (z : Points n) (hz : ‖z‖ ≤ r): ∃ x:p.Tuple, z∈ p.cell c (p.back x):= by
  let y:=Extraction.address p.spacing (z+room c); have he:z∈p.cell c y:=rfl
  have hm := p.cover_window h hc (Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact norm_near hp hz (upper_corner p c he)))
  refine ⟨wrap _ ∘ y,?_⟩; rw [show p.back (wrap _ ∘ y) = y from funext (fun i=>hm i)]; exact he

lemma alone (z : Points n) (x y : Fin n → Cover) (hx : z∈p.cell c x) (hy : z ∈ p.cell c y): x=y:= Eq.trans (Eq.symm (show Extraction.address _ _ =x from hx)) hy

def levels (F : p.Tuple (n:=n) → ℂ) : Points n → ℂ := ∑ x : p.Tuple, (p.cell c (p.back x)).indicator (fun _ => F x)

-- stair evaluated at center *shift* c
lemma stair_at {F : p.Tuple → ℂ} (z : Points n) {x : p.Tuple} (hx : z∈p.cell c (p.back x)): p.levels c F z=F x:=by
  rw [levels,Finset.sum_apply,Finset.sum_eq_single x,indicator_of_mem hx]
  · intro y _ h; exact indicator_of_notMem (fun hy=> h (back_injective p (alone p c z _ _ hy hx))) (fun _=> F y)
  simp
lemma stair_off {F : p.Tuple → ℂ} (z : Points n) (h : ∀ x:p.Tuple,z∉p.cell c (p.back x)): p.levels c F z=0:= by rw [levels,Finset.sum_apply]; exact Finset.sum_eq_zero fun i _=> indicator_of_notMem (h i) _

private lemma integrable_cell (x : Fin n→ Cover) (f : ℂ) : Integrable ((p.cell c x).indicator (fun _ => f)):= by rw [integrable_indicator_iff (p.open_cell c x)]; refine integrableOn_const ?_ (by finiteness); rw [p.area]; exact ENNReal.ofReal_ne_top
lemma integrable_stair (F : p.Tuple (n:=n)→ℂ) : Integrable (p.levels c F):= integrable_finsetSum' _ fun _ _=> integrable_cell ..
lemma stair_exact (F : p.Tuple (n:=n)→ℂ) : (∫ z, p.levels c F z)=(p.spacing^(4*n):ℂ)*∑ x,F x:= by
  simp only [levels,Finset.sum_apply]; rw [integral_finsetSum _ (fun x _=> integrable_cell ..),Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _
  rw [integral_indicator (p.open_cell c _),setIntegral_const,measureReal_def,p.area, ENNReal.toReal_ofReal (pow_nonneg p.positive.le _),Complex.real_smul, Complex.ofReal_pow]
end YM.XSpace.Mesh
