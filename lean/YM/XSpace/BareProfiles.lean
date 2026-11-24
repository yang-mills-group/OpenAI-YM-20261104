import YM.XSpace.Stairs
import YM.XSpace.TestCosts

/-!
# Order-zero comparison for the bare profiles

For the arrays `Initialize.report`, before positioning. All arities, all
weights/horizons, including fields and tests with no bound on arity; *accuracy
per fixed request*. **Simultaneously for all tests** on any indicated compact
geometry, with a fixed `C1` cost. Even-inversion quotient regulator, leading
for every stretched sequence in this project (in particular Run). This
includes existence of these arrays BEFORE expressing coupling at measurement
or imposing position conditions; not an assertion about convergence at higher
orders. No spectral pos assumptions on the Geometry here. All estimates have
been supplied in `YM.XSpace` and imports.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Mesh
open Filter Function Set Lattice Expense Maxwell TestBudget MeasureTheory Metric
open scoped Topology BigOperators ENNReal ContDiff Classical
variable (p : Mesh) {G : Gauge} (D : Initialize G) {n : ℕ} (d : Fin n → ℕ)
variable (V : ∀ i,On.Grade G (d i)) (f : Test n)
local notation "Q" => MaxwellPoint d V

def looked (c : Four ℝ) (x : p.Tuple (n:=n)): ℂ:= f (p.rel (p.back x) c)*p.note D d V x
lemma results (c : Four ℝ) : (∫ z, p.levels c (p.looked D d V f c) z)=
    (p.spacing:ℂ)^(4*n) * ∑ x:p.Tuple (n:=n), f (p.rel (p.back x) c)*p.note D d V x:= p.stair_exact c _

def perCenter (c : Four ℝ):= ∫ z,p.levels c (p.looked D d V f c) z
lemma integral_average : PowerSeries.coeff 0 ((D.report p d f) V) = (p.vol:ℂ)⁻¹ * ∫ c in p.Box,p.perCenter D d V f c:= by
  rw [D.coefficient]; simp_rw [perCenter, results]; rw [integral_const_mul,mul_comm _ (p.vol:ℂ)⁻¹, mul_assoc]; rfl
lemma on_center : IntegrableOn (p.perCenter D d V f) p.Box:= by
  unfold perCenter; simp_rw [results]; apply Integrable.const_mul; exact integrable_finsetSum _ fun i _=> (p.term_integrable f _).mul_const _

lemma averaged_price (x : ℝ) (Q₀ : ℂ) (h : ∀ c ∈ p.Box, ‖p.perCenter D d V f c-Q₀‖≤x):
    ‖PowerSeries.coeff 0 ((D.report p d f) V)- Q₀‖≤x:=by
  set a:=p.vol; let F:= p.perCenter D d V f
  have ha:0<a:=p.vol_pos
  have he : PowerSeries.coeff 0 ((D.report p d f) V)-Q₀=(a:ℂ)⁻¹ * ∫ c in p.Box,(F c-Q₀) := by rw [p.integral_average D d V f, integral_sub (p.on_center D d V f) (integrableOn_const p.compact_box.measure_ne_top),setIntegral_const,Complex.real_smul,mul_sub]; congr 1; exact (inv_mul_cancel_left₀ (show (a:ℂ)≠0 by exact_mod_cast ha.ne') Q₀).symm
  rw [he,norm_mul,norm_inv, Complex.norm_real,Real.norm_of_nonneg ha.le]
  exact (mul_le_mul_of_nonneg_left (norm_setIntegral_le_of_norm_le_const p.compact_box.measure_lt_top h) (inv_pos.mpr ha).le).trans_eq (by change a⁻¹*(x*a)=x; rw [mul_comm x, inv_mul_cancel_left₀ ha.ne'])

lemma unback (x : p.Tuple (n:=n)): wrap p.p.side ∘ p.back x=x:= funext fun i=> wrap_lift (x i)

set_option maxHeartbeats 450000 in
theorem compare_center (K : Set (Points n)) (r : ℝ) (hp : p.spacing ≤ 1) (s : p.Fits (closedBall (0:Points n) (r+4*n)))
    (hf : tsupport f ⊆ K) (hr : ∀ x∈K, ‖x‖≤r) (c : Four ℝ) (hc : c∈p.Box) {b C M : ℝ} (hM : 0≤M) (hC : 0≤C) (hb : Bound f b)
    (hK : ∀ x : p.Tuple, p.rel (p.back x) c∈K → ‖p.note D d V x-MaxwellPoint d V (p.rel (p.back x) c)‖≤ C*p.spacing)
    (hm : ∀ x y:Points n, ‖Damp f (MaxwellPoint d V) x - Damp f (MaxwellPoint d V) y‖ ≤ b*M*dist x y):
    ‖p.perCenter D d V f c-f.applyTo (MaxwellPoint d V)‖ ≤ b*((C+(4*n:ℝ)*M)*volume.real (closedBall (0:Points n) (r+4*n)))*p.spacing := by
  set W:=closedBall (0:Points n) (r+4*n)
  let q:=Damp f Q; let R:=p.levels c (p.looked D d V f c); let P := b*(C+(4*n:ℝ)*M)*p.spacing
  have hb' : 0≤b:=bound_nonneg f hb; have hP: 0≤P:=by unfold P; have h:=p.positive; positivity
  have hs (x : Points n) (h : x∉ K) : f x=0:= image_eq_zero_of_notMem_tsupport (fun hi=>h (hf hi))
  have hbq (x : Points n) (h : x∉ K): q x=0:=mul_eq_zero_of_left (hs x h) _
  have hut (z): z∈W ↔ ‖z‖≤r+4*n:=by rw [mem_closedBall,dist_zero_right]
  have he (z) : ‖R z-q z‖ ≤ P ∧ (z∉ W→ R z-q z=0) := by
    by_cases h:∃ x:p.Tuple (n:=n),z∈p.cell c (p.back x)
    · obtain ⟨x,hx⟩:=h; let a:=p.rel (p.back x) c; have he := p.upper_corner c hx
      have hg : R z=f a*p.note D d V x := p.stair_at c z hx
      have hk : ‖R z-q a‖ ≤ b*C*p.spacing := by
        rw [hg,show q a=f a*Q a from rfl, ← mul_sub,norm_mul]; by_cases h:a∈K
        · rw [mul_assoc b]; exact mul_le_mul (hb a).1 (hK x h) (norm_nonneg _) hb'
        rw [hs a h,norm_zero,zero_mul]; have h:=p.positive; positivity
      constructor
      · calc
          _ ≤ ‖R z-q a‖ + ‖q a-q z‖ := by rw [show R z-q z = _ from (sub_add_sub_cancel (R z) (q a) (q z)).symm]; exact norm_add_le ..
          _ ≤ b*C*p.spacing + b*M*((4*n:ℝ)*p.spacing):= by exact add_le_add hk ((hm a z).trans (mul_le_mul_of_nonneg_left he (by positivity)))
          _ = P:= by unfold P; ring
      intro hu; rw [hg,hs a (fun h=> hu ((hut z).2 (norm_near hp (hr a h) (le_trans (le_of_eq (dist_comm ..)) he)))),zero_mul,hbq z (fun h=> hu ((hut z).2 ((hr z h).trans (by simp)))), sub_self]
    rw [hbq z (fun H => h (p.gained c hp hc s z (hr z H))),show R z=0 from p.stair_off c z (fun x hx=> h ⟨x,hx⟩)]; simp [hP]
  change ‖(∫ z,R z)-(∫ z,q z)‖≤_
  rw [← integral_sub (p.integrable_stair ..) (TestBudget.integral_pays f Q (fun _ hx=> smoothMaxwell d V hx)),← setIntegral_eq_integral_of_forall_compl_eq_zero (s:=W) (fun z=> (he z).2)]; exact (norm_setIntegral_le_of_norm_le_const (isCompact_closedBall ..|>.measure_lt_top) (fun x _=> (he x).1)).trans_eq (by unfold P W; ring)

variable {ι : Type*} {u : Filter ι} {P : ι → Mesh}
/-- Preliminary order-zero conclusion (pre-frame adjustment), with genuine quantitative control across all profiles. -/
theorem leading_order (S : Stretched u P) (K : Set (Points n)) (h : IsCompact K) (hp : K ⊆ conf n): ∃ C:ℝ,0≤C∧∀ᶠ i in u, ∀ f:Test n, tsupport f ⊆ K → ∀ b:ℝ, Bound f b → ‖PowerSeries.coeff 0 ((D.report (P i) d f) V)- f.applyTo (MaxwellPoint d V)‖ ≤ b*C*(P i).spacing := by
  obtain ⟨B,hB,H⟩:= uniform D d S K h hp V
  obtain ⟨r,hr⟩:=(h.image continuous_norm).bddAbove
  obtain ⟨M,hM,hf⟩:= TestBudget.global h hp (MaxwellPoint d V) (fun _ hx=> smoothMaxwell d V hx)
  let K':= closedBall (0:Points n) (r+4*n); let C:= (B+4*n*M)*volume.real K'
  refine ⟨C,by unfold C; positivity,?_⟩
  filter_upwards [H,fits_compact S K' (isCompact_closedBall ..),S.smaller] with i Hi Hi' Hi'' f hv b hb
  refine (P i).averaged_price D d V f _ _ (fun c hc=>compare_center (P i) D d V f K r Hi'' Hi' hv (fun x hx=>hr (Set.mem_image_of_mem _ hx)) c hc hM hB.le hb (fun x hx=> ?_) (hf f hv b hb))
  specialize Hi ((P i).back x) c hc hx; rw [unback] at Hi; exact Hi
end YM.XSpace.Mesh
