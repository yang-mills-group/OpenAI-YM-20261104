import YM.MSbar.Pole.Scale.Motion
import YM.MSbar.Pole.Analysis.Compensate
import YM.MSbar.Pole.Analysis.Exponents

/-! # Joint polylog Mellin remainder on stripped tensor tests -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole.Ray
open Function Set Filter MeasureTheory Ambient Momentum
open scoped Topology ContDiff Classical BigOperators
variable {E A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

variable {U : Set ℂ} {H : ℂ→ℝ × E→ℂ} (o:IsOpen U) (h : Wall U (ticket (@id (ℝ × E))) 1 H)
local notation "dash" => Ioc (0:ℝ) 1
local notation "ν" => volume.restrict dash
variable (L N : ℂ)

include h o
lemma marching : Barrel ν (strip E U) (stretch (ticket (@id E))) 1 (fun r z=> H z.1 (r,z.2)) := by
  let x (r:ℝ):ℂ × (ℝ × E):=(0,r,0)
  let V:=ContinuousLinearMap.fst ℝ ℂ E; let W:=ContinuousLinearMap.snd ℝ ℂ E
  let D : ℂ × E→L[ℝ]ℂ × (ℝ × E):= V.prod ((0:ℂ×E→L[ℝ]ℝ).prod W)
  have hs r (t:ℂ×E): x r + D t = (t.1,r,t.2) := by change (0+t.1,r+0,0+t.2)=_; simp
  have hk : ‖D‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun t=> ?_
    rw [one_mul]; change max ‖t.1‖ (max ‖(0:ℝ)‖ ‖t.2‖) ≤ max ‖t.1‖ ‖t.2‖; simp
  have hb:=pullBarrel (T:=x) (p:=stretch (ticket (@id E))) (q:=1) (μ:=ν) (fun _=>D) h.stream (o.prod isOpen_univ)
    (show ContinuousOn (fun (q:ℂ×E) => 1+‖q.2‖) _ from continuousOn_const.add continuousOn_snd.norm)
    zero_le_two (Eventually.of_forall fun _=> hk.trans one_le_two) ?_ ?_
  · simp_rw [hs] at hb; exact hb
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz t ht
    simp_rw [hs]; refine ⟨mem_prod.mpr ⟨ht.1,mem_univ _⟩,?_,(by exact (show (1:ℝ) ≤ 2*1 by norm_num))⟩
    change 1+max ‖z‖ ‖t.2‖≤ 2*(1+‖t.2‖); rw [Real.norm_of_nonneg hz.1.le]
    cases le_total z ‖t.2‖ with
    | inl h=> rw [max_eq_right h]; linarith [norm_nonneg t.2]
    | inr h=> rw [max_eq_left h]; linarith [hz.2,norm_nonneg t.2]
  intro k hv; simp_rw [hs]
  apply Continuous.aestronglyMeasurable
  refine continuous_iff_continuousAt.mpr fun i:ℝ=> ?_
  exact (h.stream.smooth (k.1,i,k.2) ⟨hv.1,mem_univ _⟩).continuousAt.comp (f:=fun i:ℝ=>(k.1,i,k.2)) (x:=i) (by fun_prop)

def later (H : ℂ→ℝ × E→ℂ) (L N:ℂ)(z:ℂ)(x:E):= ∫ t : ℝ in dash,H z (t,x)*(t:ℂ)^(N+L*z)
lemma carrying (hq : ∀ z∈U, 1≤(N+L*z).re) :
    Wall U (ticket (@id E)) 1 (later H L N) ∧ ∀ z∈U, ∀ x:E,Integrable (fun t:ℝ=> H z (t,x)*(t:ℂ)^(N+L*z)) ν := by
  let D : ℂ × E→L[ℝ]ℂ:= L • ContinuousLinearMap.fst ℝ ℂ E
  let G (t:ℝ) (x:ℂ × E) := (t:ℂ)^(N+D x)
  have hg (t : ℝ) (ht:0<t) : ContDiff ℝ ∞ (G t):=by
    unfold G; simp_rw [Complex.cpow_def_of_ne_zero (x:=(t:ℂ)) (by exact_mod_cast ht.ne')]; fun_prop
  have hb := leibniz_small (G:=G) (marching o h) (fun x hx=> ?_) ?_ ?_
  · refine ⟨⟨hb.integrates, fun z hz x=> ?_⟩, fun z hz x=> hb.integrable (x:=(z,x)) (mem_prod.mpr ⟨hz,mem_univ x⟩)⟩
    apply holo hb (mem_prod.mpr ⟨hz,mem_univ _⟩)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    apply (h.region z hz (t,x)).mul
    change DifferentiableAt ℂ (fun z' => (t:ℂ)^(N+L*z')) z
    have ht' : (t:ℂ)≠0:= by exact_mod_cast ht.1.ne'
    simp_rw [Complex.cpow_def_of_ne_zero ht']; fun_prop
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    exact fun t ht=> (Complex.continuousAt_ofReal_cpow_const t (N+D x) (Or.inr ht.1.ne')).continuousWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht; exact fun _ _=> (hg t ht.1).contDiffAt
  intro i; refine ⟨(i:ℝ)^i*‖D‖^i,(by positivity),?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht x hx
  exact Power.near_bill D ht.1 ht.2 N x i (hq _ hx.1)

lemma once_at_zero : Wall U (ticket (@id E)) 1 (fun z x=> H z (0,x)):= by
  let K:=ContinuousLinearMap.inr ℝ ℝ E
  refine h.pull K (q:=1) ?_ (Bills.const _)
  refine bill_byprice (p:=ticket (@id E)) (s:= (ticket (@id (ℝ × E))).back K) (fun x hx=>?_)
  change 1+max ‖(0:ℝ)‖ ‖x‖≤ 1+‖x‖; simp
end YM.MSbar.Pole.Ray
