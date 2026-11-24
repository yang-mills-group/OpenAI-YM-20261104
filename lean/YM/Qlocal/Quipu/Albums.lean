import YM.Qlocal.Quipu.TaxC
import YM.Push.STATIONARY_UNIFORM.Scatter
import YM.Comparison.RG02.Assembly.Radial
import YM.AllOrder.Response.Invoice
/-!
 # Families of analytic vases.S.parse.Mark REAL. Countable labels follow paint requests.
 Phase width before τ.Note addresses a particular slot set V← independently queried ℓ.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Quipu.Sonnet
open Function Filter Lattice Laurent RG Wilson Stationary Lasso Zora Work.F02 Metric
open Marker Multi Finset Set
open scoped Topology BigOperators Classical ENNReal ContDiff Matrix.Norms.Frobenius
open ConnectedActivityE6.Blaze Extra.Iteration Push Uniform
variable {V:Type}[DecidableEq V]{ι E:Type} {G:Gauge}{k n j r i:ℕ} {c:Side} {d t a v u C:ℝ}{R:Census V}
open Vase
abbrev Album (ι:Type) (s:Senses R)(G:Gauge)(n:ℕ):= ι→ Vase s G n
variable (p:ι→Prop)(o:V→Site c) {s:Senses R}(A:Album ι s G n)(x:Site c)(U:Config G c)(t':ℕ)
namespace Album
def Health (A:Album ι s G n)(a C:ℝ) : Prop:= SumBudget (fun i=> (A i).fare a) C -- a C variable implicit inaccessible, put explicit
variable (h:A.Health a C)(ha:0 < a)
abbrev readout (i:ι): Config G c→ℝ:= if p i then (A i).read x t' else 0
def realize (P:ι→Prop)(A: Album ι s G n)(x:Site c)(t':ℕ)(U:Config G c):=∑' i, A.readout P x t' i U
def picture (P:ι→Prop)(A: Album ι s G n)(o:V→Site c)(t':ℕ):Config G c→ℝ:= realize (fun i=> P i ∧ Bay.Hears (A i).stage o) A (o (Sonnet.root s)) t'
local notation "K"=> realize p A x t' -- notebook
lemma safe : GaugeInvariant (realize p A x t'):= fun u v=> tsum_congr (fun i=> by unfold readout; split; exact (A i).legitimate _ _ _ _; rfl)
include ha h
lemma summable_fare : Summable (fun i=> (A i).fare a):= h.2.1
lemma global_fund(i:ι): ‖A.readout p x t' i U‖≤ Vase.ticketC G t' n *(A i).fare a:= by unfold readout; split; exact (A i).paid x U ha _; rw [Pi.zero_apply,norm_zero]; exact mul_nonneg (ticketC_pos ..) (h.1 i) -- split positivity adjust
lemma global_sum : Summable (fun i=> A.readout p x t' i U):= Summable.of_norm_bounded (h.2.1.mul_left _) (fun i=> global_fund p A x U t' h ha i)
lemma cap(t':ℕ): ‖A.realize p x t' U‖≤ ticketC G t' n*C:= by let f i:=A.readout p x t' i U; have ht:Summable (fun i=> ‖f i‖):= (h.2.1.mul_left _).of_nonneg_of_le (fun i=> norm_nonneg _) (global_fund p A x U t' h ha); apply (norm_tsum_le_tsum_norm ht).trans; apply (ht.tsum_le_tsum (global_fund p A x U t' h ha) (h.2.1.mul_left _)).trans; rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left h.2.2 (ticketC_pos ..)
lemma aperture_mark : Continuous (realize p A x t'):=by
 apply continuous_tsum (u:=fun i=> ticketC G t' n*(A i).fare a) _ (h.2.1.mul_left _); swap; · intro i; unfold readout; split; exact (A i).cont_ x _; exact continuous_const
 intro i q; exact global_fund p A x q t' h ha i
lemma granted_stall : Envelope K:= ⟨(aperture_mark p A x t' h ha).measurable,ticketC G t' n*C,fun i=> cap p A x i h ha t'⟩
private noncomputable def exposed (i:ι): Ambient G c→ℂ:= if p i then (A i).swatch x t' else 0
private lemma world (M:Ambient G c)(hm: M∈Metric.ball (physical U) (stature t' a)) (i:ι): ‖exposed p A x t' i M‖≤ ticketC G t' n*(A i).fare a:= by unfold exposed; split; exact ferried _ _ _ _ M ha hm; rw [Pi.zero_apply,norm_zero]; exact (show 0≤ _ from mul_nonneg (ticketC_pos ..) (h.1 i))
private lemma global_pay : K U= Complex.re (∑' i, exposed p A x t' i (physical U)):= by
 have hv(i:ι): exposed p A x t' i (physical U)=(A.readout p x t' i U:ℂ):= by unfold readout exposed; split; exact real_bill ..; simp
 simp_rw [hv,← Complex.ofReal_tsum]; rfl
variable [NormedAddCommGroup E][NormedSpace ℝ E] (T:E→ Config G c)
variable {y:E}(hU :∀ i, ContDiffAt ℝ ω (fun t=> G.mat (T t i)) y)
include hU
lemma winter : ContDiffAt ℝ ω (K ∘ T) y:= by
 let f(M:Ambient G c):= ∑' i, exposed p A x t' i M
 have he(i:ι): Differentiable ℂ (exposed p A x t' i) := by unfold exposed; split; exact ((A i).reign x t').differentiable (by simp); exact differentiable_const _
 have hh:AnalyticAt ℂ f (physical (T y)):= analytic_series _ (openness ha t') he (h.2.1.mul_left _) (fun i M hx=> world p A x (T y) t' h ha M hx i) -- order arguments
 have h': ContDiffAt ℝ ω f _:= hh.contDiffAt.restrict_scalars ℝ
 have hy: ContDiffAt ℝ ω (Complex.reCLM ∘ (f ∘ physical ∘ T)) y:= Complex.reCLM.contDiff.contDiffAt.comp (f:= f ∘ physical ∘ T) _ (h'.comp (f:=physical ∘ T) _ (physical_contDiffAt hU))
 refine Eq.mp ?_ hy; exact congr_arg (fun v=> ContDiffAt ℝ ω v y) (funext (fun i:E=> (global_pay p A x _ t' h ha).symm)) -- inspect cast ↑
set_option linter.unusedSectionVars false
lemma jobs (i:ι): ContDiffAt ℝ ω (A.readout p x t' i ∘ T) y := by
   unfold readout; split; swap; · exact contDiffAt_const
   rw [show ((A i).read x t' ∘ T)=Complex.reCLM ∘ ((A i).swatch x t' ∘ physical ∘ T) from ?_]; swap; · funext t; rw [Function.comp_apply]; exact ((congr_arg Complex.re (real_bill (A i) x (T t) t')).trans (Complex.ofReal_re _)).symm
   exact Complex.reCLM.contDiff.contDiffAt.comp _ (((A i).reign x t' |>.restrict_scalars ℝ).contDiffAt.comp _ (physical_contDiffAt hU))
local notation "w"=>capita G n t' k d a
set_option quotPrecheck false
local notation "P₀"=> fun i=> w*(A i).fare a
local notation "F'"=> fun i=> A.readout p x t' i ∘ T
omit hU
lemma paths (hu : Mode T y k d) (j:ι) : Brush k (w*(A j).fare a) 1 (F' j) y:= by
 change Brush _ _ _ (readout p A x t' j ∘ T) _; unfold readout; split
 next ht=> exact Vase.palace (A j) x hu _ ha
 apply (Brush.certified zero_le_one (0:ℝ)).climb _ le_rfl; rw [norm_zero]; exact mul_nonneg (capita_ge G _ _ _ hu.pos ha) (h.1 j)
variable (hq : ∀ᶠ y' in 𝓝 y,∃ c', Mode T y' k c') -- actually uniform bound `∃ c`, from ContDiff at t0
include hU
-- compute derivatives at any point using local radius ⇒ Allows closure (ContDiffAt ω global storage from user's hU). Halo near.W.
lemma printing (he:∀ᶠ y' in 𝓝 y, Mode T y' k d) (hi:i ≤ k): HasSum (fun j=> iteratedFDeriv ℝ i (F' j) y) (iteratedFDeriv ℝ i (K ∘ T) y) := by
   have hz :∀ᶠ y in 𝓝 y,∀ i,ContDiffAt ℝ ω (fun t=> G.mat (T t i)) y:= eventually_all.mpr fun i=> (hU i).eventually (by simp) -- check
   obtain ⟨b,hb,hx⟩ := Metric.eventually_nhds_iff_ball.mp (he.and hz); let B:= Metric.ball y b; have h₀:y∈B:= mem_ball_self hb; let f:= F'; let c := P₀; have hJ i j (he:j∈B) : Allows k (f i) j (c i):= ⟨jobs p A x t' h ha T (hx _ he|>.2) i, Brush.offer.mp (paths p A x t' h ha T (hx _ he|>.1) i) |>.inside⟩ -- argument order
   have hX : Summable c:= (h.2.1.mul_left _); rw [show K ∘ T=(fun j=> ∑' i,f i j) from rfl,iterated_at_sum Metric.isOpen_ball (convex_ball y b|>.isPreconnected) hX hJ h₀ i hi]; exact (Summable.of_norm_bounded hX (fun i=> (hJ i y h₀).norm_le _ hi)).hasSum
lemma ready (hu: Mode T y k d) (hv:∀ᶠ y' in 𝓝 y, Mode T y' k v) : Brush k (capita G n t' k d a*C) 1 (K ∘ T) y:= by
 apply Brush.offer.2; refine ⟨(winter p A x t' h ha T hU).of_le le_top,fun i hi=>?_⟩; let M:ι→ℝ:= P₀; let f:= F'; unfold normJ; rw [← (printing p A x t' h ha T hU hv hi).tsum_eq]; have hh:Summable M:= h.2.1.mul_left _; let g j:= ‖iteratedFDeriv ℝ i (f j) y‖; have hk(j):g j≤ M j:= Brush.offer.mp (paths p A x t' h ha T hu j)|>.inside _ hi; have he:Summable g:=hh.of_nonneg_of_le (fun j=> norm_nonneg _) hk; apply (norm_tsum_le_tsum_norm he).trans ((Summable.tsum_le_tsum hk he hh).trans ?_); unfold M; rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left h.2.2 (capita_ge G n t' k hu.pos ha)

end Album
end YM.Qlocal.Quipu.Sonnet
