import YM.AllOrder.Laplace.Hint
/-!
# Price an uncurved comparison of the *curved* diagram's exponential.

No manipulations of termwise integration of an infinite exponential. Use only
along message from the finite-dimensional gauge branch, then multiply the
(real analytically extended) vacuum scalar.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Laplace.SigmaP
open PertExtension.Series Radial Tested MeasureTheory ProbabilityTheory Function Set Metric Filter
open scoped Topology ENNReal ContDiff Classical
open Matrix Lattice ConnectedActivityE6 Blaze Brush Poll PhysicalNext Repeat Lantern Local Vote PositionX.Jet
open scoped BigOperators MatrixOrder
variable {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X]
    {ι:Type}[Fintype ι][DecidableEq ι]
local notation "Y"=> Poll.Body ι
variable {A B:X × Poll.Body ι →ℝ}{m:X→Matrix ι ι ℝ}{ρ:X→Poll.Body ι}

abbrev enrolling (P:ℝ→X)(z:Poll.Body ι)(A:X×Poll.Body ι→ℝ)(ρ:X→Poll.Body ι)(t:ℝ):ℝ:= A (P t,ρ (P t)+t•z)
def dropP (P:ℝ→X)(B : X × Poll.Body ι →ℝ) (m:X→Matrix ι ι ℝ)(ρ:X→Poll.Body ι)(t:ℝ) := B (P t,ρ (P t))+ Lantern.shade m (P t) - Lantern.shade m 0
def slopeP (P:ℝ→X)(A B : X×Poll.Body ι →ℝ)(m:X→Matrix ι ι ℝ)(ρ:X→Poll.Body ι)(t:ℝ) := -climb2 (enrolling P 0 A ρ) t - dropP P B m ρ t
def glowP (P:ℝ→X)(A B:X×Poll.Body ι→ℝ)(m:X→Matrix ι ι ℝ)(ρ:X→Poll.Body ι)(z:Poll.Body ι)(t:ℝ):= Real.exp (grace A B ρ m z (t,P t))

variable (T: Accent A B m ρ) (P:ℝ→X)(hp:ContDiffAt ℝ ω P 0)(hP:P 0=0)
include T hp hP
omit [FiniteDimensional ℝ X] in
lemma avows [FiniteDimensional ℝ X]  (z:Y): enrolling P z A ρ 0=0 ∧ deriv (enrolling P z A ρ) 0=0 ∧ ContDiffAt ℝ ω (enrolling P z A ρ) 0:= by
   let f (x:ℝ):= (P x,ρ (P x)+x•z); have hf:f 0=0:= Prod.ext hP (by simp [f,hP,T.steer.map0]); have he : ContDiffAt ℝ ω f 0:= hp.prodMk (((hP.symm ▸ T.steer.shape).comp (f:=P) 0 hp).add (contDiffAt_id.smul contDiffAt_const))
   have hh:HasDerivAt (enrolling P z A ρ) 0 0:= by
       exact ((show HasFDerivAt (𝕜:=ℝ) A 0 (f 0) from hf.symm ▸ (T.steer.quiet ▸ (T.steer.hard.differentiableAt (by simp)).hasFDerivAt)).comp_hasDerivAt 0 ((he.differentiableAt (by simp)).hasDerivAt))
   exact ⟨(congr_arg A hf).trans T.steer.root,hh.deriv,(hf.symm ▸ T.steer.hard).comp (f:=f) _ he⟩
omit [FiniteDimensional ℝ X] in
lemma nice_drop [FiniteDimensional ℝ X]  : ContDiffAt ℝ ω (dropP P B m ρ) 0:= by
   let f (x:ℝ):=(P x,ρ (P x)); have hf: f 0=0:= by simp [f,hP,T.steer.map0]
   have hv:ContDiffAt ℝ ω f 0:=hp.prodMk ((hP.symm ▸ T.steer.shape).comp (f:=P) _ hp)
   exact (((hf.symm ▸ T.poly).comp (f:=f) _ hv).add ((hP.symm ▸ T.alive).comp (f:=P) 0 hp)).sub contDiffAt_const
lemma nice_slope : ContDiffAt ℝ ω (slopeP P A B m ρ) 0:= (shifty (shifty (avows T P hp hP 0).2.2)).neg.sub (nice_drop T P hp hP)

lemma nice_glow (z:Y) : ContDiffAt ℝ ω (glowP P A B m ρ z) 0:= by
   let F t:= (t,P t); let G₀:=grace A B ρ m z ∘ F; suffices hh:ContDiffAt ℝ ω G₀ 0 from hh.exp; let U y:=climb2 (enrolling P y A ρ)
   let b (x:ℝ):=(P x,ρ (P x)+x•z); let Q x:= dropP P B m ρ x- (U z x-U 0 x) -B (b x)+vote A ρ z (0,0)
   have hB:b 0=0:= Prod.ext hP (by simp [b,hP,T.steer.map0]); have hQ x:= shifty (shifty (avows T P hp hP x).2.2)
   have ht:ContDiffAt ℝ ω b 0:= hp.prodMk (((hP.symm ▸ T.steer.shape).comp (f:=P) _ hp).add (contDiffAt_id.smul contDiffAt_const))
   have hy : ContDiffAt ℝ ω Q 0:= (((nice_drop T P hp hP).sub ((hQ z).sub (hQ 0))).sub (ContDiffAt.comp (g:=B) (f:=b) 0 (hB.symm ▸ T.poly) ht)).add contDiffAt_const
   apply hy.congr_of_eventuallyEq; have hg :ContinuousAt G₀ 0 := by apply ContinuousAt.comp (f:=F) _ _; exact ((show F 0=(0,0) from Prod.ext rfl hP).symm ▸ (grace_nice T z 0).continuousAt); exact continuousAt_id.prodMk hp.continuousAt
   apply (hg.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hy.continuousAt).1;  filter_upwards [(extend_foot T (P:=P) (hP ▸ hp.continuousAt) z).filter_mono (nhdsWithin_le_nhds (s:=({(0:ℝ)}:Set ℝ)ᶜ)),self_mem_nhdsWithin] with i hi hx
   have hc x:enrolling P x A ρ i= i^2*U x i:= shift_two (avows T P hp hP x).1 (avows T P hp hP x).2.1 i
   have hp':vote A ρ z (i,P i)=U z i-U 0 i:=by
       have ho:enrolling P z A ρ i-enrolling P 0 A ρ i=i^2*vote A ρ z (i,P i):=by simp only [enrolling,smul_zero,add_zero]; exact hi
       apply mul_left_cancel₀ (pow_ne_zero 2 (show i≠0 from hx)); rw [mul_sub, ←ho, hc,hc]
   unfold G₀ F Q grace dropP b; rw [Function.comp_apply]; simp only [hp',Lantern.visit, zero_smul,one_smul,add_zero]; abel
lemma cost_shift (z:Y) : ∀ᶠ t in Tested.germ, - (enrolling P z A ρ t)/t^2-B (P t,ρ (P t)+t•z)= slopeP P A B m ρ t+grace A B ρ m z (t,P t)-vote A ρ z (0,0) := by
   filter_upwards [(extend_foot T (P:=P) (hP ▸ hp.continuousAt) z).filter_mono nhdsWithin_le_nhds,Tested.eventually_pos] with t ht hb
   have hy : A (P t,ρ (P t))= t^2 * climb2 (enrolling P 0 A ρ) t := by
     have hg := shift_two (avows T P hp hP 0).1 (avows T P hp hP 0).2.1 t
     convert hg using 1
     simp [enrolling]
   unfold slopeP dropP enrolling grace; change A _-A _= _ at ht
   simp only [Lantern.visit,one_smul,zero_smul,add_zero]; rw [eq_add_of_sub_eq ht, hy]; field_simp; ring
end YM.AllOrder.Laplace.SigmaP
