import YM.AllOrder.Catch.Scale
import YM.AllOrder.Laplace.Native
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Catch
open Function Filter Matrix Metric MeasureTheory ProbabilityTheory Finset
open ConnectedActivityE6 Blaze Brush Poll Local Vote Clock
open PositionX.Jet PhysicalNext Repeat Lantern
open Laplace Laplace.SigmaP PertExtension PertExtension.Series Radial Tested
open scoped Topology ENNReal BigOperators Classical ContDiff Polynomial
variable {X:Type} [NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X]
variable {ι:Type}[Fintype ι][DecidableEq ι]
local notation "Y"=> Body ι
local notation "Ω"=> ℝ×(X×Y)
variable (V:ℝ× (X× Body ι)→ℝ) (W:X) {n:ℕ}
    {A B: X× Body ι→ℝ}{M:X→ Matrix ι ι ℝ}{ρ:X→Body ι}
    (h:Accent A B M ρ)
local notation "T"=> course W
structure Rise (V:ℝ× (X× Body ι)→ℝ):Prop where
   nice : ContDiffAt ℝ ω V 0
   ranks : ∀ i≤2, jet V i=0
namespace Rise
variable {V} (hX:Rise V)
include hX
lemma bills : V 0=0 ∧ fderiv ℝ V 0=0:= by
 refine ⟨?_,?_⟩; · have ht:= congr_fun (hX.ranks 0 (by omega)) 0; simp [jet] at ht; exact ht
 apply ContinuousLinearMap.ext; intro x; rw [← Laplace.zero_first]; exact congr_fun (hX.ranks 1 (by omega)) x
end Rise
abbrev issueb (v:Y) (t:ℝ):= V (t,course W t,ρ (course W t)+ t • v) -- ρ implicit unused param? include
abbrev uplift (P:ℝ→X) (ρ:X→Y) (v:Y) (t:ℝ):= (t,P t,ρ (P t)+t•v)
abbrev plunge (v:Y) (t:ℝ):= V (uplift (T) ρ v t)
local notation "W₀"=> ρ ∘ course W
-- Ray Convention.Ew: formally shift. Square for venue valuation.
variable (hV:Rise V)
local notation "U"=> plunge (ρ:=ρ) V W
include h hV
lemma sign (z:Y) : plunge (ρ:=ρ) V W z 0=0 ∧ deriv (plunge (ρ:=ρ) V W z) 0=0 ∧ someJ (plunge (ρ:=ρ) V W z) 2=0∧ContDiffAt ℝ ω (plunge (ρ:=ρ) V W z) 0:= by
 let f:ℝ→Ω:= uplift (T) ρ z; let P:=T; have hx : f 0=0:= (by simp [f,course,uplift,h.steer.map0]); apply And.intro ((congr_arg V hx).trans hV.bills.1)
 have hh : HasFDerivAt (𝕜:=ℝ) V 0 (f 0):= hx.symm ▸ (hV.bills.2 ▸ (hV.nice.differentiableAt (by simp)).hasFDerivAt); have hp : ContDiffAt ℝ ω P 0:= (course_claim h W).cont; have hz:P 0=0:= (course_claim h W).p0
 have he:ContDiffAt ℝ ω f 0:= contDiffAt_id.prodMk (hp.prodMk (((hz.symm ▸ h.steer.shape).comp (f:=P) _ hp).add (contDiffAt_id.smul contDiffAt_const)))
 have h':ContDiffAt ℝ ω ((U) z) 0:=(hx.symm ▸ hV.nice).comp (f:=f) _ he
 refine ⟨(show HasDerivAt (V ∘ f) 0 0 from hh.comp_hasDerivAt (0:ℝ) (he.differentiableAt (by simp)).hasDerivAt).deriv,?_,h'⟩; change someJ (V ∘ f) 2=0; rw [show someJ (V ∘ f) 2=jet (V ∘ f) 2 1 from ?_, jet_two_C he hV.nice hx hV.bills.2]; -- unresolved input jet
 · exact congr_fun (hV.ranks 2 le_rfl) _
 simpa only [smul_eq_mul,mul_one] using jet_entry (h:=(V ∘ f)) (n:=2) (h'.of_le le_top) (1:ℝ)
variable {V W}
include h hV
local notation "Gc"=> grace A B ρ M
def warmP (A B:X× Body ι→ℝ)(M:X→Matrix ι ι ℝ)(ρ:X→Body ι)(V:Ω→ℝ)(W:X)(y:Y):ℝ→ℝ:= fun t=> grace A B ρ M y (t,course W t) - climb2 (plunge (ρ:=ρ) V W y) t
abbrev unroll (v:Y):= Real.exp ∘ warmP A B M ρ V W v
lemma worth (z:Y): ContDiffAt ℝ ω (fun t=> Gc z (t,course W t)) 0:= by
 let G t:= Gc z (t,T t); let hT:=course_claim h W; have ht:= nice_glow h _ hT.cont hT.p0 z; rw [show (fun t=> G t)= Real.log ∘ (glowP (T) A B M ρ z) from funext fun i=>(Real.log_exp _).symm]; exact (Real.contDiffAt_log.mpr (Real.exp_pos _).ne').comp (f:=glowP (T) A B M ρ z) _ ht
lemma fee (v:Y): ContDiffAt ℝ ω (warmP A B M ρ V W v) 0 := (worth h hV v).sub (shifty (shifty (sign V W h hV v).2.2.2))
lemma initial (v:Y): warmP A B M ρ V W v 0=0:= by
 let q:= sign V W h hV v
 unfold warmP; simp only [course,zero_smul]; rw [show climb2 (plunge V W v (ρ:=ρ)) 0=0 from Eq.trans ((someJ_zero _).symm.trans (congr_fun (retrace q.1 q.2.1 q.2.2.2) 0)) q.2.2.1, sub_zero, zeroC]
omit hV in
lemma expense (Ep:Rise V)(r:ℝ) : Treaty A ρ ((A ∘ Prod.snd)+V) (fun x:Ω=> r*Real.exp (-B x.2)):= by
 let ht:= tripped h r; refine ⟨ht.steer,ht.activity.add Ep.nice,fun i hi=> ?_,ht.ample⟩; funext j; rw [jet_add ht.activity Ep.nice,Ep.ranks i hi]; exact add_zero _
local notation "g"=> unroll (A:=A) (B:=B) (M:=M) (ρ:=ρ) (V:=V) (W:=W)
variable (W) (R:ℝ) (r:ℝ) (hr:0< Laplace.curvature A (fderiv ℝ (course W) 0 1) (fderiv ℝ (ρ ∘ course W) 0 1)+r)
local notation "Q"=> prepare ((A∘Prod.snd)+V) (course W) (ρ∘course W) r
set_option quotPrecheck false
local notation "Hi"=> fun p:Ω=> R*Real.exp (-B p.2)
local notation "Ψ"=> (Hi)∘ tone (course W) W₀
local notation "S"=> Real.exp ∘ slopeP (course W) A B M ρ
local notation "α"=> Real.exp (-r)*R*munit (M 0)
local notation "J"=> Shield.lens₀ (M 0)⁻¹
include hr
lemma melt (z:Y) : (fun n=> normTerm Ψ Q n (onLane z))= fun i=> α * J z * plus (someJ S) (someJ (g z)) i:= by
 let c':=α*J z; let f t:= c'*(S t*g z t); have hk:= approved (expense h hV R) (course_claim h W) hr; let hP:= (course_claim h W).cont; let hp:=(course_claim h W).p0
 have hm: ContDiffAt ℝ ω (g z) 0:= (fee h hV z (W:=W)).exp; have hs:ContDiffAt ℝ ω S 0:=(nice_slope h _ hP hp).exp
 rw [coined hk.revenue hk.income («g»:=f) (contDiffAt_const.mul (hs.mul hm))]
 · rw [show f= (fun (_:ℝ)=> c')*((S)*(g z)) from rfl, some_mul contDiffAt_const (show ContDiffAt ℝ ω ((S)*(g z)) 0 from hs.mul hm),some_mul hs hm, show someJ (fun (_:ℝ)=> c')=just c' from funext (fun i=> (Act.static c' (n:=i)).writes i le_rfl),exact_scale]; rfl
 filter_upwards [cost_shift h _ hP hp z,Tested.eventually_pos] with t ht hb
 rw [projection_eq]; have hc : tone (course W) (ρ ∘ course W) (t • onLane z)= (t,course W t,ρ (course W t)+t • z):=by simp [tone,onLane]
 unfold prepare; simp only [Pi.add_apply, Function.comp_apply,hc ]; simp only [onLane,Prod.smul_mk,smul_eq_mul, mul_one]
 let y:= (course W t,ρ (course W t)+ t• z); let q:= slopeP (course W) A B M ρ t; let a:= grace A B ρ M z (t, course W t); let i:= vote A ρ z (0,0); let u:=climb2 ((U) z) t; change -(A y)/t^2-B y=q+a-i at ht
 have he: V (t,y)=t^2 *u:= Laplace.SigmaP.shift_two (sign V W h hV z|>.1) (sign V W h hV z|>.2.1) _
 change R*Real.exp (-B y)*Real.exp (-(A y+V (t,y)+r*t^2)/t^2)=(Real.exp (-r)*R*munit (M 0)*J z)*(Real.exp q*Real.exp (a-u))
 rw [he, show -(A y+t^2*u+r*t^2)/t^2= -r+ -(A y)/t^2-u from (by field_simp; ring), show -A y/t^2=q+a-i+B y from (by linarith),mul_assoc R, ← Real.exp_add,mul_assoc _ (munit _), sip_read h z, show -B y+(-r+(q+a-i+B y)-u)=-r+ -i +(q+(a-u)) from (by ring)]
 rw [Real.exp_add, Real.exp_add, Real.exp_add]; ring
end YM.AllOrder.Catch
