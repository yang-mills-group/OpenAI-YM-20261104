import YM.QuadraticLocal.Aperture.Change
import YM.AllOrder.Docket.Panorama
/-!
 # Dummy-variable auxiliary state

 The unmarked `AllOrder` Taylor comparison grants a rather strong analytic capability on
 little tori, with arbitrary stipulated higher order. Need it for joint marked coefficients;
 the asymptotic with just vacuum E terms doesn't imply bounds on arbitrary mixed coefficients!

 We adapt the proof using large extra powers of the coupling. Pressure `.Vote`
 keeps the true unmarked apertures and motion data; only adds a realized *extra activity*
 to this prescribed model on its unmasked quadratic Sienna grammar. Keeps the weight, covariance,
 precision & tags and Haar normalization. When using for the marked case, allow ANY finite set of
 marker atoms in Log, including with origin twists. The gain from Taylor truncation (before choosing
 caller Θ windows) then can be used with finite differences on this *same* activation. Every marker
 must be precise in its g powers and entire perturbation, don't estimate g-inverse chips by such
 as if Θ ≤ g.

 This auxiliary resource is intended for post no-wrap envelopes; e residual travels by its own
 full C.Bank. Keep stage life and COVER fees when transferring to actual (not AUX) tori. No estimates
 on lifted hulls from the auxiliary integral by itself. No promises on MS.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Aperture
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open AllOrder PertExtension.Series AllOrder.Laplace AllOrder.Laplace.SigmaP Response Laurent Stationary
open PositionX.Jet Extra.Iteration AllOrder.Floe AllOrder.Floe.Pace AllOrder.Floe.Aero AllOrder.Floe.StateE
open AllOrder.Catch AllOrder.Catch.Clock Sienna
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G:Gauge} {L n f: Side}{ι:Type*}{T:AllOrder.Catch.Clock ι} {W b D α a B C Ω κ V:ℝ}{k p M:ℕ}
variable {P:Patch}{K:KernelChoices}{S : StepData n f} {s:Teller G}{η : Stage}
open Metric ConnectedActivityE6.Coat
open Till Tilt Lantern Aux Aux.Name
section
variable (F:Forest S.ratio)(p':ℝ→ Config G f→ℝ)(q:ℝ→ Config G f→ℝ)
local notation "X"=> Apex n G
local notation "Y"=> Body (Precision.Key F G)
local notation "Z"=> (Apex n G× Body (Precision.Key F G))
local notation "E"=> (ℝ×(Apex n G× Body (Precision.Key F G)))
-- Central after pulls. Signs encoded negative independently when marker defines physical action term.
def scene (u:E):= q u.1 (F.drape (draw F (Desk.night u.2.1) u.2.2))
variable {o:ChartRatio G} {t:S.Choices} (W:Desk F o p' t)
variable (R:Rise (Aperture.scene F q))
local notation "V'"=> scene F q
include R
lemma accord:Treaty W.hard W.quiet (W.high+V') W.paid:= by
 refine ⟨W.pay.steer,W.pay.activity.add R.nice,fun j hj=>?_,W.pay.ample⟩; funext x; rw [jet_add W.pay.activity R.nice,R.ranks j hj,W.pay.rank j hj]; exact add_zero _
lemma horoscope : ∀ᶠ x in 𝓝 (0:E), 0<x.1 → let U:= Desk.night x.2.1; poundA F t (p'+q) (fun _=> U) x.1 (draw F U x.2.2)* Next.SectorChange.pay o (windmill F x.2.2)= Real.exp (-(W.high x+ scene F q x)/x.1^2)*W.paid x := by
 filter_upwards [W.aff] with x hx hh; obtain ⟨b,y,z⟩:=x; let x':=(b,y,z); let U:= Desk.night y; let T:= draw F U z; let a:=F.drape T; intro Q; have hx : poundA F t p' (fun _=>U) b T *Next.SectorChange.pay o (windmill F z) = Real.exp (-W.high x' / b^2) * W.paid x':= hx hh
 change poundA F t (p'+q) _ b T * _= Real.exp (-(W.high x'+scene F q x')/_)*W.paid x'; rw [show poundA F t _ _ b T=Real.exp (-scene F q x'/b^2)* poundA F t p' (fun _=>U) b T from ?_,mul_assoc,hx,←mul_assoc,← Real.exp_add]
 · exact congr_arg (· * _) (congr_arg Real.exp (by ring))
 unfold poundA rootA; rw [← Real.exp_add]; congr 1
 let g:= noiseTaylor S U a t; change -(p' b a + q b a + g)/_= -(q b a) /_+ - (p' b a + g)/_
 ring
noncomputable def add_Sign : Desk F o (p'+q) t := ⟨W.hard,W.quiet,W.high+V',W.paid,accord F p' q W R,horoscope F p' q W R⟩
end
section
variable {r:Stage}{j:ℕ}{u:ℝ→ℝ} {t w x:ℕ}{U:Push.Uniform.Before G r.width r.paths P.J K (k+3)}
variable (A: Aux.Name G P K u x r k U)
local notation "I"=>Aux.Name G P K u x r k U
local notation "X"=> A.X
local notation "F"=> A.Fs
local notation "ξ"=> Aux.scope x
local notation "d"=> A.Θ
local notation "Θ"=> A.price.threshold
local notation "Y"=> Body A.Vx
variable {O:ChartRatio G}(hO:LocalRatio O)
-- Name's lender.
structure Phase (A: Aux.Name G P K u x r k U) where
    -- entire analytic model. Real activity includes actual anchored atoms (all carriers retained on settled layout).
    shift : ℝ→ Config G A.f→ℝ
    firm : Rise (Aperture.scene A.Fs shift)
    paid : ∀ t,Envelope (shift t)
namespace Phase
variable (Q:Phase A)
local notation "Ω₀"=> Q.shift
local notation "V'"=> scene F Q.shift
abbrev roof:= V'
abbrev roofP:= A.Qc + V'
abbrev agency:= spend A.shape ξ (primitive (f:=A.f) A.tube.up A.tube.high)+ Q.shift
def tallP (hO:LocalRatio O): Desk F O (spend A.shape ξ (primitive (f:=A.f) A.tube.up A.tube.high)+ Q.shift) A.choices := Aperture.add_Sign F _ Q.shift (A.tall O hO) Q.firm
local notation "τ"=> tallP A Q hO
abbrev callP (j:ℕ)(v:A.X):= (ratePlan τ) j v-A.intercept O j
local notation "M₀"=> Poll.sweep (A.Zc 0)⁻¹
local notation "Q₀"=> ((roofP A Q))
lemma raised : Rise (Q₀):= by
 refine ⟨(A.rise.nice).add Q.firm.nice,fun j hj=>?_⟩; ext1 x; rw [roofP,jet_add A.rise.nice Q.firm.nice,A.rise.ranks j hj,Q.firm.ranks j hj]; exact zero_add _
local notation "W₀"=> unroll (A:=A.Ph) (B:=A.Bank O) (M:=A.Zc) (ρ:=A.Mh) (V:=Q₀)
abbrev coinP (O:ChartRatio G)(v:X):= coin (Q₀) v (A:=A.Ph) (B:=A.Bank O) (M:=A.Zc) (ρ:=A.Mh)
include hO
lemma leading (v:A.X) (he:∀ i≤j,Integrable (fun y=> someJ (unroll (A:=A.Ph) (B:=A.Bank O) (M:=A.Zc) (ρ:=A.Mh) (V:=roofP A Q) (W:=v) y) i) (M₀)) : callP A hO Q j v= someJ (slopeP (course v) A.Ph (A.Bank O) A.Zc A.Mh) j+logS (coinP A Q O v) j:= by
 let f:=τ; have hp :0<f.paid 0:= mul_pos (pow_pos hO.scale _) (Real.exp_pos _); have ht:logS (grants f (fun _=>v))= Function.swap (ratePlan f) v:= (logprice f (P:=fun _=>v) contDiffAt_const hp).trans (weigh_const _)
 let P':=course v; let F':=courier (fun (_:ℝ)=>v); let W:=fderiv ℝ f.quiet 0; let w':= trust (fun (_:ℝ)=>v) W; let H:= lends (ρ:= A.Mh) (P:=fun _=>v) contDiffAt_const; let V:=belong f.pay.steer H.p0 H.cont
 have hV (z:ℝ): Envelope ((spend A.shape ξ (primitive (f:=A.f) A.tube.up A.tube.high)+Ω₀) z):= (Floe.orchestra (f:=A.f) A.tube.up A.tube.high A.shape ξ A.legal z A.path.choose_spec|>.fit).add (Q.paid z)
 have hv:grants f (fun _=>v)= f.drawdown P' (A.Mh∘P') := inertia_hold F A.choices w' (A.Mh∘P') (Desk.pension (L:=f) A.loom.large.1 hO hV H) (Desk.pension (L:=f) A.loom.large.1 hO hV V) A.loom.large.1 (light_courier (P:=fun (_:ℝ)=>v) contDiffAt_const) (H.w0 ▸ H.progress.continuousAt) (V.w0 ▸ V.progress.continuousAt) hV
 let D:= 1-f.perk P' (A.Mh∘P'); have h:0 < f.perk P' (A.Mh∘P')+D:=by unfold D; simp
 unfold callP; change ratePlan f j v - _ = _; rw [show ratePlan f j v=logS (grants f (fun _=>v)) j from (congr_fun ht j).symm,hv]
 have hc : f.high=(A.Ph∘Prod.snd)+roofP A Q:= add_assoc ..; rw [show logS (f.drawdown P' (A.Mh∘P')) j=A.intercept O j + someJ (slopeP (course v) A.Ph (A.Bank O) A.Zc A.Mh) j + logS (coinP A Q O v) j from ?_]; · ring
 change logS (Real.exp D • Laplace.part volume (prepare f.high P' (A.Mh∘P') D) (f.paid∘tone P' (A.Mh∘P'))) j = _; rw [hc]; exact receives _ v (A.soft O hO) _ _ h (raised A Q) (pow_pos hO.scale _) he
end Phase
end
end YM.QuadraticLocal.Aperture
