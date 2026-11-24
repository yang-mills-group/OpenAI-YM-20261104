import YM.Qlocal.Horn
import YM.AllOrder.Docket.Hour
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Bind
open Function Filter Set Metric Lattice MeasureTheory ProbabilityTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis Bid
open AllOrder Ker Laplace Laplace.SigmaP Response Catch
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open Marker Multi PertExtension.Series Radial Extra.Iteration Floe PositionX.Jet
open Comparison.RG02.Order
open Comparison.RG02.Assembly
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G:Gauge} {k j i q r:ℕ} {n c f :Side}{S:StepData c f} {b α t:ℝ}
open PertExtension PertExtension.Series Sienna Lantern Catch Catch.Clock tether
variable {ι:Type*}{S':Catch.Clock ι}{P:Patch}{T:KernelChoices}{v:Stage}{u:ℝ→ℝ}{κ:ℕ}{F:Uniform.Before G v.width v.paths P.J T (k+3)}
open Aux.Name Presented  Poll
local notation "I"=>Aux.Name G P T u κ v k F
variable (Q : Aux.Name G P T u κ v k F)(R: reed G Q.f) (b:ℝ)
set_option quotPrecheck false
local notation "H"=> changes Q.Fs Q.shape R b (Aux.scope κ)
local notation "w"=>Q.Θ
local notation "Zed"=>Q.Fs.Slice G
local notation "V"=> Desk.night (G:=G)
local notation "X"=>Q.X
local notation "N"=> Poll.Body Q.Vx
local notation "α"=> fun (x:X)=> Fare.overall Q.Fs Q.tube Q.price Q.beta (V x)
-- exact positive/negative Boost readout on auxiliary higher comparison
variable (O:ChartRatio G)(hO:LocalRatio O) (hR:Flute R q) {s:Age→ℝ} (h:Q.Civil s) {x0 y:Q.X} (D C:ℝ) (hQ: Q.goods O D C x0)(hx: ‖y‖ < eaves G P.L Q.whenP)(he: ‖y - x0‖≤ furl G P.L Q.whenP)
namespace Aurum
local notation "μ"=> Poll.sweep (Q.Zc 0)⁻¹
local notation "Y"=>Metric.closedBall (0:N) (Q.wD D)
abbrev pulse {κ:ℕ}{F:Uniform.Before G v.width v.paths P.J T (k+3)} (Q : Aux.Name G P T u κ v k F) (R:reed G Q.f)(b:ℝ)(O:ChartRatio G)(x:Q.X) (z:Poll.Body Q.Vx) := unroll (A:=Q.Ph) (B:=Q.Bank O) (M:=Q.Zc) (ρ:=Q.Mh) («V»:=changes Q.Fs Q.shape R b (Aux.scope κ)) (W:=Q.tulip x) z Q.Θ -- pars note
abbrev feed (x:X):=∫ y in Y, pulse Q R b O x y ∂μ
abbrev act (R:reed G Q.f)(d:ℝ)(B:ℝ)(Z:Config G Q.f):= Q.tilt.eval Z * color R B d Z -- D syntax name conflict
abbrev now (x:X):=Q.data.push Q.beta (act Q R Q.Θ b) (V x)
local notation "scale✷"=> color R b w ∘ Q.Fs.drape
-- stated at ALL fields/directions. Positive trick to preserve outside. Not a new vacuum trajectory.
local notation "x'"=> x0
include hR
lemma spirit (y:X): (∀ i: Config G Q.f, 0 ≤ color R b w i) ∧ Envelope scale✷ ∧ Q.data.push Q.beta (act Q R Q.Θ b) (V y) = now Q R b y:= ⟨fun i=>(openr _).le, Env.along (real_cost R hR b w) Q.Fs.continuous_drape.measurable,rfl⟩
include h in
lemma tastes (y:X): now Q R b y=∫ z,(Q.newZ y * scale✷) z ∂ Q.Fs.order G:= by
 obtain ⟨p,hp,hU⟩:= h.price; let t := Q.data; have he:= Q.loom.large.1; let V₀:= V y; let E:= Q.Fs
 have hv:GaugeInvariant (act Q R Q.Θ b):= by intro z i; unfold act; rw [sky R hR, Presented.lawful_gi hU.cap]
 unfold now; rw [Q.Fs.pushing (Q.data.isKernel he Q.beta) _ V₀ hv (((Q.tilt.envelope hU.cap).mul (real_cost R hR b w)).integrable _) (fun k U=> t.covary he k Q.beta U V₀)]; apply integral_congr_ae; filter_upwards with i; let a:= Q.Fs.drape i; change t.density Q.beta a V₀* (Q.tilt.eval a*_)= (overall Q.Fs Q.tube Q.price Q.beta V₀ i*Real.exp (Q.view a))*_; rw [Q.tilt_eq a, Fare.total, ← mul_assoc, ← mul_assoc] <;> rfl
include hO
lemma concert (y:X) (z:N) : let g:=grace Q.Ph (Q.Bank O) Q.Mh Q.Zc z (w,y); pulse Q R b O y z = Real.exp g * Real.exp (Q.uncloud (Q.Fs.drape (Q.dockP y z))) *scale✷ (Q.dockP y z):= by
 let s':= w; intro g; let u:= Q.Fs.drape (Q.dockP y z); let x:= Q.tulip y; let g' := road (fig R b w u); let v':= plunge H x z (ρ:=Q.Mh); let v₀:= plunge Q.Qc x z (ρ:=Q.Mh); have hp : s' • x=y:= smul_inv_smul₀ Q.Θp.ne' y
 have ht := sign H x (Q.soft O hO) (slope _ _ _ Q.legal _ b hR) z; have hv := sign Q.Qc x (Q.soft O hO) Q.rise z
 have hc : v' w = v₀ w-w^2*g':= by unfold v' v₀ plunge uplift course; rw [show Q.Θ • x=y from hp]; rfl
 have hu : climb2 v' s'=climb2 v₀ s'-g':= by apply mul_left_cancel₀ (pow_ne_zero 2 Q.Θp.ne'); rw [mul_sub, ← Laplace.SigmaP.shift_two ht.1 ht.2.1, ← Laplace.SigmaP.shift_two hv.1 hv.2.1]; exact hc
 have hq: -(climb2 v₀ w)=Q.uncloud u:= Q.curved O hO z y
 unfold pulse Catch.unroll; dsimp only [Function.comp_apply]; unfold warmP course; rw [hp]; change Real.exp (g - climb2 v' w)= _; rw [hu, show g -(climb2 v₀ s' -g') = g + -(climb2 v₀ s') +g' from (by ring), hq,Real.exp_add,Real.exp_add,show Real.exp g'= _ from clear_path (fig R b w u)];
include he hO hQ hx h
lemma skeleton : (∫ i in Q.stayingN D y,(Q.tallZ y*scale✷) i ∂ Q.Fs.order G) = Q.scaleO O y * feed Q R b O D y := by
 obtain ⟨⟨hU,hV,hg,hX⟩,h'⟩:= hQ; let X':= Q.Mh y; let W:= Q.tallZ y * scale✷; let D':= Q.wD D; let hκ z (hz:‖(z:N)‖≤D'):= h' y hx he z hz
 let M z:= pulse Q R b O y z; let s:= Y
 unfold stayingN; rw [cubits Q.Fs O X' _ _ _ W Q.Θp hO (fun z hz=>(hκ z hz).2.1) (((Q.tilt_record h y).2.2.1.mul ((spirit Q R b hR y).2.1)).meas.stronglyMeasurable), ← MeasureTheory.integral_const_mul]; have hh : (∫ z in s, M z ∂μ)=∫ z in s,Shield.lens₀ ((Q.Zc 0)⁻¹) z*M z := by
    have ht:= Shield.recommends _ ((Q.soft O hO).station.self_of_nhds.1.inv) (s.indicator M); let hx:MeasurableSet s:=measurableSet_closedBall; rw [← integral_indicator hx, ← integral_indicator hx]; apply ht.trans; apply integral_congr_ae; filter_upwards with z; by_cases hp:z∈s <;> simp [hp]
 rw [show feed _ _ _ _ _ _= _ from hh,← integral_const_mul]; apply setIntegral_congr_fun measurableSet_closedBall; intro z hz
 let hS := reserves Q.Fs Q.tube O Q.choices Q.σ Q.price Q.beta D' hU Q.bpos hV Q.loom.large.1 hx (fun i hi=> (hκ i hi).2.2) hO (fun i hi=> (hκ i hi).2.1) (fun i hi=>(hκ i hi).1) z hz
 dsimp only; rw [show M z= _ from concert Q R b O hO hR y z]
 let u' := Q.uncloud (Q.Fs.drape (Q.dockP y z)); let v' := grace Q.Ph (Q.Bank O) Q.Mh Q.Zc z (w,y)
 let a:=windmill Q.Fs (X'+w • z); let v₂:=Q.dockP y z; let Y₀:= Fintype.card Q.Vx; let J := Shield.lens₀ (Q.Zc 0)⁻¹ z; let E:=Q.scaleO O y; let V'':= scale✷ v₂
 change w ^ Y₀ * (Next.SectorChange.pay O a*(α y v₂*Real.exp u' *V''))= E*(J*(Real.exp v'*Real.exp u'*V''))
 change w^Y₀* (Next.SectorChange.pay O a * (α y v₂))= E*(J*Real.exp v') at hS
 linear_combination hS * Real.exp u' * V''
/-- Variant of AllOrder.Docket/Hour.peris slender. Since multiplication uses 1+t+t², use BOTH signed slope choices and keep every amplitude actually planned.Solar positivity holds on thin; log extraction later. -/
lemma accounting (a:ℝ) (hY:∀ V': Config G Q.f, flags Q.price.threshold V'=∅→ |Q.view V'-Q.uncloud V'|≤ a ∧ |Q.view V'| ≤1 ∧ color R b Q.Θ V' ≤ 3): let x:= Q.scaleO O y; let q':= now Q R b y/x; let m:=feed Q R b O D y
   Real.exp (-a)*m ≤ q' ∧ q' ≤ Real.exp a*m+3*Real.exp 1*Q.tired D:=by
 intro x t m; let s:= Q.stayingN D y; let ν:=Q.Fs.order G; let A':=α y; let β(i:Q.forest.Slice G):= color R b w (Q.Fs.drape i); let K:=Q.newZ y*β; let p':=Q.tallZ y *β; let N':=Real.exp (-a); let E:=Real.exp 1; let r:=Real.exp a
 obtain ⟨P1,hP,hξ⟩:= h.price; obtain ⟨hW,hP1,H0,H1⟩:= Q.tilt_record h y; let hz:= Q.Θp; have hc i:0 ≤ β i:=(openr _|>.le);
 have hx : 0<x:= mul_pos (Q.born O hO) (Real.exp_pos _);
 have hr' (i:Q.Fs.Slice G) : p' i * N'≤K i ∧ K i ≤ p' i * r ∧ K i ≤ A' i * (3* E) := by
    let f:=Q.Fs.drape i; let z:= Real.exp (Q.view f); let v:= Real.exp (Q.uncloud f); let F:= A' i; let hw:0 ≤ F:=(hW i).2; change F*v*β i*N' ≤ F*z*β i ∧ F*z*β i ≤ F*v*β i*r ∧ F*z*β i≤ _; by_cases hp: flags Q.price.threshold f=∅; swap; · rw [show A' i=0 from (by unfold A'; dsimp only; rw [Fare.total, Pane.sparkling, if_neg hp,mul_zero])]; unfold F; rw [show A' i=0 from (by unfold A'; dsimp only; rw [Fare.total, Pane.sparkling, if_neg hp,mul_zero])]; simp
    obtain ⟨hp,hh,hT⟩:= hY f hp; rw [abs_le] at hp; have hq: v*N' ≤ z:=by unfold v z N'; rw [← Real.exp_add]; exact Real.exp_monotone (by linarith only [hp.1])
    have hq': z ≤ v*r:=by unfold z v r; rw [← Real.exp_add]; exact Real.exp_monotone (by linarith only [hp.2])
    rw [mul_right_comm _ (β i), mul_assoc F, mul_right_comm _ (β i) r, mul_assoc F v, mul_assoc F z (β i)]
    refine ⟨(by rw [←mul_assoc F z]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq hw) (hc i)),(by rw [← mul_assoc F z]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq' hw) (hc i)),?_⟩
    apply mul_le_mul_of_nonneg_left _ hw; rw [mul_comm (3:ℝ)]; exact mul_le_mul (Real.exp_monotone ((le_abs_self _).trans hh)) hT (hc i) (Real.exp_pos _|>.le)
 have hv := Fare.amt Q.Fs Q.tube Q.price Q.beta Q.whenP P1 hP (V y); have hK := hP1.mul (spirit Q R b hR y|>.2.1); have hF := H0.mul (spirit Q R b hR y|>.2.1)
 let W':=∫ i in s,K i ∂ν; let V':= ∫ i in sᶜ,K i ∂ν; let w':= ∫ i in s,p' i ∂ν; have he' : now Q R b y=W'+ V':= (tastes Q R b hR h y).trans (integral_add_compl (staying_meas ..) (hK.integrable ν)).symm; have he0 : w'=x*m:= skeleton Q R b O hO hR h D C hQ ‹_› he
 have hr : V' ≤ x*(3*E*Q.tired D) := by
    let s':=ν.restrict sᶜ; have hp': V' ≤ (∫ i, A' i ∂s')*(3*E):= by rw [← integral_mul_const]; exact integral_mono (hK.integrable s') ((hv.1.integrable s').mul_const _) (fun i=> (hr' i).2.2)
    refine hp'.trans ((mul_le_mul_of_nonneg_right (Aux.Name.accountability Q D O h hO hQ ‹_› he) (mul_nonneg (by norm_num) (Real.exp_pos _).le)).trans_eq ?_); ring
 have ht : N'*m*x≤W' := by rw [show N'*m*x=w'*N' from (by rw [he0]; ring)]; unfold w'; rw [← integral_mul_const]; exact integral_mono ((hF.integrable _).mul_const _) (hK.integrable _) (fun i => (hr' i).1)
 have ht' : W'≤ r*m*x:= by rw [show r*m*x=w'*r from (by rw [he0]; ring)]; unfold w'; rw [← integral_mul_const]; exact integral_mono (hK.integrable _) ((hF.integrable _).mul_const _) (fun i=> (hr' i).2.1)
 have hu:0≤V':= integral_nonneg (fun i=> mul_nonneg ((hW i).1) (hc i)); change N'*m≤ _/x∧now Q R b y/x≤ r*m+3*E*Q.tired D; rw [le_div_iff₀ hx,div_le_iff₀ hx,he']; exact ⟨ht.trans (le_add_of_nonneg_right hu), by rw [add_mul, mul_comm (3*E*Q.tired D)]; exact add_le_add ht' hr⟩
end Aurum
end YM.Qlocal.Bind

