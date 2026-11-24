import YM.QuadraticLocal.Aperture.Prop
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
variable {r:Stage}{j:ℕ}{u:ℝ→ℝ} {t w x:ℕ}{U:Push.Uniform.Before G r.width r.paths P.J K (k+3)}
variable (A: Aux.Name G P K u x r k U)
local notation "I"=>Aux.Name G P K u x r k U
local notation "X"=> A.X
local notation "F"=> A.Fs
local notation "ξ"=> Aux.scope x
local notation "d"=> A.Θ
local notation "Θ"=> A.price.threshold
local notation "Y"=> Body A.Vx

namespace Phase
variable (Q:Phase A)
local notation "b"=>A.beta
local notation "μ"=> Poll.sweep (A.Zc 0)⁻¹
local notation "FS"=> A.forest.Slice G
local notation "V'"=> Desk.night
local notation "Z"=> fun x=>overall F A.tube A.price b (V' x)
variable (D:ℝ)(O:ChartRatio G)
-- on all punctured curve. Effective perturbation on the truncated full-regulator integral is WHOLE shift. Budget-small by the extra positive weight; no analytic claim about its (possibly huge) offmask unscaled values.
abbrev shadeP (i:Config G A.f) := -A.beta * Q.shift d i
abbrev answer:= A.uncloud+shadeP A Q
abbrev fullVoice (x:X)(U:A.forest.Slice G):= Z x U * Real.exp (answer A Q ((F).drape U))
abbrev phrase (x:X)(U:A.forest.Slice G):= A.newZ x U * Real.exp (shadeP A Q ((F).drape U))
-- KEEP exact unnormalized real VAC and all tag. If later using mixed estimate, can identify
-- Aperture true sum directly with push of MARK coefficients through comparison of polynomials.
abbrev aisle (x:X):=∫ i, phrase A Q x i ∂ A.forest.order G
abbrev neckHeat (x:A.X):=∫ y in Metric.closedBall (0:Body A.Vx) (A.wD D), unroll (A:=A.Ph) (B:=A.Bank O) (M:=A.Zc) (ρ:=A.Mh) (V:=Q.roofP A) (W:=A.Θ⁻¹ • x) y A.Θ ∂μ
lemma folding (hO:LocalRatio O)(z:Y)(x:A.X): - (climb2 (plunge (Aperture.Phase.roofP A Q) (A.Θ⁻¹ • x) z (ρ:=A.Mh)) A.Θ)= Aperture.Phase.answer A Q ((F).drape (A.dockP x z)):=by
 let u:= plunge (Aperture.Phase.roofP A Q) (A.Θ⁻¹ • x) z (ρ:=A.Mh); let U:= (F).drape (A.dockP x z)
 have hr:0<A.Θ:= A.Θp; have he:= Catch.sign (Aperture.Phase.roofP A Q) (A.Θ⁻¹ • x) (A.soft O hO) (raised A Q) z
 have hG:= Laplace.SigmaP.shift_two («F»:=u) he.1 he.2.1 A.Θ; have hx:u A.Θ=(∑ i∈ξ,A.Θ^i.stamp*A.fi i U)+Q.shift d U:= by unfold u Catch.plunge uplift; simp_rw [course,smul_inv_smul₀ hr.ne']; exact congr_arg₂ (·+·) (A.clouds (A.Mh x+A.Θ • z) x) rfl -- z or Z y'= A.Mh x + g z
 change -(climb2 u A.Θ)= -A.beta* _ + -A.beta * Q.shift d U; erw [← mul_add, ←hx,hG]; have hK:= Fare.gS _ A.bpos|>.2; rw [← mul_assoc,neg_mul,mul_comm A.beta,hK]; ring
lemma hearing : RG.Envelope (shadeP A Q):= (RG.Envelope.const _).mul (Q.paid _)
variable (x':A.X){s:Age→ℝ}
lemma invest (i:A.forest.Slice G) : fullVoice A Q x' i= A.tallZ x' i * Real.exp (shadeP A Q ((F).drape i)):= by unfold fullVoice Aux.Name.tallZ answer; rw [Pi.add_apply,Real.exp_add]; ring
lemma capital (h:A.Civil s) : RG.Envelope (fullVoice A Q x'):= by rw [show fullVoice A Q x'= _ from funext (invest A Q x')]; exact (A.tilt_record h x').2.2.1.mul (Env.along (hearing A Q|>.exp) (A.forest.continuous_drape.measurable))
lemma starch (h:A.Civil s) : RG.Envelope (phrase A Q x'):= (A.tilt_record h x').2.1.mul (Env.along (hearing A Q|>.exp) (A.forest.continuous_drape.measurable))
local notation "k'"=> A.choices
variable {hScope:Age→ℝ}(h:A.Civil hScope){D O}{q x₀:A.X}(hO:LocalRatio O)(hD:Name.goods A O D C x₀)(hq:‖q‖ < eaves G P.L A.whenP)(ht: ‖q-x₀‖ ≤ furl G P.L A.whenP)
include hD hq ht hO
-- compare by staying transformation.Z includes real.
include h
lemma stance : (∫ U in A.stayingN D q,fullVoice A Q q U ∂A.forest.order G) =A.scaleO O q * (neckHeat A Q D O q):=by
 obtain ⟨⟨he,hv,hg,hV⟩,h'⟩:=hD; let u:= q; let X':= A.Mh q; let W:= fullVoice A Q q; let D':= A.wD D; let hμ z (hz:‖(z:Y)‖≤D'):= h' q hq ht z hz
 let M z:= unroll (A:=A.Ph) (B:=A.Bank O) (M:=A.Zc) (ρ:=A.Mh) (V:=Aperture.Phase.roofP A Q) (W:=A.tulip q) z d; let Y':= Metric.closedBall (0:Y) D'
 unfold stayingN; rw [cubits F O X' _ _ _ W A.Θp hO (fun z h=> (hμ z h).2.1) ((capital A Q q h).meas.stronglyMeasurable), ← MeasureTheory.integral_const_mul] -- maybe W abbreviation def reducibility
 have hh : (∫ z in Y', M z ∂μ)=∫ z in Y',Shield.lens₀ ((A.Zc 0)⁻¹) z*M z := by
    have ht:= Shield.recommends _ ((A.soft O hO).station.self_of_nhds.1.inv) (Y'.indicator M); let hx:MeasurableSet Y':=measurableSet_closedBall; rw [← integral_indicator hx, ← integral_indicator hx]; apply ht.trans; apply integral_congr_ae; filter_upwards with z; by_cases hp:z∈Y' <;> simp [hp]
 rw [show neckHeat _ _ _ _ _= _ from hh,← integral_const_mul]; apply setIntegral_congr_fun measurableSet_closedBall; intro z hz
 let hS := reserves F A.tube O k' A.σ A.price b D' he A.bpos hv A.loom.large.1 hq (fun i hi=> (hμ i hi).2.2) hO (fun i hi=> (hμ i hi).2.1) (fun i hi=>(hμ i hi).1) z hz
 let u' := answer A Q ((F).drape (A.dockP q z)); let v' := grace A.Ph (A.Bank O) A.Mh A.Zc z (d,q)
 have hw : M z= Real.exp v' * Real.exp u' := by
    unfold M unroll; simp only [Function.comp_apply]; unfold warmP; rw [course]; -- syntax
    change Real.exp (_ - _) = _; simp_rw [tulip, smul_inv_smul₀ A.Θp.ne']; rw [sub_eq_add_neg, folding A Q O hO z q, Real.exp_add]
 dsimp only; rw [hw]; let a:=windmill F (X'+d • z); let v₂:=A.dockP q z; let Y₀:= Fintype.card (A.Vx); let J := Shield.lens₀ (A.Zc 0)⁻¹ z
 change d ^ Y₀ * (Next.SectorChange.pay O a*(Z q v₂*Real.exp u'))= A.scaleO O q*(J*(Real.exp v'*Real.exp u'))
 change d^Y₀* (Next.SectorChange.pay O a * Z q v₂)= A.scaleO O q*(J*Real.exp v') at hS
 rw [← mul_assoc (Next.SectorChange.pay O a), ← mul_assoc, hS]; ring
end Phase
end YM.QuadraticLocal.Aperture

