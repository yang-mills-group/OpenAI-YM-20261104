import YM.AllOrder.Docket.Mint
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Aux
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open PertExtension.Series Laplace Laplace.SigmaP Response Laurent Stationary
open PositionX.Jet Extra.Iteration Floe Floe.Pace Floe.Aero Floe.StateE
open Catch Catch.Clock Sienna 
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G:Gauge} {L n f: Side}{ι:Type*}{T:Catch.Clock ι} {W b D α a B C Ω κ V:ℝ}{k p M:ℕ}
variable {P:Patch}{K:KernelChoices}{S : StepData n f} {s:Teller G}{η : Stage}
open Metric ConnectedActivityE6.Coat
namespace Name
variable {r:Stage}{j:ℕ}{u:ℝ→ℝ} {t w x:ℕ}{U:Push.Uniform.Before G r.width r.paths P.J K (k+3)}
variable (A: Aux.Name G P K u x r k U)
local notation "I"=>Aux.Name G P K u x r k U
local notation "ξ"=> Aux.scope x
local notation "b"=> A.beta
local notation "d"=> A.Θ
local notation "Θ"=> A.price.threshold
open Till Tilt Lantern
local notation "F"=> A.Fs
local notation "X"=> A.X
local notation "Y"=> Body A.Vx
variable (D:ℝ)(O:ChartRatio G)
local notation "μ"=> Poll.sweep (A.Zc 0)⁻¹
local notation "FS"=> A.forest.Slice G
local notation "V'"=> Desk.night
abbrev stayingN (x:A.X):= staying A.Fs (A.Mh x) A.Θ (A.wD D) (V' x)
abbrev scaleO (x:A.X):= (A.overhead O)* Real.exp (-A.tenses O x)
abbrev goods (D C:ℝ)(x:A.X): Prop := let D':= A.wD D; let u:= Name.Omega A; Sienna.Dayroom A.tube A.ν A.price A.forest A.σ A.choices P.L O D C A.whenP A.beta x
local notation "Z"=> fun x=> overall F A.tube A.price b (V' x)
variable (x':X)
abbrev newZ (x:X): A.forest.Slice G→ ℝ:= fun U=> Z x U * Real.exp (A.view (A.Fs.drape U))
abbrev tallZ (x:X): A.forest.Slice G→ ℝ := fun U=> Z x U *Real.exp (A.uncloud (A.Fs.drape U))
abbrev dockP (x:X): Y→A.forest.Slice G:= fun y=> draw F (V' x) (A.Mh x +A.Θ • y)
abbrev neck (x:A.X):=∫ y in Metric.closedBall (0:Body A.Vx) (A.wD D), unroll (A:=A.Ph) (B:=A.Bank O) (M:=A.Zc) (ρ:=A.Mh) (V:=A.Qc) (W:=A.Θ⁻¹ • x) y A.Θ ∂μ
local notation "k'"=> A.choices
local notation "t"=> A.whenP
local notation "S'"=> stayingN A D
-- Formal identity value for extra PURE-chart.Bld.Momentum.
lemma clouds (z:Y)(w:A.X) : A.Qc (A.Θ,w,z) = ∑ i∈ξ,A.Θ^i.stamp*A.fi i (A.Fs.drape (draw F (V' w) z)) := by unfold Qc venue; rw [Finset.sum_apply]; rfl
lemma curved (hO:LocalRatio O)(z:Y)(x:A.X) : - (climb2 (plunge (A.Qc) (A.Θ⁻¹ • x) z (ρ:=A.Mh)) A.Θ)= A.uncloud (A.Fs.drape (A.dockP x z)):= by
 let u:= plunge A.Qc (A.Θ⁻¹ • x) z (ρ:=A.Mh); -- need hO any; `Accent_*`, use `Sign` because value exponent all orders
 have hr:0<A.Θ:= A.Θp
 have he:= sign (A.Qc) (A.Θ⁻¹ • x) (A.soft O hO) (A.rise) z
 have hG:= Laplace.SigmaP.shift_two («F»:=u) he.1 he.2.1 A.Θ; have hx:u A.Θ=∑ i∈ξ,A.Θ^i.stamp*A.fi i (A.Fs.drape (A.dockP x z)):= by unfold u Catch.plunge uplift; simp_rw [course,smul_inv_smul₀ hr.ne']; exact clouds A _ _
 change -(climb2 u A.Θ)=_; unfold uncloud; rw [← hx,hG]; have hK:= Fare.gS _ A.bpos|>.2; rw [← mul_assoc]; simp only [neg_mul] ; rw [mul_comm b,hK]; ring -- syntax
variable {s:Age→ℝ}(h:A.Civil s)
include h
lemma tilt_record (x:X): (∀ i:A.forest.Slice G,0≤A.newZ x i ∧ 0 ≤ Z x i) ∧ RG.Envelope (A.newZ x)∧ RG.Envelope (A.tallZ x) ∧ A.attends x=∫ i,A.newZ x i ∂ A.forest.order G := by
 obtain ⟨P,hP,hU⟩:=h.price; have he := A.loom.large.1; have hr:= A.tilt.envelope hU.cap; have hp:= amt F A.tube A.price b t P hP (V' x)
 have hG i : Z x i * Real.exp (A.view ((F).drape i))= A.data.density b ((F).drape i) (V' x)* A.tilt.eval ((F).drape i):= by rw [A.tilt_eq ((F).drape i), ← mul_assoc]; exact congr_arg (· * _) (Fare.total ..); -- dot
 let a (k:A.data.Choices)i:= taggedKernel A.data b k ((F).drape i) (V' x)* A.tilt.eval ((F).drape i); have ha : (A.newZ x)=fun i=>∑ k, a k i:= by ext1 v; change Z x v * _=_; rw [hG]; exact Finset.sum_mul ..
 have hx : ∀ i:A.forest.Slice G, 0 ≤ Z x i:= fun i=> Fare.rays F A.tube A.price b i x; refine ⟨fun i=> ⟨mul_nonneg (hx i) (Real.exp_pos _).le,hx i⟩,?_,hp.1.mul (Env.along A.upEnv (F).continuous_drape.measurable),?_⟩
 · rw [ha]; exact RG.Envelope.sum _ _ (fun i=> (env_tagged _ _ he (F).continuous_drape.measurable measurable_const).mul (Env.along hr (F).continuous_drape.measurable))
 unfold attends; rw [(F).pushing (A.data.isKernel he b) _ (V' x) (Presented.lawful_gi hU.cap) (hr.integrable _) (fun k U=> A.data.covary he k b U (V' x))]; apply integral_congr_ae; filter_upwards with i using (hG i).symm
variable {D O}{q x₀:A.X}(hO:LocalRatio O)(hD:Name.goods A O D C x₀)(hq:‖q‖ < eaves G P.L A.whenP)(ht: ‖q-x₀‖ ≤ furl G P.L A.whenP)
include hD hq ht hO
-- compare by staying transformation.Z includes real.
lemma stay_eq : (∫ U in A.stayingN D q,A.tallZ q U ∂A.forest.order G) =A.scaleO O q * (A.neck D O q):=by
 obtain ⟨⟨he,hv,hg,hV⟩,h'⟩:=hD; let u:= q; let X':= A.Mh q; let W:= A.tallZ q; let D':= A.wD D; let hμ z (hz:‖(z:Y)‖≤D'):= h' q hq ht z hz
 let M z:= unroll (A:=A.Ph) (B:=A.Bank O) (M:=A.Zc) (ρ:=A.Mh) (V:=A.Qc) (W:=A.tulip q) z d; let Y':= Metric.closedBall (0:Y) D'
 unfold stayingN; rw [cubits F O X' _ _ _ W A.Θp hO (fun z h=> (hμ z h).2.1) ((A.tilt_record h q).2.2.1.meas.stronglyMeasurable), ← MeasureTheory.integral_const_mul] -- maybe W abbreviation def reducibility
 have hh : (∫ z in Y', M z ∂μ)=∫ z in Y',Shield.lens₀ ((A.Zc 0)⁻¹) z*M z := by
    have ht:= Shield.recommends _ ((A.soft O hO).station.self_of_nhds.1.inv) (Y'.indicator M); let hx:MeasurableSet Y':=measurableSet_closedBall; rw [← integral_indicator hx, ← integral_indicator hx]; apply ht.trans; apply integral_congr_ae; filter_upwards with z; by_cases hp:z∈Y' <;> simp [hp]
 rw [show neck _ _ _ _= _ from hh,← integral_const_mul]; apply setIntegral_congr_fun measurableSet_closedBall; intro z hz
 let hS := reserves F A.tube O k' A.σ A.price b D' he A.bpos hv A.loom.large.1 hq (fun i hi=> (hμ i hi).2.2) hO (fun i hi=> (hμ i hi).2.1) (fun i hi=>(hμ i hi).1) z hz
 let u' := A.uncloud ((F).drape (A.dockP q z)); let v' := grace A.Ph (A.Bank O) A.Mh A.Zc z (d,q)
 have hw : M z= Real.exp v' * Real.exp u' := by
    unfold M unroll; simp only [Function.comp_apply]; unfold warmP; rw [course]; -- syntax
    change Real.exp (_ - _) = _; simp_rw [tulip, smul_inv_smul₀ A.Θp.ne']; rw [sub_eq_add_neg, A.curved O hO z q, Real.exp_add]
 dsimp only; rw [hw]; let a:=windmill F (X'+d • z); let v₂:=A.dockP q z; let Y₀:= Fintype.card (A.Vx); let J := Shield.lens₀ (A.Zc 0)⁻¹ z
 change d ^ Y₀ * (Next.SectorChange.pay O a*(Z q v₂*Real.exp u'))= A.scaleO O q*(J*(Real.exp v'*Real.exp u'))
 change d^Y₀* (Next.SectorChange.pay O a * Z q v₂)= A.scaleO O q*(J*Real.exp v') at hS
 rw [← mul_assoc (Next.SectorChange.pay O a), ← mul_assoc, hS]; ring
end Name
end YM.AllOrder.Aux
