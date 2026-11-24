import YM.AllOrder.Docket.Frost
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
local notation "V'"=> Desk.night
local notation "Fs"=> A.forest.Slice G
local notation "Z"=> fun x=> Fare.overall F A.tube A.price b (V' x)
local notation "t"=>A.whenP
local notation "ℓ"=> A.stayingN D
local notation "Ψ"=> A.scaleO O
variable {s:Age→ℝ}(h:A.Civil s) {q x₀:A.X}(hO:LocalRatio O)(hD:Name.goods A O D C x₀)(hq:‖q‖<eaves G P.L A.whenP)(he:‖q-x₀‖≤furl G P.L A.whenP)
include h hO
abbrev tired(D:ℝ)(A: I):= Real.exp (-(((U.tables r.clip P).gap)*((A.wD D)^2)/4)/2) -- shadow A
include he hD hq
lemma accountability : let Y₀:=ℓ q; (∫ i in Y₀ᶜ, Z q i ∂A.forest.order G) ≤ (Ψ q)*A.tired D:= by
 intro X'; obtain ⟨⟨h,hX,hB,hA⟩,hv⟩:= hD; obtain ⟨P,hP,hξ⟩:= (‹Civil A s›).price; let hm:= Fare.amt F A.tube A.price b t P hP (V' q); let Y':= Z q; let f:=∫ i in X'ᶜ,Y' i ∂ A.Fs.order G; let k:=A.choices; let a:= A.wD D
 let h' z (he':‖(z:Y)‖≤a):=hv q hq he z he'; let y₀:= ratify A.Ph (A.Bank O) A.Mh A.Zc a (A.Θ,q)
 have ht': Ψ q*y₀=∫ i in X', Z q i ∂ A.Fs.order G := Eq.symm (Fare.pricing F A.tube O k A.σ A.price b a h A.bpos hX A.loom.large.1 hq (fun i hi=> (h' i hi).2.2) hO (fun i hi=>(h' i hi).2.1) (fun i hi=> (h' i hi).1) hm.1.meas.stronglyMeasurable)
 have ht: A.data.push b A.virgin.eval (V' q) - Ψ q * y₀= ∫ i in X'ᶜ, Y' i ∂ A.Fs.order G:= by change _- _=_; rw [show A.data.push _ _ _= _ from hm.2, ht', ← integral_add_compl (staying_meas ..) (hm.1.integrable _),add_sub_cancel_left];
 change f≤ _; rw [← show _=f from ht]; refine (hA q hq he).2.trans_eq ?_; -- since notation f mismatch likely
 unfold tired; rw [← A.withGap]
lemma peris (a:ℝ)(hY:∀ V:Config G A.f,flags A.price.threshold V=∅→ |A.view V-A.uncloud V|≤ a ∧ |A.view V| ≤1): let q':= (A.attends q)/Ψ q; let η:= A.neck D O q
  Real.exp (-a)*η ≤ q' ∧ q' ≤ Real.exp a*η +Real.exp 1*A.tired D:= by
 intro r η; let X':=ℓ q; let ν:= A.forest.order G; let k:= A.scaleO O q; let y:= A.newZ q; let z:= A.tallZ q; let Y':= Z q;
 obtain ⟨hU,hV,hT,hC⟩:= tilt_record A h q; let h₀:= stay_eq A h hO hD hq he; obtain ⟨P,hP,hξ⟩:=h.price; let hx:= amt F A.tube A.price b t P hP (V' q)
 have hρ (i:A.forest.Slice G) : z i * Real.exp (-a) ≤ y i ∧ y i ≤ z i*Real.exp a ∧ y i ≤ Y' i *Real.exp 1:= by
    let f:= A.Fs.drape i; let a':=A.uncloud f; let v:=A.view f; by_cases H: flags A.price.threshold f=∅; · obtain ⟨hY,hU'⟩:= hY f H; have hh:-a≤ v-a' ∧ v-a'≤ a:= abs_le.mp hY; change |v|≤1 at hU'; change Y' i*Real.exp a'*Real.exp _ ≤ _ ∧ Y' i*Real.exp v≤Y' i*Real.exp a' *Real.exp a ∧ _; rw [mul_assoc,mul_assoc,← Real.exp_add,←Real.exp_add]; exact ⟨mul_le_mul_of_nonneg_left (Real.exp_monotone (by linarith only [hh.1] : a'+ -a ≤ v)) (hU i|>.2),mul_le_mul_of_nonneg_left (Real.exp_monotone (by linarith only [hh.2])) (hU i|>.2),mul_le_mul_of_nonneg_left (Real.exp_monotone ((le_abs_self _).trans hU')) (hU i|>.2) ⟩
    have ht:Y' i=0:=by unfold Y'; dsimp only; rw [Fare.total,Pane.sparkling, if_neg H,mul_zero]
    unfold z y tallZ newZ; change Y' i*_* _ ≤ Y' i* Real.exp v ∧ Y' i*Real.exp v≤Y' i*_*_∧Y' i*Real.exp v≤ _; rw [ht]; simp
 let μ:=ν.restrict X'; let lχ:=ν.restrict X'ᶜ; let E':=∫ x,y x ∂μ; let K':=∫ x,y x ∂lχ; have hp:0<k:=mul_pos (A.born O hO) (Real.exp_pos _); have hk:0≤K':=integral_nonneg (fun i=>(hU i).1); let F':=∫ x, z x ∂μ; let v:=Real.exp a; let a':=Real.exp (-a);
 have he0:a'*η*k ≤ E' := by rw [show a'*η*k= F'*a' from (by rw [show F'=k*η from h₀]; ring)]; unfold F'; rw [← integral_mul_const]; exact integral_mono (hT.integrable μ|>.mul_const _) (hV.integrable μ) fun i=> (hρ i).1
 have he1: E' ≤ v*η*k:= by rw [show v*η*k= F'*v from (by rw [show F'=k*η from h₀]; ring)]; unfold F'; rw [← integral_mul_const]; exact integral_mono (hV.integrable μ) (hT.integrable μ|>.mul_const _) fun i=>(hρ i).2.1
 let E:= Real.exp 1; have hy : A.attends q=E'+K':= hC.trans (integral_add_compl (staying_meas ..) (hV.integrable ν)).symm; have hΦ:= accountability A D O h hO hD hq he; have hg:K' ≤ E*(k*A.tired D):= by
    let f':=∫ x,Y' x ∂lχ; have hs: K' ≤ f'*E:= by unfold f'; rw [← integral_mul_const]; exact integral_mono (hV.integrable _) (hx.1.integrable lχ|>.mul_const E) (fun i=> (hρ i).2.2)
    exact hs.trans ((mul_le_mul_of_nonneg_right hΦ (Real.exp_pos _).le).trans_eq (mul_comm ..))
 refine ⟨(le_div_iff₀ hp).2 (he0.trans ((le_add_of_nonneg_right hk).trans_eq hy.symm)),(div_le_iff₀ hp).2 ?_⟩; rw [hy]; linarith only [hg,he1] -- maybe let mismatch
end Name
end YM.AllOrder.Aux
