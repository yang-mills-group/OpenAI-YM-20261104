import YM.QuadraticLocal.Aperture.Region
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
local notation "ℓ" => stayingN A D
local notation "Ψ"=> A.scaleO O
variable {s:Age→ℝ}(h:A.Civil s){q x₀:A.X}(hO:LocalRatio O)(hD:Name.goods A O D C x₀)(hq:‖q‖<eaves G P.L A.whenP)(he:‖q-x₀‖≤furl G P.L A.whenP)
include h hO hD hq he
lemma comparison (T₀:ℝ)(hW:∀ V:Config G A.f,flags A.price.threshold V=∅→ shadeP A Q V ≤ T₀) (a:ℝ)(hY:∀ V:Config G A.f,flags A.price.threshold V=∅→ |A.view V-A.uncloud V|≤ a ∧ |A.view V| ≤1): let q':= (aisle A Q q)/Ψ q; let η:= neckHeat A Q D O q
  Real.exp (-a)*η ≤ q' ∧ q' ≤ Real.exp a*η +Real.exp (1+T₀)*A.tired D:= by
 intro r η; let X':=ℓ q; let ν:= A.forest.order G; let k:= A.scaleO O q; let y:= phrase A Q q; let z:= fullVoice A Q q; let Y':= Z q;
 let hU':= (A.tilt_record h q).1; have hU i:0 ≤ y i:= mul_nonneg (hU' i|>.1) (Real.exp_pos _).le; let hV:= starch A Q q h; let hT:= capital A Q q h; let h₀:= stance A Q h hO hD hq he; obtain ⟨P,hP,hξ⟩:=h.price; let hx:= amt F A.tube A.price b A.whenP P hP (V' q)
 let E:= Real.exp (1+T₀); let q' i:= shadeP A Q (A.Fs.drape i); have hρ (i:A.forest.Slice G) : z i * Real.exp (-a) ≤ y i ∧ y i ≤ z i*Real.exp a ∧ y i ≤ Y' i *E:= by
    let f:= A.Fs.drape i; let a':=A.uncloud f+q' i; let v:=A.view f+ q' i; have he : y i=Y' i * Real.exp v:= by change Y' i*Real.exp _*Real.exp (q' i)=_; unfold v; rw [Real.exp_add, mul_assoc]
    rw [he]; change Y' i * Real.exp a' * _ ≤ _ ∧ Y' i*Real.exp v ≤ Y' i*Real.exp a'*Real.exp a ∧ _; by_cases hg:flags A.price.threshold f=∅; · obtain ⟨hY,hU'₁⟩:= hY f hg; have he: v-a'=A.view f-A.uncloud f:= (by unfold a' v; ring); rw [←he] at hY; have hh: -a≤v-a'∧ v-a'≤a:=abs_le.mp hY; let ht:= (hU' i|>.2); rw [mul_assoc,mul_assoc,← Real.exp_add,←Real.exp_add]; exact ⟨mul_le_mul_of_nonneg_left (Real.exp_monotone (by linarith only [hh.1] : a'+ -a ≤ v)) ht,mul_le_mul_of_nonneg_left (Real.exp_monotone (by linarith only [hh.2])) ht,mul_le_mul_of_nonneg_left (Real.exp_monotone (add_le_add ((le_abs_self _).trans hU'₁) (hW _ hg))) ht⟩
    have ht:Y' i=0:=by unfold Y'; dsimp only; rw [Fare.total,Pane.sparkling, if_neg hg,mul_zero]
    rw [ht]; simp
 let μ':=ν.restrict X'; let lχ:=ν.restrict X'ᶜ; let E':=∫ x,y x ∂μ'; let K':=∫ x,y x ∂lχ; have hp:0<k:=mul_pos (A.born O hO) (Real.exp_pos _); have hk:0≤K':=integral_nonneg (fun i=>hU i); let F':=∫ x, z x ∂μ'; let v:=Real.exp a; let a':=Real.exp (-a);
 have he0:a'*η*k ≤ E' := by rw [show a'*η*k= F'*a' from (by rw [show F'=k*η from h₀]; ring)]; unfold F'; rw [← integral_mul_const]; exact integral_mono (hT.integrable μ'|>.mul_const _) (hV.integrable μ') fun i=> (hρ i).1
 have he1: E' ≤ v*η*k:= by rw [show v*η*k= F'*v from (by rw [show F'=k*η from h₀]; ring)]; unfold F'; rw [← integral_mul_const]; exact integral_mono (hV.integrable μ') (hT.integrable μ'|>.mul_const _) fun i=>(hρ i).2.1
 have hy : aisle A Q q=E'+K':= (integral_add_compl (staying_meas ..) (hV.integrable ν)).symm; have hΦ:= accountability A D O h hO hD hq he; have hg:K' ≤ E*(k*A.tired D):= by
    let f':=∫ x,Y' x ∂lχ; have hs: K' ≤ f'*E:= by unfold f'; rw [← integral_mul_const]; exact integral_mono (hV.integrable _) (hx.1.integrable lχ|>.mul_const E) (fun i=> (hρ i).2.2)
    exact hs.trans ((mul_le_mul_of_nonneg_right hΦ (Real.exp_pos _).le).trans_eq (mul_comm ..))
 refine ⟨(le_div_iff₀ hp).2 (he0.trans ((le_add_of_nonneg_right hk).trans_eq hy.symm)),(div_le_iff₀ hp).2 ?_⟩; rw [hy]; linarith only [hg,he1] -- maybe let mismatch
end Phase
end YM.QuadraticLocal.Aperture
