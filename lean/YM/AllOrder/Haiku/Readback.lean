import YM.AllOrder.Laplace.Dale
import YM.AllOrder.Haiku.Tornado
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Kinetic.Port
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace Laplace.SigmaP Ker Ker.Start
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response Ink Ink.Method Ink.Money GaussianScore Module
open Tree Wilson PhysicalNext Repeat Lapis ConnectedActivityE6 Blaze Precision Push Pressure Next.Fluctuations Next.SectorChange MeasureTheory
open Further.PhysicalPeriodLimitF933
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
open AllOrder.Haiku AllOrder.Haiku.Coat
variable (P:Patch)(K:KernelChoices){G:Gauge}{c f:Side}{S:StepData c f}{a C Λ:ℝ}{k N:ℕ} {ι:Type} [Nonempty ι]
variable (O:ChartRatio G)(T:Tube G S) {F: Forest S.ratio} (θ:S.Choices) (ρ: Bid.Dir G c→AxisChart G F)(γ:ℝ)
local notation "L"=> Coarse G
variable (Q:Push.Uniform.Before G a C S.patch.J S.kernel (N+3))(hF:Bid.Larger (G:=G) S)(hO:LocalRatio O)(h:T.up.Bounds T.high a C Λ)(hr:Q.Service F T.high T.up ρ)(hh:ClassicalMatch F T.high T.low T.up T.down ρ) {t p r:ℝ}(ht:FiniteBound F T.up T.down T.high T.low γ O ρ t p r)
local notation "Z"=> Positions (Uniform.Primary c G)
local notation "Ψ"=> Precision.thermal F θ T.high T.up ρ O
local notation "W"=> T.down
local notation "D"=> T.low
local notation "Q'"=> draft γ T.down T.low («c»:=c) -- check
set_option quotPrecheck false
local notation "B"=> startup F O θ T.up T.high Q hF h hr hO
local notation "A"=> ratePlan B

lemma portrait (x:Stationary.Link G c): Stationary.arm G c 1 x=tint G _ (exteriorL G c x):= rfl

include hF h hr hO hh ht
abbrev board (k:ℕ) (x : Stationary.Link G c):= Local.Pure.flip F T O ρ θ k (exteriorL G c x)+ Coat.Stipend T.low T.down γ k c x
abbrev subtractΨ:= Precision.thermal F θ T.high T.up ρ O-draft (c:=c) γ T.down T.low
lemma lighter (u : Stationary.Link G c) {k:ℕ}(hk:k≤2): Coat.Stipend T.low T.down γ k c u= jet (Local.Pure.hard F T ρ θ) (k+2) (exteriorL G c u)+ jet (draft (c:=c) γ T.down T.low) k (Stationary.arm G c 1 u):= by
 let L':=(tint G (Exterior.Body 1 c)).toContinuousLinearMap; let y:= Stationary.arm G c 1 u; let M:(Bid.Dir G c) →ℝ := mainTerm D W ∘ represent; let K':= (Stationary.arm G c 1).toContinuousLinearMap; let x' := exteriorL G c u; have hp := hh (k+2) (by omega) θ
 rw [intent_match O T F θ Q h hF hr hO hh _ (by omega)]; change jet (M ∘ K') (k+2) u+ jet ((Q')∘ K') k u= jet (M ∘ L') _ x'+jet (Q') k y
 rw [Kinetic.pivot K' M _ hp.2.1,Kinetic.pivot L' M _ hp.2.1, Kinetic.pivot K' _ _ ht.classicalResult]; rfl
lemma annual {k:ℕ}(hk:k≤2)(x y:Stationary.Link G c): let H:= subtractΨ O T θ ρ γ; board O T θ ρ γ k x-board O T θ ρ γ k y = jet H k (Stationary.arm G c 1 y)-jet H k (Stationary.arm G c 1 x):= by
 let A' := Ψ; intro W'; let H0:= Q';
 let m(z:Stationary.Link G c):= (exteriorL G c z)
 let S' := Local.Pure.soft F T O ρ θ; have h₀ : W'= A' - H0:=rfl
 let v:=Lantern.shade (gram F T.up T.high ρ θ) 0; let u : Z→L[ℝ] (Bid.Dir G c) := (tint G _).toContinuousLinearMap
 have hs(z: Z): jet S' k z = jet Ψ k (u z) -jet (fun (_:Z)=>v) k z:= by
    have he:= soft_ball O T F θ Q h hF hr hO; let w:= Ψ; have h': ContDiffAt ℝ (↑k) (Ψ∘tint G _) 0:= ContDiffAt.comp _ ((map_zero u).symm ▸ ((ht.born θ).of_le le_top)) u.contDiff.contDiffAt
    rw [←Kinetic.pivot u w _ (ht.born θ) k]; unfold jet; rw [(he.iteratedFDeriv ℝ k).self_of_nhds,iteratedFDeriv_sub_apply h' contDiffAt_const,_root_.sub_apply,mul_sub]; rfl -- ambiguous tilt
 let f(z:Z):=jet (fun (_:Z)=> v) k z; have hκ: f (m x)= f (m y):= by
    by_cases hv:k=0; · simp [f,hv]
    unfold f jet; simp [iteratedFDeriv_const_of_ne hv]
 unfold board; rw [lighter O T θ ρ γ Q hF hO h hr hh ht x hk,lighter O T θ ρ γ Q hF hO h hr hh ht y hk]
 let g:=jet (Local.Pure.hard F T ρ θ) (k+2); let G'(z:Z):= jet (Real.log ∘ Local.Vote.aggregation (table F θ T.up T.high) (mist F O T.up) (orbit F ρ) (gram F T.up T.high ρ θ) k) k (1,z); have he(z:Stationary.Link G c) : Local.Pure.flip F T O ρ θ k (exteriorL G c z) + (jet (Local.Pure.hard F T ρ θ) (k+2) (exteriorL G c z)+ jet (draft (c:=c) γ T.down T.low) k (Stationary.arm G c 1 z)) = f (m z) + G' 0 - jet W' k (u (m z)):= by
    have hQ : G' (m z)= G' 0:= first_vote O T F θ Q h hF hr hO (m z) 1 hk
    have hV : jet W' k (u (m z))= jet A' k (u (m z))-jet H0 k (u (m z)) := by unfold jet; rw [h₀,iteratedFDeriv_sub_apply (show ContDiffAt ℝ k A' 0 from (ht.born θ).of_le le_top) (show ContDiffAt ℝ k H0 0 from ht.classicalResult.of_le le_top),_root_.sub_apply, mul_sub]
    change -g (m z)-jet S' k (m z)+ G' (m z)+(g (m z)+jet H0 k (u (m z)))= _; rw [hQ,hV,hs]; change -_-(jet A' k (u (m z))- f (m z))+_+_=_; abel
 rw [he,he,hκ]; change _-_ - (_- jet _ _ (u (m y))) = jet _ _ (u (m y))-jet _ _ (u (m x)); abel
end YM.AllOrder.Kinetic.Port
