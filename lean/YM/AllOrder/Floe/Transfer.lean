import YM.AllOrder.Floe.Drizzle
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Floe
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G: Gauge} {c f n : Side} {k j w N : ℕ} {S:StepData c f}
variable {σ C Z D β Θ:ℝ}
open Bloch Exterior Bid Next.Fluctuations
section link
variable {F:Forest S.ratio}{R:PathData G}{p:Clip} {t:S.Choices}{ρ:Bid.Dir G c→ AxisChart G F}(Y:Finset Age)(i:Age) (P:Layout G)
local notation "X"=> Apex c G
local notation "O₁"=> Poll.Body (Precision.Key F G)
local notation "L"=> Kinetic.Port.exteriorL G c
open Kinetic.Port
-- Reader identity is framed only. When changing x across periods ensure lifts with same ℒ.L
local notation "U"=> (Towers S.patch.L)
def Mentor (u₀ u: ℕ→Atom G k) : Prop:= SameJet k (fun y=>Extra.Iteration.action u₀ (Extra.Iteration.liftedTo F ρ y)) (fun y=>Extra.Iteration.action u (represent y))
variable {N:ChartRatio G}{B:ℝ→ Config G f→ℝ}
variable (D:Laplace.Desk F N B t)(hD:D.quiet=Lapis.orbit F ρ)
variable (h:Legal Y P)(hi:i∈Y)
include hD h hi
lemma tariff_match {g: ℕ→ Atom G i.r}(hg: Mentor (F:=F) (ρ:=ρ) (P i) g)(x:Stationary.Link G c):
   note_n (i:=i) F P D i.e (L x,0)= jet (turnSeries (m:=c) g) i.r x:= by
 let H:= D.hard; let σ:=D.quiet; let C': X→L[ℝ] X×O₁:= (ContinuousLinearMap.id ℝ X).prod (fderiv ℝ σ 0)
 let f:=far F P i; have hf:=far_capsule F P Y h hi; let T: X→X×O₁:=fun z=>(z,σ z); have hV:T 0=0:= Prod.ext rfl D.pay.steer.map0; have hp: ContDiffAt ℝ ω T 0:= contDiffAt_id.prodMk D.pay.steer.shape
 have hp':fderiv ℝ T 0=C':= ((hasFDerivAt_id _).prodMk (D.pay.steer.shape.differentiableAt (by simp)).hasFDerivAt).fderiv;
 let g₀ := Extra.Iteration.action (n:=c) g ∘ represent; let f₁ : Bid.Dir G c→ ℝ:= Extra.Iteration.action (P i) ∘ Extra.Iteration.liftedTo F ρ; let L₀:= (Uniform.tint G (Exterior.Body 1 c)).toContinuousLinearMap
 have he : f∘T=f₁ ∘ L₀:=by unfold f far T σ f₁; rw [hD]; rfl
 have hh : iteratedFDeriv ℝ i.r (f ∘ C') 0= iteratedFDeriv ℝ i.r (g₀ ∘ L₀) 0:= by
     have ht:= Jets.tangent (f:=f) (hf.1.of_le le_top) (hp.of_le le_top) hV hf.2 i.r (le_refl _); rw [hp',he] at ht; rw [← ht,Next.Foundations.jets_linear (f:=f₁) L₀ ((show ContDiffAt ℝ ω f₁ 0 from hg.1).of_le le_top),Next.Foundations.jets_linear (f:=g₀) L₀ ((show ContDiffAt ℝ ω g₀ 0 from hg.2.1).of_le le_top)]; rw [show iteratedFDeriv ℝ i.r f₁ 0=iteratedFDeriv ℝ i.r g₀ 0 from hg.2.2]
 rw [lush F P Y D h hi (le_refl i.e),Nat.sub_self,Nat.zero_add]; let x':= L x
 have H' : jet (turnSeries (m:=c) g) i.r x=jet (g₀ ∘ L₀) i.r x':= Kinetic.pivot ((L).toContinuousLinearMap) (g₀ ∘ L₀) x (((L₀.map_zero).symm ▸ (show ContDiffAt ℝ ω g₀ 0 from hg.2.1)).comp (f:=L₀) _ L₀.contDiff.contDiffAt) _ -- `map_zero`?
 rw [H']; change jet f i.r (goldL F (fderiv ℝ σ 0) (x',0))=_; rw [show (goldL F _ (x',0)) = C' x' from (show (goldL F (fderiv ℝ σ 0) (x',0))= C' x' from Prod.ext rfl (add_zero _)),← Kinetic.pivot C' f x' (show ContDiffAt ℝ ω f 0 from hf.1),Radial.jet, hh]; rfl
end link
end YM.AllOrder.Floe
