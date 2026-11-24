import YM.Qlocal.BindPulse
import YM.AllOrder.Wheel.Roll
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Binding
open Function Filter Lattice RG Wilson Tree Precision Input Gauge Finset MeasureTheory
open Push Push.Uniform SectorMeasure PhysicalNext Repeat Lapis
open ConnectedActivityE6 Blaze Brush Next.SectorChange Laurent Exterior Org
open Work.F03 Work.F05
open Marker Multi Comparison.RG02.Order
open AllOrder AllOrder.Floe Laplace Response Ink
open PertExtension.Series Radial PositionX.Jet PositionX.Gauss Extra.Iteration
open Comparison.RG02.Assembly Comparison.RG02.Bulk
open scoped BigOperators Topology ENNReal Classical InnerProductSpace MatrixOrder ContDiff Matrix.Norms.Frobenius
variable {G: Gauge} {c f n: Side} {S:StepData c f} {k t j:ℕ}
    {V:Type} [DecidableEq V] {B:Census V}
open Primitives.TwoWave Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open AllOrder Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money
open Work.G05 Kinetic.Port
local notation "E"=> Apex c G
section prefixL
variable {F:Forest S.ratio}{T:S.Choices}{O:ChartRatio G}{B0:ℝ→ Config G f→ℝ} (D:Desk F O B0 T)
lemma dawnP : preview D = ratePlan D 0 0:=by
 have hz : distilled D 0=0:= Fire.fades (toward volume (win0 _)); unfold ratePlan; rw [Pi.add_apply, Pi.add_apply, hz]; change _= preview D - liftQ _ _ _ + 0; rw [add_zero,liftQ,_root_.map_zero, Laplace.curvature,show Radial.jet _ 2 _ = 0 from ?_]; · ring
 exact Comparison.RG02.Assembly.Clipper.empty 2 (by decide) _
lemma jury (x:Apex c G) (k:ℕ): distilled D k x - (if k=0 then liftQ D.hard (fderiv ℝ D.quiet 0) x else 0) = ratePlan D k x - PositionX.Jet.just (preview D) k:= by
 by_cases hk:k=0
 · subst k; rw [if_pos rfl]; change _-_= (preview D- liftQ _ _ _ + _)-preview D; abel
 unfold ratePlan; rw [if_neg hk,Pi.add_apply,Pi.add_apply]; change _-_= PositionX.Jet.just _ k+_-_; simp [PositionX.Jet.just,hk]
end prefixL
open Kinetic
section prePhase
variable (P:Patch)(K:KernelChoices){a C:ℝ}{N:ℕ}
variable {ι:Type} [Nonempty ι] (p:Clip) (O:ChartRatio G)(x:ι→PathData G)(L:ι→ℝ)(Q:Push.Uniform.Before G a C P.J K (N+3))
    (hx:∀ i,(x i).Bounds p a C (L i))(hO:LocalRatio O)(F:ι→ candidates P K G)(h:proofC P K p x Q F)
    (X:ι→Layout G)(U:Finset Age) (hV:∀ i,Legal U (X i)) (i:ι)
local notation "Ψ"=> prePhase P K p O x L Q hx hO F h X U hV
local notation "T'"=> trees P K c
local notation "S₀"=> dock P K c
variable (F' : Forest S.ratio)(t':S.Choices) {R:PathData G}{p':Clip}(A:Comparison.RG02.Bulk.Kernel S p' R O)
    [Fintype V] (W:Colors B G f) (hs:W.vac=drawn (X i) U f) (j r:ℕ) (hk:j≤r)(hS: S.patch=P)(hK:S.kernel=K)(hr:R=x i)(hl:p'=p)(hf:Bid.Larger (G:=G) S)
local notation "Y"=> rule (Coarse G) c
include hs hk hS hK hr hl hf
/-- Frame at STEP, no unstated projection to zero average. Any forest & tag in Datum; compare
  charged Exponent in Book theorem then pull. -/
def flatK {F' : Forest S.ratio} {O:ChartRatio G} {p:Clip}{R:PathData G} (A: Comparison.RG02.Bulk.Kernel S p R O)(t': S.Choices)(W:Colors B G f)(j r:ℕ) (y:rule (Coarse G) c): ℂ:= Comparison.RG02.Symmetry.Orbit.ground A F' t' W r j (tint G _ (Kinetic.Port.exteriorL G c y))
lemma clock (y:Y) : ↑(Ψ i j c y) = flatK (F':=F') A t' W j r y:= by
 subst R p'; have ht: f=below P c:=Subtype.ext (by change f.val=(below P c).val; rw [S.sizes,hS]; rfl); subst f; have hZ:S=dock P K c:= by cases S with | mk x y=> dsimp only at hS hK; subst P K; rfl
 subst S
 obtain ⟨σ,hσ⟩:= Q.graph (p:=p) F' (hx i) hf (by rfl) (by rfl)
 let D₀:= Laplace.startup T' O (label (S₀)) (x i) p Q hf (hx i) (h i c hf) hO; let D:= Laplace.startup F' O t' (x i) p Q hf (hx i) hσ hO; let P₀:= augment T' (X i) U D₀ (hV i); let P1:= augment F' (X i) U D (hV i); have hP : ratePlan P1=ratePlan P₀:= Response.exactly P1 P₀ (mul_pos (pow_pos hO.scale _) (Real.exp_pos _)) hO A.branches (fun b=> orchestra (x i) p (X i) U (hV i) b (hx i)) (mul_pos (pow_pos hO.scale _) (Real.exp_pos _))
 let z:= exteriorL G c y; rw [flatK,action F' t' (X i) U A W (hV i) hs Q σ (hx i) hf hσ z r j hk]; change _= Complex.ofReal (distilled P1 j z - if j=0 then liftQ P1.hard (fderiv ℝ P1.quiet 0) z else 0); rw [jury P1 z j,dawnP] -- remove P1
 rw [hP, ← dawnP]; have he : ratePlan P₀ j z= PositionX.Jet.just (preview P₀) j+ (Ψ i j c y):= precise_top P K p O x L Q hx hO F h X U hV i c hf y j; rw [he]; congr 1; abel
end prePhase
end YM.Qlocal.Binding
