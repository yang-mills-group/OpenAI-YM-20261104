import YM.OPE.Compatible.Glim.Zone
import YM.OPE.Compatible.Javelin.Bulls
/-! # IBP one limb of any stand. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion
open Flock Libra.Shell
variable {I:Type}[Fintype I](p:I)(a:G.Color)(b:Bool)
local notation "E!"=> Keys G I
abbrev Awake := EuclideanSpace.basisFun G.ColorIndex ℝ
noncomputable abbrev Phone (G:Gauge):Module.Basis G.ColorIndex ℝ G.Color:= (Awake (G:=G)).toBasis -- ortho basis
noncomputable abbrev Mount (i:G.ColorIndex): ScriptJ (Keys G I) := Pawn.mold (tou p (Phone G) b a i) 0
noncomputable abbrev Topper (f:ScriptJ E!): ScriptJ E!:= Flux (An p (Phone G)) (Mount p a b) univ f
noncomputable abbrev LoopM (F X r:ScriptJ E!): ScriptJ E!:= Stamp (An p (Phone G)) (Mount p a b) univ (F+X) r
variable (L:Lid G I)(W:Libra.Keys G I→ℝ)
open Glass
lemma marrow (hr:LocalRatio P)(h:L.w=ᶠ[𝓝 0] (Real.exp ∘ fun x=>-W x))(hp:ContDiffAt ℝ ω W 0) (f y:ScriptJ E!)(hf:f.B)(hy:y.B):
     L.pay P (LoopM p a b (Pawn.mold L.f 2) (Pawn.mold W 0) f*y)=L.pay P (f* Topper p a b y):=by
       let μ:=Chart.tangent G I; let T:=penon L; let M:=Mount p a b; let U:=An p (Phone G); let J:=Chart.jacobian P (U:=I); let C:=plainJ (L.seedPrice P)⁻¹
       have hz: divergence U M univ* Pawn.mold J 0+Flux U M univ (Pawn.mold J 0)=0:= prio U (tou p (Phone G) b a) univ J (Chart.Ratio.jacobian_smooth hr) (fun _ _=>CharterS p _ _ _ _) (winds' p hr a b (Phone G))
       let D:=(fun _:E!=>C)*Wax L.f W J; let q:=LoopM p a b (Pawn.mold L.f 2) (Pawn.mold W 0) f
       have ht:D=L.hat P:=by
            let g:=Real.exp ∘ fun x=>-W x
            have hv: ContDiffAt ℝ ω g 0:= hp.neg.exp
            have he: warmer P L.w=ᶠ[𝓝 0] g* J:= h.mul Filter.EventuallyEq.rfl
            funext z
            change D z=C * ((Pawn.mold (warmer P L.w) 0*_) z)
            rw [meltSame _ _ he, meltJ g _ hv (Chart.Ratio.jacobian_smooth hr),mul_comm (Pawn.mold g 0)];rfl
       have hV(p:ScriptJ E!):L.pay P p=fair μ T D p:=by rw [ht]; exact L.cutOut hr T p (penon_shape L)
       rw [hV,hV]; exact tokenOf T μ U M univ (fun i _=> tallJ _ _) L.f W J C hp (penon_shape L) hz f y hf hy
end YM.OPE.Variance
