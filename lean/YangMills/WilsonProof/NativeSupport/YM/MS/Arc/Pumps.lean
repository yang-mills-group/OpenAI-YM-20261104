import YM.MS.Arc.Pumps
import YangMills.WilsonProof.NativeSupport.YM.MS.Arc.Sky
/-!
# Dimensional scale-normalized integration (primitive)

With $D=4+2z$, and $z=-ε$, operate after all stable traces requiring one
 larger dimension. $μ$ ordinary nonnormalized Lebesgue, in fixtures. Basic integral here
 *removes* a scalar common factor (see comment). Good for compact interpolation. Real projection public.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Arc
open Function Filter Set Finset MeasureTheory Real
open scoped Topology ContDiff Interval
open ContinuousLinearMap
variable {I E F G: Type}[NormedAddCommGroup E][NormedSpace ℝ E]
 [NormedAddCommGroup F][NormedSpace ℂ F][NormedSpace ℝ F][IsScalarTower ℝ ℂ F][CompleteSpace F] [NormedAddCommGroup G][NormedSpace ℝ G]
-- differs from actual dr by β = π^z /Γ(z+1) times measure factor. n-dim ordinary outputs then β.
def coreC (W:ℝ→ℂ)(m:ℕ)(f:Tree E F): E→F:= gage m • fetching (pruning (m+1) f) W
variable {z:UScale I}{u:I→ Tree E F}{a V: I→ℝ}{w:I→ℝ→ℂ}{b:ℕ}
lemma core (h: quiet z u a)(hm:∀ i, Reflect (u i))(m:ℕ)(hw:shadeB w V b) : veg z (fun i=> coreC (w i) m (u i)) (fun i=> a i*V i):= (shade_fin (pruned h hm (m+1)).1 hw).L ( (gage m) • ContinuousLinearMap.id ℝ F) -- id ambiguity

variable [MeasurableSpace G][BorelSpace G][FiniteDimensional ℝ G](μ:Measure G)[μ.IsAddHaarMeasure]
-- nested projection
def mirror (f:(G×ℝ)×E→ F): Prop:= ∀ i t w, f ((i,-t),w)=f ((i,t),w)
def swoop (Z:ℂ)(μ:Measure G)(m:ℕ)(f:(G×ℝ)×E→F): E→F:= coreC (cloud Z) m (carpet μ f)
variable {K:I→ (G×ℝ)× E→ F}{Z:I→ℂ}{S:ℕ}
omit [μ.IsAddHaarMeasure] [CompleteSpace F] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ G] [NormedAddCommGroup G] [BorelSpace G] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] in
lemma mirror_r {f:(G×ℝ)×E→ F}(H:mirror f): Reflect (carpet μ f):= fun t w=> integral_congr_ae (Eventually.of_forall fun i=>H i t w)
lemma swoop_bill (h: quiet z K a)(hm:∀ i, mirror (K i))(m:ℕ)(hx:∀ i, ups (Z i))(he:∀ i,2*(Z i).re+1≤(S:ℝ)): veg z (fun i=> swoop (Z i) μ m (K i)) a:= by
   have hi: quiet z (fun i=>carpet μ (K i)) a:= Q.Gquiet μ h; convert! core hi (fun i=>mirror_r μ (hm i)) m (shade_cloud hx he) using 1; simp
end YM.MS.Arc
