import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.AnalyticMoments
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.CutRay
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace IssuedMaxwell.CutOdd
open YM YM.XSpace YM.Maxwell YM.XSpace.Normalize YM.XSpace.Structure1
open YM.XSpace.Cirrus YM.XSpace.AxesTangent YM.XSpace.Photo
open scoped ContDiff Topology BigOperators
variable (G:Gauge)(d:ℕ)(c:Shade.Cut)

abbrev Station := {t:PotLin G d // t.w∈Good c t.n}
theorem original (g:G.Simple)(hd:4≤d)(A:Odds G d)
    (dark:∀t:Station G d c,showCase t.val A=0):A=0:=by
  apply Subtype.ext
  refine odd_hush A.property g hd ?_
  intro n x hx
  ext1 p
  apply CutRay.original (f:=fun z=>lot (scene z d) A.val p) hx c
  · intro z hz
    simp only [lots,screen]
    exact ContDiffAt.sum fun _ _=>AnalyticMoments.original _ hz
  · intro z hz hpaid
    exact dark ⟨⟨n,p,z,hz⟩,hpaid⟩
end IssuedMaxwell.CutOdd
end
