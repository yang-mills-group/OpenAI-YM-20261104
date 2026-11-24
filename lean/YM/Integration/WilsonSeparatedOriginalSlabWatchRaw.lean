import YM.Integration.WilsonSeparatedOriginalSlabWatchPhysical

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabWatchRaw
open Set Function Spec OPE PhysMS
open scoped Topology ContDiff Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}{n:ℕ}

theorem raw (F:Final C f S)(v:Fin n→S.Tag)(x:Points n)(live:x∈conf n):
    S.useAt S x v=S.read x (detectorRaw S ∘v):=by
  have h:=S.at_project S F.room.kernel.laws.toSymmetric (fun _=>le_refl _) live (detectorRaw S ∘ v)
  refine Eq.trans ?_ h;apply congrArg (S.useAt S x);funext i;exact (OPE.raw_class S (v i)).symm

theorem continuous (F:Final C f S)(v:Fin n→S.Tag):ContinuousOn (fun x:Points n=>S.useAt S x v) (conf n):=by
  exact (S.smooth_read F.room.kernel.smooth (detectorRaw S ∘v)).continuousOn.congr (fun x live=>raw F v x live)

end YM.Integration.WilsonSeparatedOriginalSlabWatchRaw
