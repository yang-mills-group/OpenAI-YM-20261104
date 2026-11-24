import YM.Integration.WilsonOriginalOccupiedAngularPage
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonOriginalPolarizedAngularPage
open Lattice Function Finset Further.PhysicalPeriodLimitF933 Macrame
open FVA1Physical TwoReset WilsonOriginalConnectedPeriodPage WilsonOriginalOccupiedAngularPage
open scoped BigOperators
variable {n N:Side} {α E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual deck acts on all test links in a copy before taking its connected coefficient. -/
def board (h:n.val∣N.val) (anchor:Site N) (move:Site N→E→L[ℝ]E) (F:E→ℂ):E→ℂ:=
  ∑ u:Fin (Pages n N), F ∘ (move ((FVA1Physical.TwoReset.page h (splitter h anchor) u).val-anchor))

def entries (r:ℕ) (ray:Site N×α→E) (F:E→ℂ) (x:Positions N α r):ℂ:=
  iteratedFDeriv ℝ r F 0 (fun v=>ray (x v))

theorem filed (h:n.val∣N.val) (anchor:Site N) (move:Site N→E→L[ℝ]E) (ray:Site N×α→E)
    (placed:∀ a (x:Site N×α),move a (ray x)=ray (a+x.1,x.2)) (r:ℕ) {F:E→ℂ} (smooth:ContDiff ℝ r F)
    (x:Positions N α r):entries r ray (board h anchor move F) x=roster h anchor (entries r ray F) x:=by
  unfold board entries roster
  rw [iteratedFDeriv_sum_apply (fun u _=>(smooth.comp (move _).contDiff).contDiffAt),
    _root_.sum_apply]
  apply sum_congr rfl
  intro u _
  let a:Site N:=(FVA1Physical.TwoReset.page h (splitter h anchor) u).val-anchor
  change iteratedFDeriv ℝ r (F ∘ (move a)) 0 (fun v=>ray (x v))=
    iteratedFDeriv ℝ r F 0 (fun v=>ray ((shift a x) v))
  rw [(move a).iteratedFDeriv_comp_right smooth 0 (le_refl _),map_zero,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  exact congrArg (fun t=>iteratedFDeriv ℝ r F 0 t) (funext (fun v=>placed a (x v)))

theorem binding (h:n.val∣N.val) (left right:Site N) (move:Site N→E→L[ℝ]E) (ray:Site N×α→E)
    (placed:∀ a (x:Site N×α),move a (ray x)=ray (a+x.1,x.2)) (r:ℕ) (F G:E→ℂ)
    (physical:ContDiff ℝ r F) (independent:ContDiff ℝ r G)
    (paid:∀ A,board h left move F A=board h right move G A) (x:Positions N α r):
    roster h left (entries r ray F) x=roster h right (entries r ray G) x:=by
  rw [←filed h left move ray placed r physical x,←filed h right move ray placed r independent x,funext paid]

end YM.Integration.WilsonOriginalPolarizedAngularPage
