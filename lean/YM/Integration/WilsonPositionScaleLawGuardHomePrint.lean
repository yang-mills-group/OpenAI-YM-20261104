import YM.Integration.WilsonPositionScaleLawGuardLift
import YM.Integration.WilsonPositionScaleLawGuardEval
import YM.Integration.WilsonPositionScaleLawDressedBudget

/-! The finite polynomial of the prescribed homogeneous Borel correction in
the original normed field coordinates, including its identity coefficient. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardHomePrint
open Function Filter Set Finset Spec Table Extraction OPE OPE.Orbits Climb PhysMS Trace.Pilot
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus PhysicalNext.Repeat.Legato
open MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival PowerSeries
open WilsonPhysicalPositionBornCandidates (record)
open WilsonPositionScaleLawGuardLift (act pack)
open WilsonPositionScaleLawGuardPoly (value)
open WilsonPositionScaleLawDressedTransport (adjust)
open WilsonPositionHomogeneousCoefficients (Warrant letter)
open scoped Topology Polynomial Classical BigOperators
local instance {X:Type*}[NormedAddCommGroup X][NormedSpace ℂ X]:NormedRing (X→L[ℂ]X):=ContinuousLinearMap.toNormedRing
local instance {X:Type*}[NormedAddCommGroup X][NormedSpace ℂ X]:NormedAlgebra ℂ (X→L[ℂ]X):=ContinuousLinearMap.toNormedAlgebra
variable {G:Gauge}(C:Family G)(Z:WilsonPrescription G){d:ℕ}
set_option quotPrecheck false
local notation "E"=> (Bel C.book).Field

theorem entry (a:Change G d):record G C d (guide G d a)=act C d a.val:=by
  ext v
  change (fields C.labels d).symm (((guide G d).symm (guide G d a)).val ((fields C.labels d) v))=
    (fields C.labels d).symm (a.val ((fields C.labels d) v))
  rw [LinearEquiv.symm_apply_apply]

theorem each (H:Warrant Z)(k:ℕ):act C d (coeff k (adjust Z d))=
    (if k=0 then 1 else 0)+record G C d (guide G d (letter Z d k)):=by
  by_cases e:k=0
  · subst k
    have a:coeff 0 (adjust Z d)=1:=(coeff_zero_eq_constantCoeff_apply _).trans (H.scheme d).scale.lead
    simp [a,WilsonPositionHomogeneousCoefficients.letter]
  · rw [if_neg e,zero_add,entry,WilsonPositionHomogeneousCoefficients.positive Z H d e]

def tab (d q:ℕ)(g:ℝ):MoveSpace G d:=∑k∈range (q+1),g^k • guide G d (letter Z d k)

def taylor (d q:ℕ)(g:ℝ):E d→L[ℂ]E d:=value (trunc (q+1) (pack C (adjust Z d))) (g:ℂ)

theorem original (H:Warrant Z)(d q:ℕ)(g:ℝ):
    taylor C Z d q g=1+record G C d (tab Z d q g):=by
  rw [taylor,WilsonPositionScaleLawGuardEval.printed]
  have I:Finset.Iic q=range (q+1):=by ext n;simp only [Finset.mem_Iic,Finset.mem_range];omega
  rw [I];simp_rw [WilsonPositionScaleLawGuardLift.coefficient]
  change (∑k∈range (q+1),(g:ℂ)^k • act C d (coeff k (adjust Z d)))=_
  simp_rw [each C Z H,smul_add]
  rw [Finset.sum_add_distrib]
  have unit:(∑k∈range (q+1),(g:ℂ)^k • (if k=0 then (1:E d→L[ℂ]E d) else 0))=1:=by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro j _ hj;rw [if_neg hj];ext v;change (g:ℂ)^j • (0:E d)=0;exact smul_zero _
    · intro h;exact (h (Finset.mem_range.mpr (by omega))).elim
  rw [unit,tab,map_sum]
  congr 1
  apply Finset.sum_congr rfl;intro k _
  rw [map_smul,←Complex.ofReal_pow];rfl

end YM.Integration.WilsonPositionScaleLawGuardHomePrint
