import YM.Integration.WilsonSeparatedOriginalSlabWatchScalar
import YM.Integration.WilsonSeparatedOriginalSlabWatchGauge
import YM.Integration.WilsonSeparatedOriginalSlabPhysicalBox

/-! The complete zero-horizon coefficient of a registered primary roster keeps every fine position and the common signed center measure. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabWatchScalarMesh
open Function Set Filter MeasureTheory Lattice Wilson RG Source Labels Analysis Next.Foundations Next.UVStress Push.Local Bid
open ProjectorNext.Equivariance Trace.Physical Trace.Physical.GermGraph RG16 RG16.Literal
open RG05Readout Address Native Many Pulse Flatten PhysicalNext.Repeat.Legato RGComparison.Core16 OPE PhysMS Spec RG17 Extraction
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Extra.Histories.Relay PhysicalNext
open FilteredWilsonProduct
open WilsonMacroscopicRichFlatPosteriorLaw WilsonSeparatedOriginalSlabPhysicalBox WilsonReportHarvestReadmittedSource
open WilsonReportingTerminalPrimaryStencil WilsonSeparatedOriginalSlabWatchContrast
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}(R:Run G){N p m k u:ℕ}{I:Type}[Fintype I][DecidableEq I]
local notation "C"=>R.family

def weighted (s:I→ℕ)(k m N:ℕ)(r:ℝ)(Ψ:Wave I)(g:Body)(x:I→Site ((C).side N p)):ℂ:=
  weight («C»:=R.family) s m N r*row C k r Ψ g ((C).S.place ∘ x)

def micros (s:I→ℕ)(v:(i:I)→(C).label (s i))(x:I→Site ((C).side N p)):Cut C N p:=fun U=>∏i,(C).O N p (v i) (x i) U

omit [DecidableEq I] in
theorem regular (s:I→ℕ)(v:(i:I)→(C).label (s i))(x:I→Site ((C).side N p)):Continuous (micros R s v x):=
  continuous_finsetProd _ fun _ _=>(C).continuousO ..

theorem full {f:Extraction.Order}{S:Table (C).book}{F:Final C f S}(L:Layout F)(s:I→ℕ)(w:(i:I)→(C).label (s i))
    (U:(t:ℕ×ℕ)→(i:I)→Emblems C (s i)){r cap:ℝ}(rp:0<r)(Ψ:Wave I)(g:Body)(top:k≤N)(mn:m≤N)
    (enclosed:∀x∈tsupport Ψ.val,∀i,‖x i‖≤cap)(room:r*cap+2*(C).S.a k<(C).S.radius p)(V:Config G ((C).side N p)):
    WilsonSeparatedOriginalSlabWatchContrast.full L s r w U k m Ψ g (N,p) V=
      ∑x:I→Site ((C).side N p), weighted R s k m N r Ψ g x * micros R s (fun i=>atRef L (s i) r (N,p) (w i)) x V:=by
  unfold WilsonSeparatedOriginalSlabWatchContrast.full;rw [dif_pos top]
  simp_rw [carried L _ r _ _ m N p mn]
  exact WilsonSeparatedOriginalSlabPhysicalBox.returned R.makes s _ r Ψ top rp enclosed room m g V

theorem original {f:Extraction.Order}{S:Table (C).book}{F:Final C f S}(L:Layout F)(s:I→ℕ)(w:(i:I)→(C).label (s i))
    (U:(t:ℕ×ℕ)→(i:I)→Emblems C (s i)){r cap:ℝ}(rp:0<r)(Ψ:Wave I)(g:Body)(top:k≤N)(mn:m≤N)
    (enclosed:∀x∈tsupport Ψ.val,∀i,‖x i‖≤cap)(room:r*cap+2*(C).S.a k<(C).S.radius p)
    (T:Slices (C).path.levels p)(live:u<N)(door:Opened C 0 u p)
    (paid:Booked C N p 0 (WilsonSeparatedOriginalSlabWatchContrast.full L s r w U k m Ψ g (N,p)) u live.le):
    let Y:=WilsonSeparatedOriginalSlabWatchContrast.full L s r w U k m Ψ g (N,p)
    let z:=label («C»:=R.family) (D:=0) (w:=(N,p)) R.makes door live.le Y
    z 0=∑x:I→Site ((C).side N p),weighted R s k m N r Ψ g x *
      (traversal T live.le).conditioned (line (C).path p u N) (micros R s (fun i=>atRef L (s i) r (N,p) (w i)) x) 1:=by
  let Y:=WilsonSeparatedOriginalSlabWatchContrast.full L s r w U k m Ψ g (N,p)
  let μ:=WilsonMacroscopicRichFlatPosteriorLaw.law R N p live 1
  letI:IsProbabilityMeasure μ:=WilsonMacroscopicRichFlatPosteriorLaw.prob R live le_rfl 1
  let v:=fun i=>atRef L (s i) r (N,p) (w i)
  let c:=weighted R s k m N r Ψ g (p:=p)
  have single (x:I→Site ((C).side N p)):∫V,micros R s v x V ∂μ=(traversal T live.le).conditioned (line (C).path p u N) (micros R s v x) 1:=by
    simpa only [WilsonMacroscopicRichReportedPosterior.observation,pow_zero,one_mul] using
      (WilsonSeparatedOriginalSlabWatchPosterior.physical (h:=0) R T live (micros R s v x) (regular R s v x) 1).symm
  dsimp only
  rw [WilsonSeparatedOriginalSlabWatchScalar.original R T live door Y Y.continuous (WilsonSeparatedOriginalSlabWatchGauge.filed R.makes L s r w U k m Ψ g (N,p)) paid]
  calc
    _=∫V,∑x:I→Site ((C).side N p),c x * micros R s v x V ∂μ:=by
      apply integral_congr_ae;filter_upwards with V;exact full R L s w U rp Ψ g top mn enclosed room V
    _=∑x:I→Site ((C).side N p),c x*(traversal T live.le).conditioned (line (C).path p u N) (micros R s v x) 1:=by
      rw [integral_finsetSum];swap
      · exact fun x _=>(continuous_const.mul (regular R s v x)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      apply Finset.sum_congr rfl;intro x _;rw [integral_const_mul,single]

end YM.Integration.WilsonSeparatedOriginalSlabWatchScalarMesh
