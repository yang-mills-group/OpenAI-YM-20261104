import YM.Integration.WilsonMacroscopicRichPreparedPortfolio
import YM.Integration.WilsonSeparatedOriginalSlabWatchScalarMesh

/-! The independently prescribed RG12 nominal input on exactly the fine sites
of the measured physical stencil. Both signed experiments use the same UV
gauge field, the same envelope factors and the same unchanged spectator. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichSharedGrid
open Function Filter Set MeasureTheory Lattice RG Wilson Source Labels Analysis Next.Foundations Push.Local
open PhysicalNext PhysicalNext.Repeat.Legato RG05Readout Address Native Pulse Flatten RGComparison.Core16
open OPE PhysMS Spec RG17 Extraction MergeProof.Accent Marker Precision
open LocalComparison LocalComparison.Global IterationFour IterationFour.Vacuum FullQLocal
open FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric WilsonLimitConstruction QLocalOriginalQHistory
open WilsonSeparatedOriginalSlabWatchScalarMesh
open scoped Classical BigOperators Topology
variable {G:Gauge}{V:Type}[DecidableEq V][Fintype V]
    (R:Run G)(N per:ℕ)
local notation "UV" => Config G (R.family.side N per)
local notation "Sites" => V → Site (R.family.side N per)
variable (comparison:(V → Site (R.family.side N per)) → Config G (R.family.side N per) → ℂ)

variable {f:Extraction.Order}{S:Table R.family.book}{F:Final R.family f S}(L:Layout F)
    (h:V → ℕ)(w:(i:V) → R.family.label (h i))(Y:(t:ℕ×ℕ) → (i:V) → Emblems R.family (h i))
    {r cap:ℝ}(rp:0<r)(Ψ:Wave V)(g:Body){k m:ℕ}(top:k≤N)(paid:m≤N)
    (enclosed:∀x∈tsupport Ψ.val,∀i,‖x i‖≤cap)(room:r*cap+2*R.family.S.a k<R.family.S.radius per)
local notation "positions" => weighted R h k m (N) r Ψ g
local notation "submitted" => comparison
local notation "marked" => micros R h (fun i=>atRef L (h i) r (N,per) (w i))
local notation "physical" => WilsonSeparatedOriginalSlabWatchContrast.full L h r w Y k m Ψ g (N,per)

def registered (U:UV):ℂ:=∑x:Sites,positions x*submitted x U

include rp top paid enclosed room in
theorem together (U:UV):
    physical U-registered R N per comparison h (r:=r) Ψ g (k:=k) (m:=m) U=
      ∑x:Sites,positions x*(marked x U-submitted x U):=by
  rw [WilsonSeparatedOriginalSlabWatchScalarMesh.full R L h w Y rp Ψ g top paid enclosed room U]
  simp only [registered,mul_sub,Finset.sum_sub_distrib]

include rp top paid enclosed room in
theorem tested (ν:Measure UV)[IsFiniteMeasure ν](E:UV → ℂ)(continuousE:Continuous E)
    (smooth:∀x,Continuous (comparison x)):
    ∫U,(physical U-registered R N per comparison h (r:=r) Ψ g (k:=k) (m:=m) U)*E U ∂ν=
      ∑x:Sites,positions x*∫U,(marked x U-submitted x U)*E U ∂ν:=by
  have each (x:Sites):Continuous (fun U=>(marked x U-submitted x U)*E U):=
    ((WilsonSeparatedOriginalSlabWatchScalarMesh.regular R h _ x).sub
      (smooth x)).mul continuousE
  calc
    _=∫U,∑x:Sites,positions x*((marked x U-submitted x U)*E U) ∂ν:=by
      apply integral_congr_ae;filter_upwards with U
      rw [together R N per comparison L h w Y rp Ψ g top paid enclosed room U,Finset.sum_mul]
      simp only [mul_assoc]
    _=_:=by
      rw [integral_finsetSum];swap
      · intro x _
        exact (continuous_const.mul (each x)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      apply Finset.sum_congr rfl;intro x _
      rw [integral_const_mul]

end YM.Integration.WilsonMacroscopicRichSharedGrid
