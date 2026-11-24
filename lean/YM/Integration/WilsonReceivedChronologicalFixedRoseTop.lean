import YM.Integration.WilsonReceivedChronologicalSocket
import YM.Integration.WilsonOriginalCompactTrialTelescope
/-! The entire selected canonical stencil is integrable on the original upper Haar field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalFixedRoseTop
open Finset Lattice Wilson RG Marker Multi QuadraticLocal Org AllOrder
open QuadraticLocal.Affinity QuadraticLocal.Earn QuadraticLocal.Mentor
open WilsonThermometerDeclaredSeeds XSpace PhysicalNext.Repeat.Legato
open WilsonOriginalCensusCanonicalRows (row probe)
open WilsonOriginalMixedBlockRows (room)
open WilsonReceivedCanonicalVersePortfolio (Selection)
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider OriginalMarkedSourceComet
open scoped Classical BigOperators
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open Planned.GuardedAtom Push.Local Source Labels Extra.Histories Next.Foundations
open scoped Classical BigOperators Topology

open Push.AbsoluteSums

open MeasureTheory WilsonRootedKioskOccupiedSlip

open YM.Overlay.Bands WilsonOriginalJointTrialHearing
open Extra.Histories.Relay MergeProof MergeProof.Accent Extra.Trajectories Extra.Multi


open WilsonReceivedChronologicalSocket (input extend lit)
open WilsonReceivedCanonicalVersePosterior (word)
variable {G:Gauge}{V:Type}[Fintype V][DecidableEq V](R:Run G)(d:V→ℕ){h:V→ℕ}
local notation "J" => Stock.census V


theorem parts (s:(J).Mode)(q:Selection R d s.val)(hd:∀j,0<d j){n:Side}
    (o:V→Site n)(σ:ℝ)(g:ℝ)(κ:(j:V)→Knob (h j))(pt:V→Chamber)
    (t:(J).Mode)(U:Config G n):
    (Poly.pass (Spill.Foundry.uncut (row R d (extend R d s.val q) hd o σ) g lit U)).part t=
      word R d κ pt g o t.val (fun a=>extend R d s.val q a.val) U:=by
  let z:=extend R d s.val q
  let M:=row R d z hd o σ
  let f:V→ℂ:=fun j=>WilsonReceivedCanonicalVerseBasis.restored R d κ pt g j (z j) (o j) U
  have source:Spill.Foundry.uncut M g lit U=∑j,WardBin.Lambda.fuse j (f j):=by
    unfold Spill.Foundry.uncut
    rw [tsum_fintype]
    apply sum_congr rfl
    intro j _
    change Poly.send ((J).fire j) ((M j).nominal g lit U)=_
    rw [WilsonOriginalCensusCanonicalRows.nominal R d z hd o σ κ pt]
    simp only [probe,WilsonReceivedChronologicalSocket.lit,one_mul]
    rfl

  change (Poly.pass (Spill.Foundry.uncut M g lit U)).part t=_
  rw [source,WardBin.Lambda.passion,WardBin.Lambda.expend]
  change (∏j∈t.val,f j)=_
  rw [←prod_coe_sort]
  rfl

theorem original {N per K:ℕ}(valid:K≤N)(s:(J).Mode)(q:Selection R d s.val)(hd:∀j,0<d j)
    (o:V→Site (R.family.side K per))(σ:ℝ)(g:ℝ)(κ:(j:V)→Knob (h j))(pt:V→Chamber):
    Integrable (input R d s q hd o σ (R.family.path.rep N per K) g) (prior G _):=by
  let Y:=R.family.path.rep N per K
  let P:Config G (R.family.side K per) → Poly (J):=fun U=>
    Poly.pass (Spill.Foundry.uncut (row R d (extend R d s.val q) hd o σ) g lit U)
  have field:Continuous P:=by
    have allrows:P=fun U=>∑t:(J).Mode,Poly.send t ((P U).part t):=funext fun U=>(Poly.studs _).symm
    rw [allrows]
    apply continuous_finsetSum
    intro t _
    apply (sends t).comp
    have same:(fun U=>(P U).part t)=word R d κ pt g o t.val (fun a=>extend R d s.val q a.val):=
      funext (parts R d s q hd o σ g κ pt t)
    rw [same]
    exact WilsonReceivedCanonicalVersePosterior.smooth R d κ pt g o t.val _
  have quiet:=Y.envelope (R.makes.wilson.represents N per K valid).good
  obtain ⟨C,bounded⟩:=isCompact_univ.exists_bound_of_continuousOn field.continuousOn
  obtain ⟨D,measure⟩:=quiet.cost
  change Integrable (fun U=>(Y.eval U:ℂ) • P U) (prior G _)
  apply Integrable.of_bound ((Complex.continuous_ofReal.measurable.comp quiet.meas).smul field.measurable).aestronglyMeasurable (D*C)
  refine ae_of_all _ fun U=>?_
  change ‖(Y.eval U:ℂ) • P U‖ ≤ D*C
  rw [norm_smul,Complex.norm_real]
  exact mul_le_mul (measure U) (bounded U (Set.mem_univ _)) (norm_nonneg _) ((norm_nonneg _).trans (measure U))

end YM.Integration.WilsonReceivedChronologicalFixedRoseTop
end
