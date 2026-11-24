import YM.Integration.WilsonOriginalFiledBochner
import YM.Integration.WilsonOriginalJointTrialHearing

/-! The literal microscopic ordinary product and each freshly planted dated
compact word enter a common Wilson telescope on every finite roster. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCompactTrialTelescope
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

variable {G:Gauge}(R:Run G){V:Type}[DecidableEq V](J:Census V){N per:ℕ}
local notation "X" j:max => Config G (R.family.side j per)

def product (d:V→ℕ)(Y:∀a,R.family.label (d a))(site:V→Site (R.family.side N per))(U:X N):Poly J:=
  Poly.inject fun s=>∏a∈s.val,R.family.O N per (Y a) (site a) U

theorem microscopic (ρ:RG.Rep G (R.family.side N per))(quiet:Envelope ρ.eval)
    (d:V→ℕ)(Y:∀a,R.family.label (d a))(site:V→Site (R.family.side N per)):
    Integrable (fun U:X N=>(ρ.eval U:ℂ) • product R J d Y site U) (prior G _):=by
  let P:=product R J d Y site
  have hP:Continuous P:=by
    have parts:P=fun U=>∑s:J.Mode,Poly.send s ((P U).part s):=funext fun U=>(Poly.studs _).symm
    rw [parts]
    apply continuous_finsetSum
    intro s _
    apply (sends s).comp
    change Continuous (fun U:X N=>∏a∈s.val,R.family.O N per (Y a) (site a) U)
    exact continuous_finsetProd s.val fun a _=>R.family.continuousO N per (d a) (Y a) (site a)
  obtain ⟨C,bounded⟩:=isCompact_univ.exists_bound_of_continuousOn hP.continuousOn
  obtain ⟨D,measure⟩:=quiet.cost
  apply Integrable.of_bound ((Complex.continuous_ofReal.measurable.comp quiet.meas).smul hP.measurable).aestronglyMeasurable (D*C)
  refine ae_of_all _ fun U=>?_
  change ‖(ρ.eval U:ℂ) • P U‖ ≤ D*C
  rw [norm_smul,Complex.norm_real]
  exact mul_le_mul (measure U) (bounded U (Set.mem_univ _)) (norm_nonneg _) ((norm_nonneg _).trans (measure U))

variable [Fintype V]{m k b K:ℕ}{π:ℕ→Layout G}{Γ:ℕ→Pace.Coin}
variable (Ψ:∀j,RG.Rep G (R.family.side j per))(course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (mb:m ≤ b)(bK:b ≤ K)(KN:K ≤ N)
    (d:V→ℕ)(Y:∀a,R.family.label (d a))(site:V→Site (R.family.side N per))
    {I T:ℕ→Type}[∀j,Countable (I j)]{o:∀j,V→Site (R.family.side j per)}
    (bank:∀j,Lamps (T j) (I j) G (Ψ j).p (o j) J)(z:∀j,T j)
    {w:ℕ→V→ℝ}{a C:ℕ→ℝ}
    (positive:∀j∈Icc b K,∀v,0<w j v)(width:∀j∈Icc b K,0 ≤ a j)
    (gross:∀j∈Icc b K,Gross (bank j) (w j) (Ψ j).p.B (a j) (C j))
local notation "top" => fun U:X N=>((Ψ N).eval U:ℂ) • product R J d Y site U
local notation "print" => fun j (U:X j)=>((Ψ j).eval U:ℂ) • Poly.pass (bare (bank j) (z j) U)

include course mb positive width gross in
theorem priced (W:Config G (R.family.side b per))(s:J.Mode){upper:ℝ}{charges:ℕ→ℝ}
    (entrance:‖WilsonOriginalJointTrialHearing.read R N per W bK (gust R.family.path N per N (top) K KN-(print) K) s‖ ≤ upper)
    (edges:∀j∈Ico b K,‖WilsonOriginalJointTrialHearing.fee R N per W (print) j s‖ ≤ charges j):
    ‖WilsonOriginalJointTrialHearing.read R N per W (bK.trans KN) (top) s-
      ((R.family.path.rep N per b).eval W:ℂ)⁻¹*((print) b W).part s‖ ≤ upper+∑j∈Ico b K,charges j:=by
  apply WilsonOriginalJointTrialHearing.priced R N per W bK KN (top) _ (print) _ s entrance edges
  · exact microscopic R J (Ψ N) (WilsonOriginalFiledBochner.envelope R course ((mb.trans bK).trans KN) le_rfl) d Y site
  · intro j bj jK
    have within:=Finset.mem_Icc.mpr ⟨bj,jK⟩
    exact WilsonOriginalOrdinaryBochner.unmasked (Ψ j)
      (WilsonOriginalFiledBochner.envelope R course (mb.trans bj) (jK.trans KN))
      (bank j) (positive j within) (width j within) (gross j within) (z j)

end YM.Integration.WilsonOriginalCompactTrialTelescope
end
