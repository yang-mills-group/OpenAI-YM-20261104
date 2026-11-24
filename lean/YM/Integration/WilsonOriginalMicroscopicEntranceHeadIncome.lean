import YM.Integration.WilsonSeparatedPrefixCanonicalWithdrawal
import YM.Integration.WilsonOriginalMicroscopicEntranceHeadCharge
import YM.Integration.WilsonSeparatedPrefixCanonicalConvolution

/-! A before-cutoff, arbitrary-roster receipt on the authentic canonical carrier. The
left side is the complete original submitted ordinary face minus the masked peer product,
with every old quiet and all admissible occupied owners in the physical numerator. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceHeadIncome
open Function Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Marker Push AbsoluteSums
open Push.Local RG12 Extra.Histories Extra.Histories.Relay Ac GridApprox.Nil MergeProof MergeProof.Accent MergeProof.Menu
open RG05Readout RG05Readout.Native RG05Readout.Address RG05Readout.Many RG05Readout.Pantry Records
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Motion Bandage
open Extra.Multi Extra.Trajectories ConnectedActivityE6 Pressure Extra.Iteration Next.Foundations Lotus
open Trace.Physical.GermGraph Lodestar WilsonThermometerUnitFilingCoarse WilsonOriginalCompanionLinearFiling
open WilsonOriginalOccupiedStencil WilsonOriginalOccupiedSource
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)
local notation "V" => Fin 3
local notation "C" => R.family
local notation "A" => R.family.path.levels
local notation "S₀" => Marks V
local notation "S₂" => Marks (V×Bool)
local notation "V₂" => V×Bool
local notation "X" => Unit×(V×Bool)

open WilsonOriginalMicroscopicEntranceEarlier (face salary)
open WilsonOriginalMicroscopicEntranceDeposits (funded)

theorem pupil {p f:ℕ}(o:Fin 3→Site ((C).side f p))(x:Fin 3)(φ:Config G ((C).side f p)→ℂ)(c:Poly S₀)
    (M:Support ((C).side f p)→ Config G ((C).side f p)→Poly S₀){σ α fee:ℝ}{B:ℕ}{w:Fin 3→ℝ}
    (burn:∀Z,Burns o Z (M Z) σ)(towed:Towed w id M B α fee)
    (row:∀U,Poly.send ((S₀).fire x) (φ U)=c+∑Z,M Z U):funded φ:=by
  let s: (S₀).Mode:=(S₀).fire x
  have scalar(U):φ U=c.part s+∑Z,(M Z U).part s:=by
    have h:=congrArg (fun v:Poly S₀=>v.part ((S₀).fire x)) (row U)
    rw [Poly.part_send,if_pos rfl] at h
    change φ U=c.part s+(∑Z,M Z U).part s at h
    simpa only [Poly.part_sum] using h
  obtain ⟨_,_,_,tokens⟩:=towed
  choose bound _ bills _ using tokens
  refine ⟨?_,‖c.part s‖+∑Z,bound Z s,?_⟩
  · rw [show φ=(fun U=>c.part s+∑Z,(M Z U).part s) from funext scalar]
    exact measurable_const.add (Finset.measurable_sum _ fun Z _=>(burn Z).me s)
  · intro U
    rw [scalar]
    apply (norm_add_le ..).trans
    exact add_le_add_right ((norm_sum_le _ _).trans (Finset.sum_le_sum fun Z _=>bills Z U s)) _

theorem original {N p f:ℕ}(live:f≤N)(o:Fin 3→Site ((C).side f p))(φ:Fin 3→ Config G ((C).side f p)→ℂ)(c:Fin 3→Poly S₀)
    (M:Fin 3→Support ((C).side f p)→ Config G ((C).side f p)→Poly S₀){σ α:ℝ}{B:ℕ}{w fee:Fin 3→ℝ}
    (burn:∀a Z,Burns o Z (M a Z) σ)(towed:∀a,Towed w id (M a) B α (fee a))
    (row:∀a U,Poly.send ((S₀).fire a) (φ a U)=c a+∑Z,M a Z U)(s:(S₀).Mode):
    Integrable (fun U=>(((C).path.rep N p f).eval U:ℂ)*∏a∈s.val,φ a U) (prior G _):=by
  obtain ⟨m,M',h⟩:=salary φ (fun a=>pupil R o a (φ a) (c a) (M a) (burn a) (towed a) (row a)) s
  have seen:=actualTransport_weighted_integrable (C) R.makes live m.aestronglyMeasurable h (le_refl f)
  simpa only [actualTransport_base (C) R.makes live,face,Complex.real_smul] using seen

end YM.Integration.WilsonOriginalMicroscopicEntranceHeadIncome
end
