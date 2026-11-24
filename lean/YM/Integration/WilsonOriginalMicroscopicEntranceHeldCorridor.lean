import YM.Integration.WilsonOriginalMicroscopicEntranceHeldBoards
import YM.Integration.WilsonOriginalMicroscopicEntranceHeldPhase
import YM.Integration.WilsonOriginalSignedPhysicalCorridor

/-! The entrance of the original physical corridor is the signed difference on the same
finite Wilson board, with the old scalar and every occupied component at its own grade. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceHeldCorridor
open Function Finset MeasureTheory Lattice Wilson RG Marker PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Extra.Histories Extra.Histories.Relay MergeProof MergeProof.Accent Extra.Trajectories Extra.Multi
open WilsonOriginalJointTrialHearing (read)
open WilsonMeasuredPublicEntrancePanel (Panel Raw Guard)
open WilsonOriginalMicroscopicEntranceHeldBoards (board)
open WilsonOriginalMicroscopicEntranceHeldPhaseIncome (entry)
open WilsonOriginalMicroscopicEntranceHeldMasterRead (ReadingAt)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){V:Type}[Fintype V][DecidableEq V](d:V→ℕ)
  {N per f K j requested power t:ℕ}{B:ℝ}{fk:f≤K}(cut:K≤N)
  (A:Panel R d N per f K fk cut requested power t B)
local notation "C" => R.family
local notation "J" => Stock.census V
local notation "X" i:max=>Config G ((C).side i per)
local notation "H" =>(C).path.levels.clock.hatBeta f

theorem field :
    gust (C).path N per N (board R (N:=N) (Raw R d A)) K cut - board R (N:=N) (Guard R d A)=
      board R (N:=N) (entry R d cut A):=by
  rw [WilsonOriginalMicroscopicEntranceHeldBoards.deposited R _ (WilsonOriginalMicroscopicEntranceHeldBoards.raw R d cut A) cut le_rfl]
  funext U s
  change ((C).path.rep N per K).eval U • actualTransport (C) (N:=N) (Raw R d A s) cut U -
      ((C).path.rep N per K).eval U • Guard R d A s U =
      ((C).path.rep N per K).eval U • (actualTransport (C) (N:=N) (Raw R d A s) cut U-Guard R d A s U)
  exact (smul_sub ..).symm

/-- The exact variable named enter in the original corridor, evaluated before any
triangle inequality on the dated regular or hard terms. -/
theorem original (jf:j≤f)(W:X j)(heard:ReadingAt R d A jf W):
    let physical:=board R (N:=N) (Raw R d A)
    let trial:=board R (N:=N) (Guard R d A)
    let road:=jf.trans fk
    let upper:=gust (C).path N per N physical K cut-trial
    Integrable physical (prior G _) ∧ Integrable trial (prior G _) ∧ Integrable upper (prior G _) ∧
    ∀s:(J).Mode,
      let entered:=read R N per W road upper s
      entered=actualTransport (C) (N:=N) (entry R d cut A s) road W ∧
      entered=actualTransport (C) (N:=N) (Raw R d A s) (road.trans cut) W-
        actualTransport (C) (N:=N) (Guard R d A s) road W ∧ ‖entered‖≤((H)^requested)⁻¹:=by
  intro physical trial road upper
  obtain ⟨top,printed⟩:=WilsonOriginalMicroscopicEntranceHeldBoards.original R d cut A
  have receipt:Integrable (board R (N:=N) (entry R d cut A)) (prior G _):=
    integrable_pi_iff.mpr (WilsonOriginalMicroscopicEntranceHeldPhaseIncome.original R d cut A)
  have bound:upper=board R (N:=N) (entry R d cut A):=field R d cut A
  refine ⟨top,printed,bound ▸ receipt,?_⟩
  intro s entered
  have eq:entered=actualTransport (C) (N:=N) (entry R d cut A s) road W:=by
    change read R N per W road upper s=_
    rw [bound]
    exact WilsonOriginalMicroscopicEntranceHeldBoards.reading R _ receipt road W s
  exact ⟨eq,eq.trans (heard s).1,eq ▸ (heard s).2⟩

end YM.Integration.WilsonOriginalMicroscopicEntranceHeldCorridor
end
