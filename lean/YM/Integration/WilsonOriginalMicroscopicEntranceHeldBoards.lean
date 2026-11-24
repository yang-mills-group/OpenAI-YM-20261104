import YM.Integration.WilsonOriginalMicroscopicEntranceHeldPhaseIncome
import YM.Integration.WilsonOriginalOccupiedTransport
import YM.Integration.WilsonOriginalJointTrialHearing

/-! Unnormalized squarefree boards for the actual physical cutoff and the fixed restart.
Taking a marked component after the genuine Wilson push preserves the scalar vacuum. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceHeldBoards
open Function Filter Finset MeasureTheory Lattice Wilson RG Marker PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Extra.Histories Extra.Histories.Relay MergeProof MergeProof.Accent Extra.Trajectories Extra.Multi
open WilsonOriginalJointTrialHearing (read)
open WilsonMeasuredPublicEntrancePanel (Panel Raw Guard charged)
open WilsonMeasuredPublicEntranceGridDebit (fitted)
open WilsonReflectedPublicOrientedFaces (displayed)
open WilsonAddressedFiniteGuardTrial (printed submitted)
open Labels Source QuadraticLocal
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){V:Type}[Fintype V][DecidableEq V]
  {N per f K j requested power t:ℕ}{B:ℝ}
local notation "C" => R.family
local notation "J" => Stock.census V
local notation "X" i:max => Config G ((C).side i per)

def board {i:ℕ}(F:(J).Mode→X i→ℂ)(U:X i):Poly J:=
  fun s=>((C).path.rep N per i).eval U • F s U

theorem reading {i:ℕ}(F:(J).Mode→X i→ℂ)
    (bought:Integrable (board R (N:=N) F) (prior G _))(ji:j ≤ i)(W:X j)(s:(J).Mode):
    read R N per W ji (board R (N:=N) F) s=actualTransport (C) (N:=N) (F s) ji W:=by
  unfold WilsonOriginalJointTrialHearing.read actualTransport
  rw [congrFun (WilsonOriginalOccupiedTransport.projected R _ bought s ji) W]
  simp only [Complex.real_smul,Complex.ofReal_inv]
  rfl

theorem deposited {i:ℕ}(F:(J).Mode→X i→ℂ)
    (bought:Integrable (board R (N:=N) F) (prior G _))(ji:j ≤ i)(live:i≤N):
    gust (C).path N per i (board R (N:=N) F) j ji=
      board R (N:=N) (fun s=>actualTransport (C) (N:=N) (F s) ji):=by
  funext W s
  have same:=reading R F bought ji W s
  have nz:(((C).path.rep N per j).eval W:ℂ)≠0:=
    Complex.ofReal_ne_zero.mpr (Multi.AxisShift.chosen_positive R.makes.wilson (ji.trans live) W).ne'
  change _=((C).path.rep N per j).eval W • actualTransport (C) (N:=N) (F s) ji W
  rw [←same,WilsonOriginalJointTrialHearing.read,Complex.real_smul,←mul_assoc,mul_inv_cancel₀ nz,one_mul]
  rfl

variable (d:V→ℕ){fk:f≤K}(cut:K≤N)(A:Panel R d N per f K fk cut requested power t B)

theorem raw : Integrable (board R (N:=N) (Raw R d A)) (prior G _):=by
  apply integrable_pi_iff.mpr
  intro s
  apply WilsonMeasuredPublicEntranceOrder.integrable (C) R.makes (le_refl N)
  have h:Continuous (Raw R d A s):=by
    unfold WilsonMeasuredPublicEntrancePanel.Raw
    apply continuous_finsetProd
    intro i _
    exact continuous_const.mul ((C).continuousO N per (d i) (displayed R (d i) (A.names i) (A.turn i))
      (WilsonThermometerReflectedTrajectory.anchorAt R (A.loc i) N))
  obtain ⟨M,paid⟩:=(isCompact_range h.norm).bddAbove
  exact ⟨h.aestronglyMeasurable,M,fun U=>paid ⟨U,rfl⟩⟩

theorem original :
    Integrable (board R (N:=N) (Raw R d A)) (prior G _) ∧
    Integrable (board R (N:=N) (Guard R d A)) (prior G _):=by
  have top:=raw R d cut A
  have earlier:=gust_live (C).path N per N (board R (N:=N) (Raw R d A)) top cut
  rw [deposited R _ top cut le_rfl] at earlier
  refine ⟨top,integrable_pi_iff.mpr fun s=>?_⟩
  have bought:=integrable_pi_iff.mp earlier s
  have diff:=WilsonOriginalMicroscopicEntranceHeldPhaseIncome.original R d cut A s
  have eq:(fun U=>board R (N:=N) (fun k=>actualTransport (C) (N:=N) (Raw R d A k) cut) U s-
      ((C).path.rep N per K).eval U • WilsonOriginalMicroscopicEntranceHeldPhaseIncome.entry R d cut A s U)=
      (fun U=>board R (N:=N) (Guard R d A) U s):=by
    funext U
    simp only [board,WilsonOriginalMicroscopicEntranceHeldPhaseIncome.entry,smul_sub,sub_sub_cancel]
  simpa only [Pi.sub_def,eq] using bought.sub diff

end YM.Integration.WilsonOriginalMicroscopicEntranceHeldBoards
end
