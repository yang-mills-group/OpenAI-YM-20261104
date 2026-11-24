import YM.Integration.WilsonOriginalPublicNodalHearing
import YM.Integration.WilsonMeasuredPublicEntranceEntered

/-! The precise printed field returned by the funded original entrance, expressed
on the separately normalized public measuring board. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 700000
namespace YM.Integration.WilsonOriginalPublicNodalEntry
open Finset MeasureTheory Lattice Wilson RG Source Labels PowerSeries Marker QuadraticLocal.Affinity
open RegulatorIR.FVAAlt2 Pert.Asymptotics PhysicalNext.Repeat.Legato
open XSpace XSpace.Normalize XSpace.Rose
open WilsonOriginalPublicTrialFigure
open WilsonOriginalPublicPivotReflected (evaluated)
open WilsonThermometerPositionTunedSlope (Columns finite paid)
open WilsonPositionProgramTrialThermalGrades (frozen)
open WilsonOriginalPublicNodalFiling (residual)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){I:Type}[Fintype I][LinearOrder I](d:I→ℕ)
    {N per K u:ℕ}(o:I→Site (R.family.side K per))(v:∀i,R.family.label (d i))
    (z:I→ℂ)(x:Wallet (WilsonOriginalAlternativeFiniteSource.disks (V:=I)))(s:(Stock.census I).Mode)
local notation "g₀" => regulatorRun R.family N per K
local notation "X" n:max => Config G (R.family.side n per)
local notation "read" => actualTransport R.family (N:=N) (p:=per)
local notation "ink" => WilsonAddressedFiniteGuardTrial.printed R d (N:=N) o v z x s

def dose (i:I):R.family.label (d i):=
  WilsonPositionProgramReportedField.entire R (d i) K (N,per)
    (WilsonAddressedFiniteGuardTrial.submitted R d v z x i)

variable (sites:I→ Cover)(lift:∀a:s.val,wrap (R.family.side K per) (sites a)=o a)
local notation "D" => (fun a:s.val=>d a)
local notation "V" => (fun a:s.val=>dose R d (N:=N) (K:=K) (per:=per) v z x a)
local notation "roots" => (fun a:s.val=>sites a)

include lift in
/-- This is the complete original entrance pupil on every configuration. Its
submitted amplitude, radius and absolute site are those of that entrance. -/
theorem field:
    ink=measured R D g₀ V roots:=by
  funext U
  unfold WilsonAddressedFiniteGuardTrial.printed measured
  rw [←Finset.prod_coe_sort]
  apply prod_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  rw [lift a]
  simp only [dose,amount,WilsonPositionProgramBlockedTrialFiling.atomAt,Complex.real_smul,
    Complex.ofReal_inv,mul_assoc]

variable (P:Period)(tree:P.Tree)(q:ℕ)
local notation "published" => evaluated q g₀ (paid R D (frozen R D V) (finite R D P roots tree))

def balance (uk:u≤K)(U:X u):ℂ:=
  ∑a:Columns R D,weight R D g₀ V a*residual R D roots P tree (N:=N) uk U a q g₀

include lift in
theorem returned (kn:K≤N)(uk:u≤K)(U:X u):
    read ink uk U-published=balance R d (N:=N) (per:=per) v z x s sites P tree q uk U:=by
  rw [field R d o v z x s sites lift]
  exact WilsonOriginalPublicNodalFiling.issued R D roots P tree kn uk U V q
    (ActualRunKernelPackets.regulator_pos R N per K kn).ne'

/-- The authentic upper read in EntranceEntered is the entire jointly transported
N-born word minus this already printed uncut K pupil on the older flat. -/
def enter (kn:K≤N)(uk:u≤K)(Y:X N→ℂ):ℂ:=
  read (fun W=>read Y kn W-ink W) uk 1

include lift in
theorem original (kn:K≤N)(uk:u≤K)(Y:X N→ℂ)
    (landed:enter R d o v z x s kn uk Y=read Y (uk.trans kn) 1-read ink uk 1)
    {A B:ℝ}(phase:‖WilsonOriginalTwoFlatGridScaling.gap R N per u (uk.trans kn) Y‖≤A)
    (funded:‖enter R d o v z x s kn uk Y‖≤B):
    let E:=balance R d (N:=N) (per:=per) v z x s sites P tree q uk 1
    R.family.omega N per Y-published-E=
      WilsonOriginalTwoFlatGridScaling.gap R N per u (uk.trans kn) Y+enter R d o v z x s kn uk Y ∧
    ‖R.family.omega N per Y-published-E‖≤A+B:=by
  intro E
  have step:R.family.omega N per Y-published-E=
      WilsonOriginalTwoFlatGridScaling.gap R N per u (uk.trans kn) Y+enter R d o v z x s kn uk Y:=by
    rw [←WilsonOriginalPublicNodalHearing.phase R (uk.trans kn) Y,landed]
    dsimp only [E]
    rw [←returned R d o v z x s sites lift P tree q kn uk 1]
    ring
  exact ⟨step,step ▸ (norm_add_le ..).trans (add_le_add phase funded)⟩

/-- The independently chosen board may be varied after the authentic upper
entrance is purchased. The single remaining signed coefficient comparison is
evaluated on the original issued amplitudes and on that very board. -/
def Issued (kn:K≤N)(uk:u≤K)(Y:X N→ℂ)(B:ℝ):Prop:=
  ∀(sites:I→ Cover), (∀i:s.val,wrap (R.family.side K per) (sites i)=o i) →
  ∀(P:Period)(tree:P.Tree)(q:ℕ),
    let Dₛ:=fun i:s.val=>d i
    let vₛ:=fun i:s.val=>dose R d (N:=N) (K:=K) (per:=per) v z x i
    let board:=evaluated q g₀ (paid R Dₛ (frozen R Dₛ vₛ)
      (finite R Dₛ P (fun i:s.val=>sites i) tree))
    let E:=balance R d (N:=N) (per:=per) v z x s sites P tree q uk 1
    let phase:=WilsonOriginalTwoFlatGridScaling.gap R N per u (uk.trans kn) Y
    R.family.omega N per Y-board-E=phase+enter R d o v z x s kn uk Y ∧
      ‖R.family.omega N per Y-board-E‖≤‖phase‖+B

theorem issued (kn:K≤N)(uk:u≤K)(Y:X N→ℂ){B:ℝ}
    (landed:enter R d o v z x s kn uk Y=read Y (uk.trans kn) 1-read ink uk 1)
    (funded:‖enter R d o v z x s kn uk Y‖≤B):
    Issued R d o v z x s kn uk Y B:=by
  intro sites lift P tree q
  exact original R d o v z x s sites lift P tree q kn uk Y landed le_rfl funded

end YM.Integration.WilsonOriginalPublicNodalEntry
end
