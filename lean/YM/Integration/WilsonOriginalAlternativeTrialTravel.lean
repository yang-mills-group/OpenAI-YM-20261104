import YM.Integration.WilsonOriginalAlternativeTrialSource
import YM.Integration.WilsonReceivedCloseHistory
import YM.Integration.WilsonOriginalMicroscopicEntranceReader

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeTrialTravel
open MeasureTheory Finset Lattice Wilson RG Tree Marker QuadraticLocal.Affinity MergeProof.Accent
open PhysicalNext.Repeat.Legato
open WilsonOriginalAlternativeTrialSource
open Extra.Trajectories WilsonPositionThermometerGradedReading
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) {V:Type} [Fintype V] [DecidableEq V] (d:V→ℕ) (N p b:ℕ)
  (o:V→Site (R.family.side (b+1) p)) (v:∀j,R.family.label (d j)) (z:V→ℂ)
local notation "D_" => (WilsonOriginalAlternativeFiniteSource.disks (V:=V))
local notation "J_" => Stock.census V
local notation "trial_" => source R d N p (b+1) o v z
local notation "row_" i:max step:max => WilsonReceivedCloseHistory.history (N:=N) R D_ trial_ i step

theorem field (top:b+1≤N) {f:ℕ} (floor:f≤b) (x:Wallet D_) (s:(J_).Mode)
    (U:Config G (R.family.side f p)):
    (LocalComparison.actualPush R.family N p f ((row_ f floor) x) U).part s =
      (R.family.path.rep N p f).eval U • actualTransport R.family (N:=N)
        (mode R d N p (b+1) o v z x s) (floor.trans (Nat.le_succ b)) U:=by
  have edge:LocalComparison.actualPush R.family N p f ((row_ f floor) x)=
      gust R.family.path N p (b+1) (trial_ x) f (floor.trans (Nat.le_succ b)):=
    (gust_step _ _ _ _ _ (Nat.succ_le_succ floor)).symm
  rw [edge,congrFun (WilsonOriginalMicroscopicEntranceReader.row (N:=N) R (floor.trans (Nat.le_succ b)) (trial_ x) s
    (prior R d N p (b+1) o v z top x)) U,actualTransport_unnormalize R.family R.makes top]
  rfl

theorem one (top:b+1≤N) {f:ℕ} (floor:f≤b) (j:V) (U:Config G (R.family.side f p)):
    (LocalComparison.actualPush R.family N p f ((row_ f floor) WilsonOriginalAlternativeFiniteSource.fired) U).part ((J_).fire j) =
      (R.family.path.rep N p f).eval U • actualTransport R.family (N:=N)
        (arm R d N p (b+1) o v z j) (floor.trans (Nat.le_succ b)) U:=by
  rw [field R d N p b o v z top floor]
  congr 2
  funext Y
  simp only [mode,WilsonOriginalAlternativeFiniteSource.fired,show ((J_).fire j).val={j} from rfl,
    Finset.prod_singleton,one_mul]

end YM.Integration.WilsonOriginalAlternativeTrialTravel
