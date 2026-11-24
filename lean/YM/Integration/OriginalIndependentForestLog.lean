import YM.Integration.FundedOriginalVacuumPaths
import YM.WilsonCoeffUV.Marked.Step.LogStep

/-! Forest independence of the full signed, normalized marked logarithm on
one funded original Run, before external evaluation. The moment source includes
every prescribed independent marked vertex via the native square-free exponential. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalIndependentForestLog
open Function Finset Lattice Laurent Wilson RG Tree Exterior Precision
open PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Fk WilsonCoeffUV.Power
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue
open WilsonCoeffUV.Mer WilsonCoeffUV.Cosmos WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Soil WilsonCoeffUV.Embroider FreeResolvent
open scoped Classical BigOperators

variable {G : Gauge} {ι : Type} [DecidableEq ι] {D k : ι → ℕ}

/-- Exact complete moment, as a value in the independently marked coefficient
space. The native source exponential is formed before changing forest. -/
theorem moments (R : Run G) (hG : G.Simple) (m N : ℕ) (hm : m < N) (n : Side)
    (F : Forest (mStep R.family.path.levels n m).ratio) (K : family G D) (hK : Eu k K)
    (C : Cost) (J : Finset ι) :
    let A := R.family.path.levels
    let S := mStep A n m
    let H := freeForms A N (m+1)
    let M := roam A N m n
    let P := (story A R.metals.O N (m+1)).1 (n*(loose A m).L)
    unmark S (repeatF S) H M R.metals.O P K C k J = unmark S F H M R.metals.O P K C k J := by
  intro A S H M P
  have h := placedO K hK J
  exact congrArg (Blue.mix C) (FundedOriginalVacuumPaths.forests R hG N m hm n F _ _
    (h.span _) (h.pale _) (h.token _))

/-- The same result after the original normalized connected logarithm, for any
specified subset, any test derivatives, all joint colors and all orders.
Uniqueness is used only on the already identified native moment algebra. -/
theorem connected (R : Run G) (hG : G.Simple) (m N : ℕ) (hm : m < N) (n : Side)
    (F : Forest (mStep R.family.path.levels n m).ratio) (K : family G D) (hK : Eu k K)
    (C : Cost) (J : Finset ι) :
    let A := R.family.path.levels
    let S := mStep A n m
    let H := freeForms A N (m+1)
    let M := roam A N m n
    let P := (story A R.metals.O N (m+1)).1 (n*(loose A m).L)
    mist S (repeatF S) H M R.metals.O P K C k J = mist S F H M R.metals.O P K C k J := by
  intro A S H M P
  have hO := R.alloy.B.ratio
  have hp := (old A R.metals.O hG hO N (m+1) hm).basis (n*(loose A m).L)
  have hu := steaks S (repeatF S) H M R.metals.O P K C hp.lamp hO hK J
  have hv := steaks S F H M R.metals.O P K C hp.lamp hO hK J
  funext i j z
  apply pen_inj
  intro B
  have first := WindE S (repeatF S) H M R.metals.O P K C B hp.lamp hO hK
  have second := WindE S F H M R.metals.O P K C B hp.lamp hO hK
  have hbase : (fun I => flash (pPly B I (unmark S (repeatF S) H M R.metals.O P K C k I))) =
      fun I => flash (pPly B I (unmark S F H M R.metals.O P K C k I)) := by
    funext I
    rw [moments R hG m N hm n F K hK C I]
  rw [hbase] at first
  have he := Equation.unique _ _ _ first second
  have hr := by_flash (ply_shell (touch B J).toLinearMap hu.1)
    (ply_shell (touch B J).toLinearMap hv.1) (fun j => ply_pure _ (hu.2 j))
    (fun j => ply_pure _ (hv.2 j)) (congr_fun he J)
  exact congr_fun (congr_fun (congr_fun hr i) j) z

/-- The actual finite face of the funded cover logarithm can be computed
on the independently specified physical forest. The genuine coupling reset
stays after the normalized connected cumulant on that same forest. -/
theorem fromRun (R : Run G) (hG : G.Simple) (m N : ℕ) (hm : m < N) (n : Side)
    (F : Forest (mStep R.family.path.levels n m).ratio) (K : family G D) (hK : Eu k K) (J : Finset ι) :
    let A := R.family.path.levels
    let O := R.metals.O
    let S := mStep A n m
    (logO A O m N K k J).1 n = mist S F (freeForms A N (m+1)) (roam A N m n) O
      ((story A O N (m+1)).1 (n*(loose A m).L)) K (ratioHigh A O N m) k J := by
  intro A O S
  exact (feeleg A O m N K k hm hG R.alloy.B.ratio hK n J).trans
    (connected R hG m N hm n F K hK _ J)

end YM.Integration.OriginalIndependentForestLog
end
