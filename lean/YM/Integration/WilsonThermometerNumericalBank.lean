import YM.Integration.WilsonThermometerDeclaredSeeds
import YM.Integration.WilsonThermometerRegisteredPupil

/-! The numerical upper bank is calculated from the actual fitted numbers,
translated Wilson paths, registered grades and prescribed quiet layout,
before either auxiliary-copy limit or original conditional integration. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerNumericalBank
open Finset Function Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise Comparison.RG02
open Comparison.RG02.Bulk Next.SectorChange Multi AllOrder AllOrder.Floe
open Further.PhysicalPeriodLimitF933 Macrame Shingle
open PhysicalNext.Repeat.Legato ActualRunCurvaturePackets NativeCurvatureTensor
open WilsonOriginalStarSceneWords WilsonOriginalStarGradedScene FVA1Physical.TwoReset
open WilsonThermometerFrozenCopies WilsonCoeffUV
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) {V T : Type} [DecidableEq V] [Fintype V]
  (d : V→ℕ) {n f : Side} (o : V→Site n) (σ g τ : ℝ)
  (v : (j:V)→R.family.label (d j)) (t : V→T→ℂ) (pos : ∀j, 0<d j)
local notation "M" => words R d o σ g τ v t pos

def bank (h : n.val ∣ f.val) (x : T) (L : Layout G) (pay : Finset Age) :
    Colors (Stock.census V) G f where
  vac := QuadraticLocal.Fk.money L pay
  power s := Launch.index (Stock.census V) d s.val+1
  mark s u U := ∑ p : Fin (Pages n f), ∑ j : Entry R d,
    if (Stock.census V).fire (root R d j) = s.val then
      WilsonThermometerFrozenCopies.word R d g τ v t j u x
        (page h (o (root R d j)) p).val U else 0

theorem same (h : n.val∣f.val) (x : T) (L : Layout G) (pay : Finset Age) :
    copyColor h M d (fun j=>(M j).paint x) L pay = bank R d o g τ v t h x L pay := by
  have read (s : Multi.Hot (Stock.census V)) (u : ℝ) (U : Config G f) :
      (copyColor h M d (fun j=>(M j).paint x) L pay).mark s u U =
       (bank R d o g τ v t h x L pay).mark s u U :=
    colored R d o σ g τ v t pos h x L pay s u U
  unfold copyColor bank
  congr 1
  funext s u U
  exact read s u U

end YM.Integration.WilsonThermometerNumericalBank
