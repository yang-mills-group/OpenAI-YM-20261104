import YM.WilsonCoeffUV.Horizon.OrbitShift
import YM.Integration.WilsonReceivedFixedDigitIntake
import YM.Integration.WilsonNeutralTwoPrintPathInheritedBlocks
import YM.Integration.WilsonPointChildCenteredSeat

/-! Reissuing the finite catalogue of whole previous depositions preserves
its actual finite-period coefficients before the next Gaussian integral. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace YM.Integration.WilsonNeutralTwoPrintPathInheritedMotion
open Function Finset Filter Lattice RG Laurent Wilson
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Blue
open WilsonCoeffUV.Soil WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Winding
open WilsonCoeffUV.Shard WilsonCoeffUV.Embroider.Canvas WilsonCoeffUV.Cosmos
open WilsonReceivedCompactVerseEntrance (CoverBill submit)
open WilsonNeutralTwoPrintPathInherited (atom)
open WilsonNeutralTwoPrintPathInheritedBlocks (gathered amount)
open private translated from YM.Integration.WilsonPointChildCenteredSeat
open private center from YM.Integration.WilsonNeutralTwoPrintPathInherited
open scoped Classical BigOperators

open Precision Tree Exterior Bloch Work.F08
open WilsonCoeffUV.Wheel.Motion (steppedC raised0 ramble alongShift)
open WilsonNeutralTwoPrintPathRebadge (table)
open WilsonReceivedFixedDigitIntake (next)
variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I]{D k:I→ℕ}

theorem seated (T:(i:I)→TowerS G (D i))(w:Cover):ramble w (table T):=by
  intro y
  funext S
  by_cases hit:∃i,S={i}
  · obtain ⟨i,rfl⟩:=hit
    change table T (steppedC w y) {i}=shifted (table T y {i}) w
    rw [WilsonNeutralTwoPrintPathRebadge.one,WilsonNeutralTwoPrintPathRebadge.one]
    exact shifted_add _ _ _
  · have away:∀i,S≠{i}:=fun i h=>hit ⟨i,h⟩
    change table T (steppedC w y) S=shifted (table T y S) w
    rw [WilsonNeutralTwoPrintPathRebadge.dark _ _ _ away,WilsonNeutralTwoPrintPathRebadge.dark _ _ _ away]
    rfl

theorem original (L:Levels G)(O:ChartRatio G)(j N:ℕ)(arrived:j<N)(simple:G.Simple)(rat:LocalRatio O)
    (T:(i:I)→TowerS G (D i))(healthy:Wellness k (table T))(digit:I→Site (loose L j).L)
    (S:Finset I)(y z:I → Cover)(v:Cover)(moving:∀i∈S,z i=v+y i):
    (next L O j N k (table T) digit z S)=shifted (next L O j N k (table T) digit y S) v:=by
  have outside:next L O j N k (table T) digit z S=
      next L O j N k (table T) digit (steppedC v y) S:=
    (WilsonReceivedFixedDigitIntake.lawful L O j N k (table T) digit simple rat arrived healthy).filial _ _ S moving
  rw [outside]
  change logO L O j N (table T (chartIn (loose L j) (steppedC v y) digit)) k S=_
  have moved:chartIn (loose L j) (steppedC v y) digit=
      steppedC ((L.S.block j).val • v) (chartIn (loose L j) y digit):=by
    funext i
    change (L.S.block j).val • (v+y i)+_=(L.S.block j).val • v+((L.S.block j).val • y i+_)
    rw [nsmul_add,add_assoc]
  rw [moved]
  exact congrFun (alongShift (A:=L) (Ñ:=O) healthy arrived simple rat (seated T _) (chartIn (loose L j) y digit)) S

theorem period (L:Levels G)(O:ChartRatio G)(j N:ℕ)(arrived:j<N)(simple:G.Simple)(rat:LocalRatio O)
    (T:(i:I)→TowerS G (D i))(healthy:Wellness k (table T))(digit:I→Site (loose L j).L)
    (S:Finset I)(y z:I → Cover)(v:Cover)(moving:∀i∈S,z i=v+y i)(b:Side)(hidden:wrap b v=0)(e r:ℕ):
    plume ((next L O j N k (table T) digit z S).2 e r) b=
      plume ((next L O j N k (table T) digit y S).2 e r) b:=by
  rw [original L O j N arrived simple rat T healthy digit S y z v moving]
  change plume (revolve v _) b=_
  rw [translated,hidden]
  funext x
  have same:jog (-(0:Site b)) ∘ x=x:=by
    funext i
    ext <;> simp [jog]
  exact congrArg (plume ((next L O j N k (table T) digit y S).2 e r) b) same

end YM.Integration.WilsonNeutralTwoPrintPathInheritedMotion
end
