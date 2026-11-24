import YM.Integration.WilsonOriginalNullHouse
import YM.FullVolume.Nectar.Ritz
import YM.RelayRG.Cycle.Ratio

/-! The signed coefficient of the real marked course at its original cluster. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalNullWord
open Function Filter Set Lattice RG Pressure Tree Wilson Finset MeasureTheory
open PhysicalNext Repeat Legato Graces
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost Lotus Blush Mallow
open UVNext.CouplingReset Animals Marlin Progress.DirectedRecipe Ovens Ovens.Pipes
open Extra.Histories Next.Foundations Labels Peak Mercury
open AllOrder AllOrder.Transit WheelP AllOrder.Floe
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

open Merge Merge.Palette
variable {G : Gauge} (R : Run G) {N per i : ℕ}
    (Ψ : ∀ j, RG.Rep G (R.family.side j per))

theorem grouped (live : i < N)
    (S : Mallow.Spring R.kit N i per 0 0 (fun _ => Ψ (i+1)))
    {I : Type} [Fintype I] (rows : I → Lotus.Leaf (Ψ (i+1))) (w : I → ℝ) :
    let K := Mallow.houseS S WilsonOriginalNullHouse.point
    ∀ j : I, ∀ z : K.fragrances, ∀ V : Config G (R.family.side i per),
      Switch.jet (Photo.tones rows K Chi.canonical w z V) {j} =
        w j * RG.masked (Pressure.temp (R.alloy.B.a.clock.hatBeta i))
          (K.bookFoot (.inr z)) (matin (rows j) K z Chi.canonical) V := by
  intro K j z V
  have stage := step_paid R.alloy.B.a i
  have ticket := R.b.r _ _ (R.alloy.B.valid.pays i) _ stage |>.1.2
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, cap, herd⟩ :=
    ticket _ _ _ _ (Opera.protocol R.alloy.B live R.kit.pledging.conducts.full (n:=per)) _ _ K
  have symbol := ((podE K rows V Chi.canonical z).1 w).choose_spec
  have h := Luna.Frets.reacts K rows w cap herd j z V 0 symbol
  rw [Daisy.Charity.mask_ag] at h
  exact h

end YM.Integration.WilsonOriginalNullWord
