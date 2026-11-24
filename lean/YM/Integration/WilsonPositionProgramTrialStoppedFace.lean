import YM.Integration.WilsonPositionProgramTrialFixedDigits
import YM.Integration.WilsonPositionProgramTrialStoppedTranslation
import YM.Integration.WilsonNeutralTwoPrintPathOldMotion

/-! Both stages read the same marked field and its original unmarked history.
First follow each registered fine site with its own prescribed child at every
step. Then continue the whole ordinary conditional through a second, older
date and extract its scalar at the selected perturbative order. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialStoppedFace
open Finset Function Lattice RG Laurent Precision Wilson
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Soil WilsonCoeffUV.Mer WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Embroider WilsonCoeffUV.Blue WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Motion WilsonReceivedFixedDigitHistory
open WilsonPositionProgramTrialCellDigits WilsonPositionProgramTrialFixedDigits
open scoped Classical BigOperators
variable {G : Gauge} {I : Type} [DecidableEq I] {D k : I → ℕ}

def returned (L : Levels G) (O : ChartRatio G) (N : ℕ) {c K : ℕ} (filed : c ≤ K)
    (seed : Outerm G D) (o : I → Cover) (s : Finset I) (read : Pen D s →L[ℝ] ℝ) : Era G ℝ :=
  tuftV read (levelsO (itinerary L O k N (cells L c K o) (K-c) c seed (parents L.S filed o)) s)

def stopped (L : Levels G) (O : ChartRatio G) (N : ℕ) {c K : ℕ} (filed : c ≤ K)
    (seed : Outerm G D) (o : I → Cover) (s : Finset I) (read : Pen D s →L[ℝ] ℝ)
    (w e : ℕ) : ℝ :=
  (cruises L O N (mass k s) c w (returned (k:=k) L O N filed seed o s read)).2 e 0 Fin.elim0

theorem original (L : Levels G) (O : ChartRatio G) (simple : G.Simple) (ratio : LocalRatio O)
    {w c K N : ℕ} (early : w ≤ c) (filed : c ≤ K) (upper : K ≤ N) (seed : Outerm G D)
    (well : Wellness k seed) (moves : ∀ z, ramble z seed) (o : I → Cover)
    (anchor : I) (s : Finset I) (read : Pen D s →L[ℝ] ℝ) (e : ℕ) :
    stopped (k:=k) L O N filed seed (residual L.S (early.trans filed) o anchor) s read w e =
      stopped (k:=k) L O N filed seed o s read w e := by
  let v := -ancestor L.S (early.trans filed) o anchor
  let u := (L.S.toDepth early 0).count.val • v
  let a := parents L.S filed o
  let M := itinerary L O k N (cells L c K o) (K-c) c seed
  have top : c+(K-c) ≤ N := by omega
  have laws : Wellness k M := WilsonReceivedFixedDigitHistory.sound L O k N _ simple ratio seed well _ _ top
  have shift : ramble u M :=
    WilsonNeutralTwoPrintPathOldMotion.history L O N _ simple ratio seed well moves _ _ top u
  have sale : levelsO (M (steppedC u a)) s=shifted (levelsO (M a) s) u := by
    rw [shift a,composed0 _ (laws.level' a) (laws.quiet' a)]
    rfl
  unfold stopped returned
  rw [WilsonPositionProgramTrialFixedDigits.original _ early filed o anchor,
    WilsonPositionProgramTrialFixedDigits.at_stop _ early filed o anchor]
  change (cruises L O N (mass k s) c w (tuftV read (levelsO (M (steppedC u a)) s))).2 e 0 Fin.elim0=_
  rw [sale]
  change (cruises L O N (mass k s) c w (shifted (tuftV read (levelsO (M a) s)) u)).2 e 0 Fin.elim0=_
  exact WilsonPositionProgramTrialStoppedTranslation.emitted L simple ratio (filed.trans upper) _
    ((placedO (M a) (laws.level' a) s).tuft _) early v e

end YM.Integration.WilsonPositionProgramTrialStoppedFace
