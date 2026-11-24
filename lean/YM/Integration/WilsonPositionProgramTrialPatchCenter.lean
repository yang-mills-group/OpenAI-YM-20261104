import YM.Integration.WilsonPositionProgramTrialStoppedFace
import YM.Integration.WilsonPositionProgramTrialCenterHousing

/-! A single older cell translates all node tuples of an interpolation patch.
Its pivot is an actual site, independent of the differentiated node or the
deleted source labels. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialPatchCenter
open Finset Function Lattice RG Laurent Precision Wilson
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Soil WilsonCoeffUV.Mer WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Embroider WilsonCoeffUV.Blue WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Motion WilsonReceivedFixedDigitHistory
open WilsonPositionProgramTrialCellDigits WilsonPositionProgramTrialFixedDigits WilsonPositionProgramTrialStoppedFace
open scoped Classical BigOperators
variable {G : Gauge} {I : Type} [DecidableEq I] {D k : I → ℕ}

def augmented (pivot : Cover) (o : I → Cover) : Option I → Cover
  | none => pivot
  | some i => o i

def moved (S : Schedule) {w K : ℕ} (cut : w ≤ K) (pivot : Cover) (o : I → Cover) (i : I) :=
  residual S cut (augmented pivot o) none (some i)

omit [DecidableEq I] in
theorem housing (S : Schedule) {w K : ℕ} (cut : w ≤ K) (pivot : Cover) (o : I → Cover) (i : I) :
    ‖S.gridPoint K (moved S cut pivot o i)‖ ≤ S.a w+‖S.gridPoint K (o i-pivot)‖ :=
  WilsonPositionProgramTrialCenterHousing.original S cut (augmented pivot o) none (some i)

theorem original (L : Levels G) (O : ChartRatio G) (simple : G.Simple) (ratio : LocalRatio O)
    {w c K N : ℕ} (early : w ≤ c) (filed : c ≤ K) (top : K ≤ N) (seed : Outerm G D)
    (well : Wellness k seed) (moves : ∀ z, ramble z seed) (o : I → Cover) (pivot : Cover)
    (s : Finset I) (read : Pen D s →L[ℝ] ℝ) (e : ℕ) :
    stopped (k:=k) L O N filed seed (moved L.S (early.trans filed) pivot o) s read w e =
      stopped (k:=k) L O N filed seed o s read w e := by
  let v := -ancestor L.S (early.trans filed) (augmented pivot o) none
  let u := (L.S.toDepth early 0).count.val • v
  let a := parents L.S filed o
  let M := itinerary L O k N (cells L c K o) (K-c) c seed
  have active : c+(K-c) ≤ N := by omega
  have laws : Wellness k M := WilsonReceivedFixedDigitHistory.sound L O k N _ simple ratio seed well _ _ active
  have shift : ramble u M :=
    WilsonNeutralTwoPrintPathOldMotion.history L O N _ simple ratio seed well moves _ _ active u
  have raw : levelsO (M (steppedC u a)) s=shifted (levelsO (M a) s) u := by
    rw [shift a,composed0 _ (laws.level' a) (laws.quiet' a)]
    rfl
  have sameDigits : cells L c K (moved L.S (early.trans filed) pivot o)=cells L c K o := by
    funext j i
    change cells L c K (residual L.S _ (augmented pivot o) none) j (some i)=_
    rw [WilsonPositionProgramTrialFixedDigits.original L early filed]
    rfl
  have sameParents : parents L.S filed (moved L.S (early.trans filed) pivot o)=steppedC u a := by
    funext i
    exact congrFun (WilsonPositionProgramTrialFixedDigits.at_stop L early filed (augmented pivot o) none) (some i)
  unfold WilsonPositionProgramTrialStoppedFace.stopped returned
  rw [sameDigits,sameParents]
  change (cruises L O N (mass k s) c w (tuftV read (levelsO (M (steppedC u a)) s))).2 e 0 Fin.elim0=_
  rw [raw]
  exact WilsonPositionProgramTrialStoppedTranslation.emitted L simple ratio (filed.trans top) _
    ((placedO (M a) (laws.level' a) s).tuft read) early v e

end YM.Integration.WilsonPositionProgramTrialPatchCenter
