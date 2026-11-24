import YM.Integration.WilsonOlderFreshSoftOrdinary
import YM.Integration.WilsonOlderFreshSoftSocketHistory
import YM.Integration.WilsonReceivedFixedDigitHistory
import YM.WilsonCoeffUV.Product.Report.Shapes

/-! Ordinary fields on a fixed sequence of physical children under their original cutoff vacuum. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalTestedCore
open Precision Function Finset Lattice Wilson RG Source Labels Marker WilsonCoeffUV
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp
open WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Blue WilsonCoeffUV.Soil
open WilsonCoeffUV.Embroider WilsonCoeffUV.Winding WilsonFiniteMarkedHistoryStep
open WilsonReceivedFixedDigitHistory (Digits itinerary sound)
open scoped Classical BigOperators

variable {G:Gauge}{I:Type}[DecidableEq I][Fintype I]{D:I→ℕ}
variable (L:Levels G)(O:ChartRatio G)(d:I→ℕ)(N:ℕ)(cells:Digits L I)

def roots : ℕ → ℕ → (I → Cover) → (I → Cover)
  | 0, _, y=>y
  | days+1, m, y=>roots days (m+1) (chartIn (loose L m) y (cells m))

theorem step (simple:G.Simple)(localO:LocalRatio O)(Y:Outerm G D)(real:Wellness d Y)
    (S:Finset I)(test:Pen D S→L[ℝ] ℝ)(days m:ℕ)(top:m+days≤N)(y:I → Cover):
    tuftV test (levelsO (itinerary L O d N cells days m Y y) S)=
      cruises L O N (mass d S) (m+days) m
        (tuftV test (levelsO (Y (roots L cells days m y)) S)):=by
  induction days generalizing m y with
  | zero=>simp only [Nat.add_zero,roots,itinerary,cruises_top]
  | succ days ih=>
    let o:=chartIn (loose L m) y (cells m)
    let Z:=itinerary L O d N cells days (m+1) Y
    have good:=sound L O d N cells simple localO Y real days (m+1) (by omega)
    have paid:Eu d (Z o):=good.level' o
    change tuftV test (levelsO (logO L O m N (Z o) d) S)=_
    rw [step_S L O m N (Z o) d (by omega) simple localO paid]
    change tuftV test (verseI L O m N (mass d S) (levelsO (Z o) S))=_
    rw [ply_verse L (by omega) simple localO (placedO _ paid S)]
    rw [cruises_sub _ _ _ _ _ (show m < m + (days+1) by omega)]
    congr 1
    simpa only [Z,roots,o,show m+1+days = m+(days+1) by omega] using ih (m+1) (by omega) o

theorem original (simple:G.Simple)(localO:LocalRatio O)(Y:Outerm G D)(real:Wellness d Y)
    (v c K:ℕ)(vc:v≤c)(cK:c≤K)(KN:K≤N)(y:I → Cover)(S:Finset I)(test:Pen D S→L[ℝ] ℝ):
    cruises L O N (mass d S) c v
        (WilsonOlderFreshSoftOrdinary.material D d L O Y N cells c K y S test)=
      cruises L O N (mass d S) K v
        (tuftV test (levelsO (Y (roots L cells (K-c) c y)) S)):=by
  have hk:c+(K-c)=K:=by omega
  have edge:=step L O d N cells simple localO Y real S test (K-c) c (by omega) y
  rw [hk] at edge
  rw [WilsonOlderFreshSoftOrdinary.material,edge,←cruisesMore L O _ vc cK]

end YM.Integration.WilsonOriginalPublicNodalTestedCore
end
