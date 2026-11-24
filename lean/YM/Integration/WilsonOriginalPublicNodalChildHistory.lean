import YM.Integration.WilsonReceivedFixedDigitFinite

/-! The ordinary field of an individual located child receives the full original vacuum on every earlier step. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalChildHistory
open Function Finset Lattice RG Wilson Precision Laurent Source Labels Marker
open WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Cosmos WilsonFiniteMarkedHistoryStep
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Winding
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Blue WilsonCoeffUV.Bank
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Soil WilsonCoeffUV.Embroider
open WilsonReceivedFixedDigitHistory (Digits itinerary sound)
open scoped BigOperators Classical
variable {G:Gauge}{I:Type}[DecidableEq I]{D:I→ℕ}

def site (V:Levels G)(c:Digits V I):(days m:ℕ)→(I → Cover)→(I → Cover)
  | 0,_,x=>x
  | days+1,m,x=>site V c days (m+1) (chartIn (loose V m) x (c m))

theorem original (V:Levels G)(O:ChartRatio G)(k:I→ℕ)(Y:Outerm G D)
    (simple:G.Simple)(ratio:LocalRatio O)(well:Wellness k Y)(N:ℕ)(c:Digits V I)
    (days m:ℕ)(live:m+days≤N)(x:I → Cover)(s:Finset I)(f:Pen D s→L[ℝ]ℝ):
    tuftV f (levelsO (itinerary V O k N c days m Y x) s)=
      cruises V O N (mass k s) (m+days) m (tuftV f (levelsO (Y (site V c days m x)) s)):=by
  induction days generalizing m x with
  | zero=>rw [Nat.add_zero,cruises_top];rfl
  | succ days ih=>
    let y:=chartIn (loose V m) x (c m)
    let U:=itinerary V O k N c days (m+1) Y
    have hi:m<N:=by omega
    have bound:m+1+days≤N:=by omega
    have paid:=sound V O k N c simple ratio Y well days (m+1) bound
    have step:=step_S V O m N (U y) k hi simple ratio (paid.level' y)
    have fee:=placedO (U y) (paid.level' y) s
    have previous:=ih (m+1) bound y
    change tuftV f (levelsO (logO V O m N (U y) k) s)=_
    rw [step]
    change tuftV f (verseI V O m N (mass k s) (levelsO (U y) s))=_
    rw [ply_verse V hi simple ratio fee f,previous]
    have movement : m < m + (days+1):=by omega
    rw [cruises_sub V O N (mass k s) _ movement]
    rw [show m+1+days=m+(days+1) by omega]
    rfl

end YM.Integration.WilsonOriginalPublicNodalChildHistory
end
