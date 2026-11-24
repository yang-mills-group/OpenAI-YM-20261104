import YM.Integration.WilsonIndependentCollarShortHistory

/-! The ordinary face at one fixed fine address is one linear Wilson
coefficient history, including all younger interactions and proper faces. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarOrdinaryCruise
open Function Finset Lattice Wilson RG Precision
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Mer
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Winding
open WilsonCoeffUV.Embroider WilsonCoeffUV.Soil
open WilsonReceivedFixedDigitHistory
open scoped BigOperators Classical
variable {G:Gauge} {ι:Type} [Fintype ι] [DecidableEq ι] {D k:ι→ℕ}

def address (L:Levels G) (cells:Digits L ι):ℕ → ℕ → (ι → Cover) → (ι → Cover)
  | 0,_,y=>y
  | d+1,m,y=>address L cells d (m+1) (chartIn (loose L m) y (cells m))

theorem original (L:Levels G) (O:ChartRatio G) (simple:G.Simple) (localRatio:LocalRatio O)
    (N:ℕ) (cells:Digits L ι) (seed:Outerm G D) (well:Wellness k seed) (S:Finset ι)
    (f:Pen D S →L[ℝ] ℝ) (days m:ℕ) (y:ι → Cover) (cut:m+days≤N):
    tuftV f (levelsO (itinerary L O k N cells days m seed y) S)=
      cruises L O N (mass k S) (m+days) m
        (tuftV f (levelsO (seed (address L cells days m y)) S)):=by
  induction days generalizing m y with
  | zero=>simp [itinerary,address,cruises_top]
  | succ d ih=>
    let x:=chartIn (loose L m) y (cells m)
    let Y:=itinerary L O k N cells d (m+1) seed
    have hN:m<N:=by omega
    have inner:m+1+d≤N:=by omega
    have previous:=sound L O k N cells simple localRatio seed well d (m+1) inner
    have h:=step_S L O m N (Y x) k hN simple localRatio (previous.level' x)
    change tuftV f (levelsO (logO L O m N (Y x) k) S)=_
    rw [h]
    change tuftV f (verseI L O m N (mass k S) (levelsO (Y x) S))=_
    rw [ply_verse L hN simple localRatio (placedO (Y x) (previous.level' x) S) f]
    rw [cruises_sub L O N (mass k S) _ (show m < m+(d+1) by omega)]
    apply congrArg (verseI L O m N (mass k S))
    simpa only [address,show m+1+d=m+(d+1) by omega] using ih (m+1) x inner

end YM.Integration.WilsonIndependentCollarOrdinaryCruise
end
