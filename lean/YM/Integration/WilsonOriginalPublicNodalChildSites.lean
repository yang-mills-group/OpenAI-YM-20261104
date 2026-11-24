import YM.Integration.WilsonOriginalPublicNodalChildHistory

/-! Each original cover site determines all of its genuine children on the fixed interval. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalChildSites
open Function Finset Lattice RG Wilson Precision Laurent Source Labels Marker
open WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Cosmos WilsonFiniteMarkedHistoryStep
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Winding
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Blue WilsonCoeffUV.Bank
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Soil WilsonCoeffUV.Embroider
open WilsonReceivedFixedDigitHistory (Digits itinerary)
open WilsonOriginalPublicNodalChildHistory (site)
open scoped BigOperators Classical
variable {G:Gauge}{I:Type}[DecidableEq I]{D:I→ℕ}

def here (V:Levels G)(K:ℕ)(z:I → Cover)(m:ℕ):I → Cover:=
  if hm:m<K then fun i=>parentC (loose V m).L (here V K z (m+1) i) else z
termination_by K-m

def digits (V:Levels G)(K:ℕ)(z:I → Cover):Digits V I:=
  fun m i=>wrap (loose V m).L (here V K z (m+1) i)

omit [DecidableEq I] in
theorem next (V:Levels G)(K:ℕ)(z:I → Cover){m:ℕ}(lower:m<K):
    chartIn (loose V m) (here V K z m) (digits V K z m)=here V K z (m+1):=by
  funext i
  conv_lhs => unfold chartIn;rw [here,dif_pos lower]
  exact heapZ_eq (loose V m) _

omit [DecidableEq I] in
theorem climb (V:Levels G)(K:ℕ)(z:I → Cover)(days m:ℕ)(prior:m+days≤K):
    site V (digits V K z) days m (here V K z m)=here V K z (m+days):=by
  induction days generalizing m with
  | zero=>rfl
  | succ days ih=>
    rw [site,next V K z (by omega),ih (m+1) (by omega)]
    rw [show m+1+days=m+(days+1) by omega]

theorem original (V:Levels G)(O:ChartRatio G)(k:I→ℕ)(Y:Outerm G D)
    (simple:G.Simple)(ratio:LocalRatio O)(well:Wellness k Y)(N K m:ℕ)
    (before:m≤K)(top:K≤N)(z:I → Cover)(s:Finset I)(f:Pen D s→L[ℝ]ℝ):
    tuftV f (levelsO (itinerary V O k N (digits V K z) (K-m) m Y (here V K z m)) s)=
      cruises V O N (mass k s) K m (tuftV f (levelsO (Y z) s)):=by
  have height:m+(K-m)=K:=by omega
  rw [WilsonOriginalPublicNodalChildHistory.original V O k Y simple ratio well N _ (K-m) m (by omega),
    climb V K z (K-m) m (by omega),height,here, dif_neg (Nat.lt_irrefl K)]

end YM.Integration.WilsonOriginalPublicNodalChildSites
end
