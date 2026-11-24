import YM.Integration.WilsonOriginalPublicNodalChildSites
import YM.WilsonCoeffUV.Marked.Capture.AtSensor

/-! Fixed-child expansion on each occupied cell of an enrolled spatial test, including all previous vacuum coefficients. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalProfiles
open Function Finset Lattice RG Wilson Precision Source Labels Marker
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.Mosaic.Near
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Flooring
open WilsonCoeffUV.Soil WilsonCoeffUV.Embroider WilsonCoeffUV.Embroider.Canvas
open WilsonReceivedFixedDigitHistory (itinerary)
open WilsonOriginalPublicNodalChildSites (digits here)
open scoped BigOperators Classical
variable {G:Gauge}

theorem sum {B:Type}(V:Levels G)(O:ChartRatio G)(simple:G.Simple)(ratio:LocalRatio O)
    (N K m k:ℕ)(before:m≤K)(top:K≤N)(T:Finset B)(v:B→ℝ)(X:B→Era G ℝ)
    (paid:∀i∈T,Auth k (X i)):
    cruises V O N k K m (∑i∈T,v i • X i)=∑i∈T,v i • cruises V O N k K m (X i):=by
  induction before using Nat.decreasingInduction with
  | self=>simp only [cruises_top]
  | of_succ m ht ih=>
    rw [cruises_sub V O N k _ ht,ih]
    rw [verse_sum V simple (ht.trans_le top) ratio (S:=T)
      (fun i hi=>cruising V simple ratio ht top (paid i hi)) v]
    exact Finset.sum_congr rfl fun i _=>congrArg (v i • ·) (cruises_sub V O N k (X i) ht).symm

variable {I:Type}[DecidableEq I][Fintype I]{D:I→ℕ}

def returns (V:Levels G)(O:ChartRatio G)(k:I→ℕ)(Y:Outerm G D)(N K m:ℕ)
    (u y:ℝ)(o:CellR)(F:Garland D):Era G ℝ:=
  ∑ z∈boxes u y F, lyric u k • tuftV (touch (lyra u y o F z) Finset.univ)
    (levelsO (itinerary V O k N (digits V K z) (K-m) m Y (here V K z m)) Finset.univ)

theorem original (V:Levels G)(O:ChartRatio G)(simple:G.Simple)(ratio:LocalRatio O)
    (k:I→ℕ)(Y:Outerm G D)(well:Wellness k Y)(N K m:ℕ)(before:m≤K)(top:K≤N)
    (u y:ℝ)(o:CellR)(F:Garland D):
    returns V O k Y N K m u y o F=cruises V O N (fullK k) K m (Finale u y o F k (AuthSum Y)):=by
  let field := scrollR u y o F (AuthSum Y)
  have paid(z):Auth (fullK k) (field z):=(placedO _ (well.level' z) Finset.univ).tuft _
  change _=cruises V O N (fullK k) K m (∑z∈boxes u y F,lyric u k • field z)
  rw [sum V O simple ratio N K m _ before top _ _ _ (fun z _=>paid z)]
  unfold returns
  apply Finset.sum_congr rfl
  intro z _
  exact congrArg (lyric u k • ·) (WilsonOriginalPublicNodalChildSites.original V O k Y simple ratio well N K m before top z Finset.univ _)

end YM.Integration.WilsonOriginalPublicNodalProfiles
end
