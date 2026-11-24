import YM.Integration.WilsonOriginalTwoFlatRoseSingleSlot
import YM.Integration.WilsonIndependentCollarOrdinaryCruise

/-! Restrict a marked history at its initial printed stencils. An occupied
singleton has exactly the same finite response and source wage on either
roster, with the actual angular test evaluated at its own site. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatRoseRestrictedStart
open Function Finset Lattice Wilson RG Source Labels Marker
open WilsonCoeffUV WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Bank
open WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Blue WilsonCoeffUV.Soil
open OriginalMarkedSourceComet
open scoped Classical BigOperators


open WilsonCoeffUV.Mer WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Wheel.Motion
open WilsonCoeffUV.Shard WilsonCoeffUV.Embroider.Canvas WilsonCoeffUV.Winding
open IndependentSourcePathFamily
open Function Finset Lattice Wilson RG Precision
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Mer
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Winding
open WilsonCoeffUV.Embroider WilsonCoeffUV.Soil
open WilsonReceivedFixedDigitHistory
open scoped BigOperators Classical

open WilsonReceivedFixedDigitHistory WilsonIndependentCollarOrdinaryCruise

variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I]{D k:I→ℕ}
  {B:I→Type}[∀i,Fintype (B i)](X:(i:I)→B i→Seed G (D i))
  (t:Finset I)(A:Case D)(z:I→ Cover)(j:t)(n:Side)

private theorem dark (s:Finset I)(outs:∀i,s≠{i}):independent X z s=0:=
  sum_eq_zero fun i _=>dif_neg (Ne.symm (outs i))

theorem seen (paid:∀i b,(X i b).rank≤k i+(X i b).head):
    readO A (levelsO (independent X z) t) n=
      readO (fun a:t=>A a.val)
        (levelsO (independent (fun a:t=>X a.val) (fun a:t=>z a.val)) univ) n:=by
  classical
  have narrow:=legal (fun a:t=>X a.val) (fun a:t=>z a.val) (fun a b=>paid a.val b)
  rw [WilsonReceivedCanonicalSocketLevels.original _ (legal X z paid) (dark X z) A n t,
    WilsonReceivedCanonicalSocketLevels.original _ narrow (dark (fun a:t=>X a.val) (fun a:t=>z a.val)) _ n univ,
    ←prod_coe_sort t]
  exact prod_congr rfl fun a _=>WilsonOriginalTwoFlatRoseSingleSlot.original X t A z a n paid

theorem original (paid:∀i b,(X i b).rank≤k i+(X i b).head):
    tuftV (touch A t) (levelsO (independent X z) t)=
      tuftV (touch (fun a:t=>A a.val) univ)
        (levelsO (independent (fun a:t=>X a.val) (fun a:t=>z a.val)) univ):=by
  have p:=(placedO _ (legal X z paid) t).tuft (touch A t)
  have q:=(placedO _ (legal (fun a:t=>X a.val) (fun a:t=>z a.val) (fun a b=>paid a.val b)) univ).tuft
    (touch (fun a:t=>A a.val) univ)
  apply Auth.ext p q
  funext n
  exact by_flash (p.span n) (q.span n) (p.pale n) (q.pale n) (seen X t A z n paid)

omit [Fintype I] [DecidableEq I] in
theorem cells (L:Levels G)(trail:Digits L I)(age m:ℕ)(y:I→ Cover):
    address L (fun a (i:t)=>trail a i.val) age m (fun i:t=>y i.val)=
       fun i:t=>address L trail age m y i.val:=by
  induction age generalizing m y with
  | zero=>rfl
  | succ e ih=>exact ih (m+1) (chartIn (loose L m) y (trail m))

omit [Fintype I] [DecidableEq I] in
private theorem grade:mass (fun a:t=>k a.val) (univ:Finset t)=mass k t:=by
  change (∑a:t,k a.val)=∑a∈t,k a
  exact sum_coe_sort t _

theorem filed (paid:∀i b,(X i b).rank≤k i+(X i b).head)
    (L:Levels G)(O:ChartRatio G)(simple:G.Simple)(ratio:LocalRatio O)(N m age:ℕ)(bound:m+age≤N)
    (trail:Digits L I)(y:I→ Cover)
    (good:Wellness k (independent X))(restricted:Wellness (fun i:t=>k i.val) (independent (fun i:t=>X i.val))):
    tuftV (touch A t) (levelsO (itinerary L O k N trail age m (independent X) y) t)=
      tuftV (touch (fun a:t=>A a.val) univ)
        (levelsO (itinerary L O (fun a:t=>k a.val) N (fun a (i:t)=>trail a i.val) age m
          (independent (fun a:t=>X a.val)) (fun a:t=>y a.val)) univ):=by
  rw [WilsonIndependentCollarOrdinaryCruise.original L O simple ratio N trail _ good t _ age m y bound,
    WilsonIndependentCollarOrdinaryCruise.original L O simple ratio N _ _ restricted univ _ age m _ bound,
    grade t, cells t]
  exact congrArg (cruises L O N (mass k t) (m+age) m) (original X t A (address L trail age m y) paid)

end YM.Integration.WilsonOriginalTwoFlatRoseRestrictedStart
