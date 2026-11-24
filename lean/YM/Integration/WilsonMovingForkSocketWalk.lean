import YM.Integration.WilsonMovingForkSocketPhysicalDigits
import YM.Integration.WilsonMovingForkSocketScalar
import YM.Integration.WilsonOriginalPublicNodalTestedCore

/-! The actual bounded original child itinerary reads the nominated integer site. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000
noncomputable section
namespace YM.Integration.WilsonMovingForkSocketWalk
open Lattice Wilson RG WilsonCoeffUV.Bank
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonOriginalPublicNodalChildSites (here)
open WilsonIndependentCollarOrdinaryCruise (address)
open WilsonOriginalPublicNodalTestedCore (roots)
open WilsonReceivedChronologicalMaterialSites (digits)
open PhysicalNext.Repeat.Legato
open scoped Classical
variable {G:Gauge}{I:Type}

theorem path (L:Levels G)(K:ℕ)(z:I → Cover)(t:Digits L I)
    (file:∀j,j<K→t j=WilsonOriginalPublicNodalChildSites.digits L K z j)(days m:ℕ)(live:m+days≤K):
    address L t days m (here L K z m)=here L K z (m+days):=by
  induction days generalizing m with
  | zero=>rfl
  | succ days ih=>
    rw [address,file m (by omega),WilsonOriginalPublicNodalChildSites.next L K z (by omega),ih (m+1) (by omega)]
    rw [show m+1+days=m+(days+1) by omega]

theorem same (L:Levels G)(t:Digits L I)(days m:ℕ)(x:I → Cover):
    roots L t days m x=address L t days m x:=by
  induction days generalizing m x with
  | zero=>rfl
  | succ days ih=>exact ih _ _

theorem original (R:Run G){n K c v per:ℕ}(vc:v≤c)(ck:c≤K)(z:Fin n → Cover)
    (center:here R.family.path.levels K z v=0):
    let L:=R.family.path.levels
    let t:=digits R (fun i=>wrap (R.family.side K per) (z i))
    let y:=address L t (c-v) v 0
    y=here L K z c ∧ roots L t (K-c) c y=z:=by
  let L:=R.family.path.levels
  let t:=digits R (fun i=>wrap (R.family.side K per) (z i))
  have marked (j:ℕ)(lower:j<K):t j=WilsonOriginalPublicNodalChildSites.digits L K z j:=
    WilsonMovingForkSocketPhysicalDigits.filed R lower per z
  have first:address L t (c-v) v 0=here L K z c:=by
    rw [←center,path L K z t marked (c-v) v (by omega),Nat.add_sub_of_le vc]
  refine ⟨first,?_⟩
  change roots L t (K-c) c (address L t (c-v) v 0)=z
  rw [first,same,path L K z t marked (K-c) c (by omega),Nat.add_sub_of_le ck,here,dif_neg (Nat.lt_irrefl K)]

end YM.Integration.WilsonMovingForkSocketWalk
end
