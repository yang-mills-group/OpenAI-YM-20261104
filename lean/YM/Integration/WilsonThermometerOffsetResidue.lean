import YM.Integration.WilsonThermometerOffsetCylinder
import YM.Next.RANK.Coordinates

/-! Use the intrinsic ancestors and residues of an arbitrary cutoff site.
The resulting word of actual child translations has that physical endpoint. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerOffsetResidue
open Function Set Lattice Wilson Labels RG Source Extra.Histories RG05Readout Address Records
open Push.GridApprox PhysicalNext.Repeat.Legato WilsonThermometerOffsetCylinder
open scoped Classical
variable {G : Gauge} (R : Run G) (N p m : ℕ)

def digits (z : Site (R.family.side N p)) (i : ℕ) : Bud R.family p i :=
  if h : i+1≤N then
    (R.family.path.levels.clock.op i p).ratio.residue ((R.family.S.toDepth h p).parent z)
  else 0

theorem partialSum (z : Site (R.family.side N p)) (q : ℕ) (live : m+q≤N) :
    address R N p m (digits R N p z) q live +
      anchor R.family.S p (show m≤N by omega) ((R.family.S.toDepth (by omega : m≤N) p).parent z) =
      anchor R.family.S p live ((R.family.S.toDepth live p).parent z) := by
  induction q with
  | zero => rw [address,zero_add]
  | succ q ih =>
    let S := R.family.S
    let K := (R.family.path.levels.clock.op (m+q) p).ratio
    let h₀ : m+q≤N := by omega
    let hi := (S.toDepth live p).parent z
    let lo := (S.toDepth h₀ p).parent z
    have nested : lo=K.parent hi := Next.Rank.Station.parent_nested K (S.toDepth live p) (S.toDepth h₀ p)
      (S.block_odd _) (S.toDepth_odd live p) z
    have atStep : digits R N p z (m+q) = K.residue hi := by
      unfold digits; rw [dif_pos (show m+q+1≤N by omega)]
    have delta : child R.family p (m+q) (digits R N p z (m+q)) = Lattice.wrap _ (lift (K.residue hi)) := by
      rw [atStep]
      change K.embed 0+_= _
      rw [show K.embed 0=0 from K.root.map_zero,zero_add]
    have unpacked : K.embed lo + child R.family p (m+q) (digits R N p z (m+q))=hi := by
      rw [delta,nested]; exact K.unpack_at hi
    have first : anchor S p h₀ lo = anchor S p live (K.embed lo) :=
      Next.Rank.Station.embed_comp K (S.toDepth live p) (S.toDepth h₀ p) lo
    have sum (a b : Site (R.family.side (m+q+1) p)) :
        anchor S p live (a+b) = anchor S p live a + anchor S p live b :=
      (S.toDepth live p).root.map_add a b
    rw [address,add_right_comm,ih h₀]
    change anchor S p h₀ lo+anchor S p live _ = anchor S p live hi
    rw [first,←sum,unpacked]

theorem original (q : ℕ) (z : Site (R.family.side (m+q) p)) :
    address R (m+q) p m (digits R (m+q) p z) q le_rfl +
      anchor R.family.S p (Nat.le_add_right m q)
        ((R.family.S.toDepth (Nat.le_add_right m q) p).parent z) = z := by
  let A := R.family.S.toDepth (le_refl (m+q)) p
  have same (x : Site (R.family.side (m+q) p)) : A.embed x = x :=
    like_embed (C:=R.family) (N:=m+q) (p:=p) x
  have parent : A.parent z=z :=
    (congrArg A.parent (same z).symm).trans (A.embed_parent z)
  exact (partialSum R (m+q) p m z q le_rfl).trans ((same (A.parent z)).trans parent)

end YM.Integration.WilsonThermometerOffsetResidue
end
