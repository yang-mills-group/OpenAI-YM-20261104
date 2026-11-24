import YM.Integration.WilsonAddressedAlignedPalette

/-! The charged aligned primary reproduces its literal filed upper vector before any integration. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedAlignedColumn
open Filter Lattice Wilson Labels RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Push.Local
open PhysicalNext.Repeat.Legato MergeProof Accent Trace.Physical Trace.Physical.GermGraph
open ProjectorNext.Equivariance Work.G08 Next.Rank
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open WilsonThermometerOwnOffsetField
open scoped BigOperators Classical Topology
variable {G:Gauge} (R:Run G) {k N p d:ℕ}
local notation "Rf" => R.family
local notation "T" => R.family.factory d N p
local notation "F" => R.family.labels.level d

def offer (x:(Rf).label d) (opened:Opened (Rf) d k p) (hk:k≤N):Palette (Rf) d:=
  chunk (primaryLetter d) (fitting d N p k R.makes opened hk
    ((((Rf).S.a k:ℂ)^d)⁻¹ • (T).terminal.symm x))

theorem original {b:ℕ} {D:Rail (Rf)} {B:ℕ→ℕ→ℝ} {V:Sight (Rf) d p} {r:Emblems (Rf) d}
    (enrolled:Enrolled R.makes D B b N p d (digits R N p 0) V r) (hk:k≤N) (entered:b≤k)
    (steps:∀e≤d,(Rf).ref e≤N) (opened:Opened (Rf) d k p) (x:(Rf).label d):
    let y:=offer R x opened hk
    ((Rf).S.a k:ℂ)^d • (T).terminal (finer r hk y (primaryLetter d))=x ∧
    size y≤2*(F).coeffSize (Price.awake (Rf) d k N p x):=by
  let a:ℂ:=((Rf).S.a k:ℂ)^d
  let v:=a⁻¹ • (T).terminal.symm x
  let h:=fitting d N p k R.makes opened hk
  let y:=offer R x opened hk
  let t:=primaryLetter d
  have paid:h (finer r hk y t)=y t:=WilsonAddressedAlignedPalette.primary R enrolled hk entered steps opened y
  have slot:y t=h v:=by change chunk (C:=Rf) t (h v) t=h v;rw [chunk_self]
  have bound: finer r hk y t=v:=h.injective (paid.trans slot)
  have nonzero:a≠0:=pow_ne_zero _ (Complex.ofReal_ne_zero.mpr ((Rf).S.a_pos k).ne')
  have cash:=size_gap d N p k R.makes opened hk v
  have based:(T).Based (Rf).params ((Rf).localSection d) ((Rf).ref d):=R.makes.calibrated d N p (opened.post.trans hk)
  have same:((T).entries k v).x=Price.awake (Rf) d k N p x:=(based.linear k opened.post hk).1.map_smul _ _
  refine ⟨?_,?_⟩
  · change a • (T).terminal (finer r hk y t)=x
    rw [bound];change a • (T).terminal (a⁻¹ • (T).terminal.symm x)=x
    rw [map_smul,LinearEquiv.apply_symm_apply,smul_smul,mul_inv_cancel₀ nonzero,one_smul]
  · change size (chunk t (h v))≤_
    rw [size_chunk]
    exact cash.1.trans_eq (congrArg (fun z=>2*(F).coeffSize z) same)

end YM.Integration.WilsonAddressedAlignedColumn
end
