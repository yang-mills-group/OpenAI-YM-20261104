import YM.Integration.WilsonSeparatedPrefixCanonicalZeroPost
import YM.Integration.WilsonOriginalGalleryTwinsField

/-! Restore the constant part of every named soft field on all physical configurations.
The duplicated original hard inventory is kept inside the same compatible partition sum. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixCanonicalRestore
open Finset Function Lattice Wilson RG Ac Marker Push GridApprox.Nil QuadraticLocal MergeProof MergeProof.Accent
open Extra.Histories Extra.Multi Extra.Trajectories Lodestar
open scoped BigOperators Classical
variable {V:Type}[DecidableEq V][Fintype V]{G:Gauge}{n:Side}(P:Rep G n)
variable (φ:V → Config G n → ℂ)(h:V → Box n → Config G n → ℂ)
  (mixHead:Support n → Config G n → Poly (Marks V)) (mixOwner:Box n → Config G n → Poly (Marks V))
  (topConst:V → Poly (Marks V))(softPart:V → Support n → Config G n → Poly (Marks V))

theorem original (quiet:∀i,(topConst i).part (Marks V).quiet=0)
    (sil:∀i Z U,(softPart i Z U).part (Marks V).quiet=0)(pure:∀Z U,(mixHead Z U).part (Marks V).quiet=0)
    (split:∀i U,Poly.send ((Marks V).fire i) (φ i U)=topConst i+∑Z,softPart i Z U)(U:Config G n):
    duplicate V (restore P φ h mixHead mixOwner U)=duplicate V (Poly.pass (∑i,topConst i))*
      restore P (fun (_:V×Bool) _=>0) (fun (_:V×Bool) _ _=>0) (fun Z U=>(∑i,duplicate V (softPart i Z U))+duplicate V (mixHead Z U)) (fun b U=>(∑i,duplicate V (Poly.send ((Marks V).fire i) (h i b U)))+duplicate V (mixOwner b U)) U := by
  let R:Poly (Marks V):=∑Z,((∑i,softPart i Z U)+mixHead Z U)
  have gram:(∑i,topConst i).part (Marks V).quiet=0:=by rw [Poly.part_sum];exact sum_eq_zero (fun i _=>quiet i)
  have root:R.part (Marks V).quiet=0:=by
    unfold R
    simp only [Poly.part_sum,Poly.part_plus,sil,pure,sum_const_zero,add_zero]
  have refile:Mach (Marks V) (fun i=>φ i U)+(∑Z,mixHead Z U)=(∑i,topConst i)+R:=by
    unfold Mach R
    have swap:(∑i,∑Z,softPart i Z U)=∑Z,∑i,softPart i Z U:=sum_comm
    simp_rw [split]
    rw [sum_add_distrib,sum_add_distrib,swap]
    abel
  have regroup:duplicate V R=∑Z,(fun Z U=>(∑i,duplicate V (softPart i Z U))+duplicate V (mixHead Z U)) Z U:=by simp [R,map_sum]
  let B:=fun b=>bar P.activities (Marks V) U b+Mach (Marks V) (fun i=>h i b U)+mixOwner b U
  have flag (b:Box n):duplicate V (B b)=bar P.activities (Marks (V×Bool)) U b+(fun b U=>(∑i,duplicate V (Poly.send ((Marks V).fire i) (h i b U)))+duplicate V (mixOwner b U)) b U:=by
    have bar0:duplicate V (bar P.activities (Marks V) U b)=bar P.activities (Marks (V×Bool)) U b:=by
      change duplicate V (Poly.send (Marks V).quiet _) = _
      rw [seal_send,two_quiet]
      rfl
    simp only [B,map_add,bar0,Mach,map_sum]
    abel
  have gas:duplicate V (field B (flags P.p.threshold U))=field (fun b=>duplicate V (B b)) (flags P.p.threshold U):=by
    unfold field
    rw [map_sum]
    apply sum_congr rfl
    intro l _
    unfold grid
    split
    · exact map_prod .. 
    exact map_zero ..
  have nil:Mach (Marks (V×Bool)) (fun _=>0)=0:=by simp [Mach]
  unfold restore
  simp only [nil,zero_add,add_zero]
  change duplicate V ((Real.exp (P.exponent U):ℂ) •
      (Poly.pass (Mach (Marks V) (fun i=>φ i U)+∑Z,mixHead Z U)*field B _))=_
  rw [map_smul,map_mul,refile,pass_add gram root,map_mul,seal_pass _ root,regroup,gas,funext flag,mul_smul_comm]
  rw [mul_assoc]

end YM.Integration.WilsonSeparatedPrefixCanonicalRestore
end
