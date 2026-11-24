import YM.AlbaMS.Cutis.Render
import Mathlib.Analysis.Matrix.Order
/-!
# standard kinetic & response in precision orientation

The H data invert on exactly complement Landau. Lagrangian means transverse A
and longitudinal K. Density scale a just changes physical units; orthogonal
directions in Euclidean basis on graph variables as in Book price. Means only
enter projected-full proof. Check use strict positivity (already posSemidef from
actual Energy proof). Volume units ordinary Euclidean matrix.

Physical check does not assert positivity when not reality (coeff-germs only).
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Cutis
open Set Function Filter LinearMap Matrix
open scoped BigOperators Classical Topology Matrix InnerProductSpace ENNReal
open Bric Loft Inlay Inlay.Net Odom Lattice Nexus
variable {V E B R S : Type*} {G:Gauge}[Fintype E][Fintype B][CommRing R][CommRing S]
namespace Fritz
-- transports and algebra scalars
variable (P: Lot E B R)(F:Fritz E B R)(M:R→+*S)
def replic : Fritz E B S:=⟨F.H.map M,F.U.map M,fun i j=> congr_arg M (F.symm i j)⟩
def scale (r t:R): Fritz E B R:=⟨r • F.H,t • F.U, fun i j=> by rw [Matrix.smul_apply,Matrix.smul_apply, F.symm]⟩
omit [Fintype E] [Fintype B] [CommRing R] in
lemma H_t : F.Hᵀ=F.H:=Matrix.ext fun i j=> F.symm j i
variable [DecidableEq E][DecidableEq B]
structure Normal (F:Fritz E B R)(P: Lot E B R):Prop extends Fund P F where
 nilg : P.Z* P.X=0
 transverse : F.H * P.X=0
 orthog : (P.X * F.Uᵀ)ᵀ=P.X*F.Uᵀ
noncomputable abbrev boom : Matrix E E R:= P.X * F.Uᵀ
namespace Normal
variable {F P} (h:Normal F P)
include h

lemma tapX : (F.boom P) * P.X=P.X:=by rw [boom,Matrix.mul_assoc, h.long,Matrix.mul_one]
lemma tapK : (F.boom P)*F.U=F.U:=by unfold boom; rw [← h.orthog,transpose_mul,transpose_transpose, Matrix.mul_assoc]; rw [show P.Xᵀ*F.U=1 from by nth_rw 1 [← transpose_transpose F.U];rw [← transpose_mul,h.long,transpose_one],Matrix.mul_one]
lemma sub_inv : F.H* P.Z=1-F.boom P:=by have h:= h.resonance; rw [P.Z_sym] at h; exact eq_sub_of_add_eq' h
lemma sub_left : P.Z*F.H=1-F.boom P:=by nth_rw 1 [← F.H_t,← P.Z_sym];rw [← transpose_mul,h.sub_inv,transpose_sub,h.orthog,transpose_one]
lemma first_dot : (1-F.boom P)* F.H=F.H:=by
  have hv:F.boom P * F.H=0:=by unfold boom; nth_rw 1 [← h.orthog,← F.H_t]; rw [← transpose_mul, ← Matrix.mul_assoc, h.transverse, Matrix.zero_mul, transpose_zero]
  rw [Matrix.sub_mul,hv,Matrix.one_mul,sub_zero]
lemma first_oth : F.H * (1-F.boom P)=F.H:=by nth_rw 1 [← F.H_t]; rw [← show (1-F.boom P)ᵀ=1-F.boom P from by rw [transpose_sub,show (F.boom P)ᵀ=F.boom P from h.orthog,transpose_one], ← transpose_mul,h.first_dot,F.H_t]; -- changes both sides?
lemma spanning (v:B→R): P.X*ᵥv=0 → v=0:=by
  intro ht; calc
   _ = F.Uᵀ*ᵥ(P.X*ᵥv) := by rw [Matrix.mulVec_mulVec,h.long,Matrix.one_mulVec]
   _ = _ := by rw [ht]; simp
lemma frame_basis (v:E→R)(he : (P.Z*ᵥv)=0) : ∃ w,P.X*ᵥw=v:=by
  have hh:= congr_arg (Matrix.mulVec F.H) he; rw [Matrix.mulVec_zero,Matrix.mulVec_mulVec,h.sub_inv, Matrix.sub_mulVec,Matrix.one_mulVec,sub_eq_zero] at hh; exact ⟨F.Uᵀ *ᵥ v, (Matrix.mulVec_mulVec ..).trans hh.symm⟩
-- mapping transfers when at real coefficient ring then unit changes
lemma beams : Normal (F.replic M) (P.beam M) where
  resonance := by unfold replic Lot.beam; dsimp only; rw [← transpose_map,← transpose_map,← Matrix.map_mul,← Matrix.map_mul,← Matrix.map_add M (map_add M),h.resonance]; exact Matrix.map_one _ (map_zero M) (map_one M)
  long:=by unfold replic Lot.beam; dsimp only; rw [← transpose_map,← Matrix.map_mul,h.long]; exact Matrix.map_one _ (map_zero M) (map_one M)
  nilg:=by unfold Lot.beam; dsimp only; rw [← Matrix.map_mul,h.nilg]; exact Matrix.map_zero M (map_zero M)
  transverse:=by unfold replic Lot.beam; dsimp only; rw [← Matrix.map_mul,h.transverse]; exact Matrix.map_zero M (map_zero M)
  orthog:=by unfold replic Lot.beam; dsimp only; rw [← transpose_map, ← Matrix.map_mul, ← transpose_map,h.orthog]
lemma silvers (r s v w:R)(hr:r*v=1)(hs:s*w=1): Normal (F.scale r s) (P.scale v w) where
  resonance:=by unfold Fritz.scale Lot.scale; dsimp only; simp_rw [transpose_smul, Matrix.mul_smul, Matrix.smul_mul, smul_smul,_root_.mul_comm v r,hr,hs,one_smul];exact h.resonance
  long:=by unfold Fritz.scale Lot.scale; dsimp only; rw [transpose_smul, Matrix.smul_mul,Matrix.mul_smul,smul_smul,hs,one_smul]; exact h.long
  nilg:=by unfold Lot.scale; dsimp only;rw [Matrix.mul_smul,Matrix.smul_mul,h.nilg,smul_zero,smul_zero]
  transverse:=by unfold Fritz.scale Lot.scale; dsimp only;rw [Matrix.mul_smul,Matrix.smul_mul,h.transverse,smul_zero,smul_zero]
  orthog:=by unfold Fritz.scale Lot.scale; dsimp only;rw [transpose_smul,Matrix.mul_smul, Matrix.smul_mul,transpose_smul,transpose_smul,h.orthog]
end Normal
structure Landau (F:Fritz E B ℝ)(P:Lot E B ℝ):Prop extends Normal F P where
 root : P.Z.PosSemidef
lemma Landau.real {F:Fritz E B ℝ}{P:Lot E B ℝ}(H:Landau F P)(g:E→ℝ)(h: F.boom P*ᵥ g=0)(he:g≠0) : 0< g ⬝ᵥ (P.Z *ᵥ g):=by
  nth_rw 1 [← star_trivial g]; refine lt_of_le_of_ne (H.root.dotProduct_mulVec_nonneg g) fun hn=> ?_
  have hv:= (H.root.dotProduct_mulVec_zero_iff g).1 hn.symm
  have hh := congr_arg (Matrix.mulVec F.H) hv; rw [Matrix.mulVec_zero,Matrix.mulVec_mulVec,H.toNormal.sub_inv, Matrix.sub_mulVec,Matrix.one_mulVec,h,sub_zero] at hh; exact he hh
end Fritz
end YM.MSBar.Cutis
