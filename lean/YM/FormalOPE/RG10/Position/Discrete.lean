import YM.FormalOPE.RG10.Position.Retry

/-! # No-resonance from the scale law on the positioned formal system
All relations stated on the **same ψₜ** and the same family of frame matrices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Position.Grade
open Function Maxwell Labels Extraction Filter Finset Extra.FD PertExtension MeasureTheory
  Topology Metric PertExtension.Position PertExtension.Physical PowerSeries Triangle Matrix
open scoped Topology BigOperators ContDiff Classical
variable {J K : Type*} [Fintype J] [DecidableEq J] {w:J→ℕ}
variable {g:Flow}

structure Cycle (g:Flow) : Prop where
  uses (s t:ℝ) : (g.warp s).comp (g.warp t)=g.warp (s+t)
  still : g.warp 0=RingHom.id _

namespace Cycle
variable (C: Cycle g) (s t:ℝ) (P:Matrix J J fps)
include C
omit [DecidableEq J][Fintype J] in
lemma swap : (P.map (g.warp s)).map (g.warp t)=(P.map (g.warp t)).map (g.warp s) := by
  ext i j : 1; exact DFunLike.congr_fun ((C.uses t s).trans ((congr_arg g.warp (add_comm t s)).trans (C.uses s t).symm)) _
lemma neutral (f:fps) : g.warp s (g.warp (-s) f)=f := by rw [← RingHom.comp_apply,C.uses,add_neg_cancel,C.still,RingHom.id_apply]
end Cycle
namespace Passe
variable (h:Passe g w) (C:Cycle g)
open Retry

lemma first_step : h.book.map (g.warp 1) * h.train 1=h.drive 1*h.book:=sub_eq_zero.mp h.booked.2.2
omit [DecidableEq J] [Fintype J] in
private lemma blank_sub (x y:Matrix J J fps) (f:fps→+*fps) : (x-y).map f=x.map f-y.map f:= by ext i j : 1; simp

include C
lemma step (s:ℝ) : inter g 1 (h.train 1) ((h.drive 1).map (g.warp s)) (inter g s (h.train s) (h.drive s) h.book) =0 := by
  have he : ((h.book.map (g.warp 1)).map (g.warp s)) * ((h.train 1).map (g.warp s)) = ((h.drive 1).map (g.warp s))*(h.book.map (g.warp s)) := by rw [← Matrix.map_mul,h.first_step,Matrix.map_mul]
  have hg : ((h.train 1).map (g.warp s)) * h.train s = ((h.train s).map (g.warp 1)) * h.train 1 := by rw [h.law,h.law,add_comm]
  have hf : ((h.drive 1).map (g.warp s))*h.drive s = ((h.drive s).map (g.warp 1))*h.drive 1 := by rw [h.station_law,h.station_law,add_comm]
  unfold inter; apply sub_eq_zero.mpr; rw [blank_sub,sub_mul,mul_sub]; simp only [Matrix.map_mul]; congr 1
  · rw [C.swap s 1,mul_assoc,← hg,← mul_assoc,he,mul_assoc]
  rw [mul_assoc,h.first_step,← mul_assoc,← hf,mul_assoc]

-- consequence: the normalized adjusted law is the pure-grade block of prepositioned law
lemma describes (s:ℝ): h.book.map (g.warp s)*h.train s=h.drive s*h.book:= by
 have hz: stamp ((h.drive 1).map (g.warp s)) 0=stone w 1:= by rw [← h.stationed 1]; exact first_sup (fun _ h=> by omega)
 obtain ⟨hc,hp,_⟩:=h.booked
 refine sub_eq_zero.mp (alone (h.full 1) hz zero_lt_one ?_ (h.step C s));
 refine Cut.crush ?_ ?_
 · exact ((hc.carries _).mul (h.rank _)).sub ((layer_cut (h.station_block _)).mul hc)
 rw [tile_sub,Cut.tile (hc.carries _) (h.rank _), Cut.tile (layer_cut (h.station_block _)) hc, tile_map,hp,layer_fixed (h.station_block s)]; simp [drive]

omit C
lemma commute_w (U:Matrix J J fps)(hu:U*h.train 1=h.train 1*U)(hb : U.map (g.warp 1)=U)(hc : Layer w U) : U*h.book=h.book*U := by
 obtain ⟨hN,hO,_⟩:=h.booked
 have ht:=layer_cut hc
 have he : U*h.drive 1=h.drive 1*U:= by
    have h1:=congr_arg (tile w) hu; rw [Cut.tile ht (h.rank 1),Cut.tile (h.rank 1) ht,layer_fixed hc] at h1; exact h1
 apply sub_eq_zero.mp;
 refine alone (h.full _) (h.stationed 1) zero_lt_one ((ht.mul hN|>.sub (hN.mul ht)).crush ?_) (hK:=?_) (g:=g)
 · rw [tile_sub,Cut.tile ht hN,Cut.tile hN ht,hO,mul_one,one_mul, sub_self]
 apply sub_eq_zero.mpr; rw [blank_sub,Matrix.map_mul,Matrix.map_mul,sub_mul,mul_sub,hb]; congr 1;
 · rw [mul_assoc,first_step,← mul_assoc,he,mul_assoc]
 rw [mul_assoc,hu,← mul_assoc,first_step,mul_assoc]

lemma first_base : stamp h.book 0=1:=by rw [row,work,canvas]; simp
lemma invertible : IsUnit h.book := by rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_constantCoeff];
                                            rw [RingHom.map_det]; change IsUnit (Matrix.det (h.book.map constantCoeff)); rw [← canvas,first_base,det_one]; exact isUnit_one
lemma backs (s:ℝ) : h.drive s * ((h.drive (-s)).map (g.warp s))=1 := by
  let f := g.warp s; have he: ((h.drive (-s)).map f)*h.drive s=1:= (h.station_law ..).trans (by rw [neg_add_cancel,station_base]);
  exact mul_eq_one_comm.mpr he
end Passe

section clip
variable [Fintype K] [DecidableEq K] (x:K↪J) (α:K→ℕ) (hx : ∀ i, α i=w (x i))
end clip
end YM.FormalOPE.RG10.Position.Grade
