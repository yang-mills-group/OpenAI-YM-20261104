import YM.RG11Proof.Rigidity.Reads.Crew

/-!
# Index a word chorus at its listed positions
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity.Reads
open Maxwell Maxwell.Free Wick Crowd Prism Function Tensor
open scoped BigOperators ContDiff Classical
variable {G:Gauge}{I:Type}

private def listings (Z : Board I) : Points (List.length Z):=
    points fun i=> ((List.get Z i).1)

/-- Use any finite packing of the arity names. No continuity in labels. -/
lemma curtains {Z : Board I} (H : Curtained Z): listings Z∈ conf (List.length Z):= by
  intro i j he
  have ht:= List.nodup_iff_injective_get.mp H
  have HL (i : Fin (List.length Z)) : i.val < (Z.map Prod.fst).length := by simp
  have hk (i) : (Z.map Prod.fst).get ⟨i.val,HL i⟩= (listings Z).ofLp i:= by simp [listings,points]
  have hh := congr_arg Fin.val (ht ((hk i).trans (he.trans (hk j).symm))); exact Fin.ext hh

private def members (Y : I → Cast G)(Z : Board I): Crew G (List.length Z):= List.ofFn fun i=> (i, Y (Z.get i).2)
private lemma letters (Y : I→Cast G)(Z: Board I): lines (listings Z) (members Y Z)=scoreAt Y Z:=by
  unfold lines members scoreAt; rw [List.map_ofFn]; conv_rhs=> arg 2; rw [← List.ofFn_get Z]
  rw [List.map_ofFn]; rfl

private lemma singers {I A : Type*} [DecidableEq I][Monoid A] (i:I) (L:List I) (h:L.Nodup)(f:I→A) :
    (List.map (fun t=>if i=t then f t else 1) L).prod=if i∈L then f i else 1:=by
  induction L with
  | nil=>simp
  | cons a L ih=> by_cases H:i=a
                  · subst a; simp [ih (List.nodup_cons.mp h).2,(List.nodup_cons.mp h).1]
                  simp [H,ih (List.nodup_cons.mp h).2]

private lemma frame_sings (Y:I→Cast G)(Z:Board I)(i:Fin (List.length Z)): singing (members Y Z) i=canon (Y (Z.get i).2):=by
  unfold singing members; rw [List.map_ofFn,List.ofFn_eq_map]; dsimp only [Function.comp_def]; rw [singers i (List.finRange (List.length Z)) (List.nodup_finRange _) (fun a=>canon (Y (Z.get a).2)),if_pos (List.mem_finRange i)]

lemma page {Z:Board I}(h:Curtained Z)(Y:I→Cast G):
    moment G (listings Z) (fun i=>canon (Y (Z.get i).2))=((carol (scoreAt Y Z)).asks meter:ℂ):=by
  rw [← funext (frame_sings Y Z),← one_mul (singing (members Y Z)),← show planted (G:=G) (n:= List.length Z) []=1 from rfl,script _ (curtains h),letters];rfl

end YM.RG11.Rigidity.Reads
