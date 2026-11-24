import YM.RG11Proof.Rigidity.Halo
import YM.RG11Proof.Rigidity.Nick

/-!
# Summing the independent colors
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity
open Maxwell Maxwell.Free Function List
open scoped BigOperators Classical

abbrev Dye (C A : Type*) := (C → A) × (C → A)

def palette {C A R : Type*} [Fintype C] [AddCommMonoid R] : List (Dye C A) → (List A → R) → R
  | [],f=>f []
  | i::p,f=>∑ s : C, palette p (fun l=> f (i.1 s :: i.2 s :: l))

namespace palette
variable {C A R : Type*} [Fintype C] [CommSemiring R]

@[simp] lemma nil (f : List A → R) : palette ([]:List (Dye C A)) f=f [] := rfl
lemma cons (i : Dye C A) (L : List (Dye C A)) (f : List A → R) :
    palette (i::L) f=∑ s : C,palette L (fun l=>f (i.1 s::i.2 s::l)) := rfl
lemma append (L P : List (Dye C A)) (q : List A → R) : palette (L++P) q=palette L (fun l=>palette P (fun u=>q (l++u))) := by
  induction L generalizing q with
  | nil => simp
  | cons a l ih => rw [List.cons_append, cons,cons]; simp_rw [ih]; rfl
lemma add (L : List (Dye C A)) (q t : List A → R) : palette L (fun l=> q l+t l)=palette L q+palette L t := by
  induction L generalizing q t with
  | nil => simp
  | cons a l ih => simp_rw [cons,ih,Finset.sum_add_distrib]
lemma mul (L : List (Dye C A)) (q : List A → R) (c : R) : palette L (fun l=>c*q l)=c*palette L q := by
  induction L generalizing q with
  | nil => simp
  | cons a l ih => simp_rw [cons,ih,Finset.mul_sum]
lemma sum (L : List (Dye C A)) {I : Type*} (s : Finset I) (q : I → List A → R) :
    palette L (fun l=>∑ i∈s,q i l)=∑ i∈s,palette L (q i) := by
  induction L generalizing q with
  | nil => simp
  | cons a l ih => simp_rw [cons,ih]; exact Finset.sum_comm

variable {G : Gauge}
open Crowd

def showT (G : Gauge) (i : Crowd.Panel) : Dye G.ColorIndex (Pig G) :=
    (toss i.1.1 i.1.2,toss i.2.1 i.2.2)

lemma sums_read (L : List Crowd.Panel) (W : Crowd G) (q : Word G→ℝ) :
    (Crowd.run L W).asks q=palette ((L.reverse.map (showT G))) (fun p=>W.asks (fun r=> q (p++r))) := by
  induction L generalizing W with
  | nil => simp [run]
  | cons i l ih =>
    rw [List.reverse_cons,List.map_append,append]
    change (run l (W.panel i)).asks _ = _
    rw [ih,List.map_singleton]; simp_rw [cons (showT G i) [],nil,panelRead]
    simp [List.append_assoc,showT,painting]

end palette

end YM.RG11.Rigidity
