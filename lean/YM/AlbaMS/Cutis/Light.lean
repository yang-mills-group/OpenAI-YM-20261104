import YM.AlbaMS.Odom.Hearth
/-!
# Quadratic forms and covariance calculus on simple graph

Use matrices on chosen orthonormal basis indices. Entries precision already
include canonical counting integration `a^4` and engineering factors. Separate
pairing scale `a^-4`. General spectral functions allowed including finite band
(Bill independence), values in R. Symmetry/orthogonality transpose literal.
Don't assume any unscaled group coords here. Working representation used for
both Book & continuum (latter at finite scales in Symbol). Fintype universes
for contents unrestricted.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Cutis
open Set Function Filter LinearMap Matrix
open scoped BigOperators Classical Topology Matrix
open Bric Coil Inlay Inlay.Net Loft
variable {E B I R S : Type*} [Fintype E][Fintype B][CommRing R][CommRing S]
abbrev θ (a:R)(i j : Place E B):= a * Loft.oriented R i j
structure Lot (E B R : Type*) [CommRing R] where
 Z : Matrix E E R
 X : Matrix E B R
 symm i j : Z i j=Z j i
-- Γ twist in ∆
structure Strip (E B R:Type*) where
 Z : Matrix E E R
 X : Matrix B B R
namespace Strip
variable (P:Strip E B R)
def footing (i j:Place E B): R:= match i,j with
  | .inl (.inl u),.inl (.inr v) => P.Z u v
  | .inr (.inl u),.inr (.inr v) => - P.X u v
  | _,_=>0
omit [Fintype E][Fintype B] in
lemma graded : Graded ø true P.footing:=by rintro ((i|i)|(i|i)) ((j|j)|(j|j)) h <;> first| rfl| exact False.elim (h rfl)
-- scaled unity uses choice matters instances
omit [Fintype E][Fintype B] in
def unity (E B : Type*) [DecidableEq E][DecidableEq B](a:R) : Strip E B R:= ⟨a • 1, a • 1⟩
omit [Fintype E][Fintype B] in
lemma universal [DecidableEq E][DecidableEq B](a:R) : (unity E B a).footing=θ a:=by
  funext i j; rcases i with (i|i)|(i|i) <;> rcases j with (j|j)|(j|j) <;>
    simp [θ,footing, Loft.oriented,unity, Matrix.one_apply, eq_comm,Place.k,Place.l]; split_ifs <;> simp
omit [Fintype E][Fintype B] in
lemma work (r:R):Graded (@ø E B) true (θ r):= by rw [← universal]; exact Strip.graded _
end Strip

namespace Lot
variable (P:Lot E B R)
variable [Algebra ℚ R]
def boson : Floor E B R:= halve R • ∑ i:E,∑ j:E,P.Z i j • (A R i*A R j)
def tong : Floor E B R:=∑ i:E,∑ j:B,P.X i j • (K R i*C R j)
def combo : Floor E B R:= P.boson+P.tong
lemma tone : EvenT P.combo:= by
  have ht (i:E): EvenT (B:=B) (A R i):= var_tone (Place.a i)
  exact Tone.add ((Tone.sum _ _ fun i _=> Tone.sum _ _ fun j _=> ((ht i).mul (ht j)).smul _).smul _) (Tone.sum _ _ fun i _=> Tone.sum _ _ fun j _=> ((var_tone (R:=R) (ρ:=ø) (Place.k i)).mul (var_tone (Place.c j))).smul _)
lemma rank : Heg 2 P.combo:= Heg.add (Heg.smul (Heg.sum _ _ fun _ _=> Heg.sum _ _ fun _ _=> ((Heg.var _).mul (Heg.var _)).smul _) _) (Heg.sum _ _ fun _ _=> Heg.sum _ _ fun _ _=> ((Heg.var _).mul (Heg.var _)).smul _)
-- derivatives. keep `D` generic only in notation if needed.
omit [Algebra ℚ R] [Fintype E] [Fintype B] in
private lemma keDC (i:E)(j:B)(x:B) : DC x (K R i*C R j)= if x=j then -K R i else 0:=by
  change D _ (_*_)=_; rw [mulD,(var_tone (ρ:=ø) (R:=R) (Place.k i)).pl]; change _* _ + -(K _ _)*_=_; by_cases he:x=j<;>simp [K,C, Place.k,Place.c,he]
omit [Algebra ℚ R] [Fintype E] [Fintype B] in
private lemma asm {ι : Type*}(r:R)(x y:ι)(a:Floor E B R): r • (ite (x=y) a 0)=ite (x=y) (r • a) 0:=by by_cases h:x=y<;>simp [h]
omit [Algebra ℚ R] [Fintype E] [Fintype B] in
private lemma pairA (i j k:E): DA i (A R j*A (B:=B) R k)= (if i=j then A _ k else 0)+(if i=k then A _ j else 0):=by
  unfold DA; rw [mulD,(var_tone (R:=R) (ρ:=ø) (Place.a j)).pl]; change _* _ + A R j*_=_; simp [A,Place.a,ite_mul,mul_ite]
lemma combo_A (i:E) : DA i P.combo=∑ j:E, P.Z i j • A R j:= by
  have he: DA i P.tong=0:=by simp [DA,tong,mulD,K,C,Place.k,Place.a,Place.c];
  rw [combo,map_add, he, add_zero,boson,map_smul]; simp_rw [map_sum,map_smul,pairA,smul_add,asm,Finset.sum_add_distrib]
  rw [Finset.sum_comm]; simp only [Finset.sum_ite_eq, Finset.mem_univ,if_true]; simp_rw [P.symm _ i,twice_halve]
lemma combo_K (i:E): DK i P.combo=∑ j:B, P.X i j • C R j:=by
  have he: DK i P.boson=0:=by simp [DK,boson,mulD,A,Place.a,Place.k]
  rw [combo,map_add,he,zero_add]; simp_rw [tong,map_sum,map_smul]; rw [Finset.sum_eq_single i];
  · simp [DK,K,C,mulD,Place.c,Place.k]
  intro j hj ht; simp [DK,K,C,mulD,Place.c,Place.k,Ne.symm ht]; simp -- indent
lemma combo_C (j:B): DC j P.combo= -(∑ i:E, P.X i j • K R i):=by
  have he: DC j P.boson=0:=by simp [boson,DC,A,mulD,Place.a,Place.c];
  simp_rw [combo,map_add,he,zero_add,tong,map_sum,map_smul,keDC,asm]; simp [Finset.sum_neg_distrib]
lemma combo_L (j:B): DL j P.combo=0:=by simp [combo,boson,tong,DL,A,K,C,mulD, Place.a,Place.l,Place.k,Place.c]

def q (r:R) : Module.End R (Floor E B R):= tether true (θ r) Finset.univ P.combo
lemma talks (r:R)(F : Floor E B R): P.q r F= r • Loft.coupling P.combo F:= by apply pay_across r -- need defeq
lemma qA (r:R)(i:E): P.q r (A R i)= r • ∑ j:B,P.X i j • C R j:=by rw [talks, Loft.connects _ _ P.tone]; simp_rw [P.combo_K]; simp [A,DA,DL,DC,DK, Place.a,Place.l,Place.k,Place.c]
lemma qC (r:R)(j:B): P.q r (C R j)=0:=by rw [talks, Loft.connects _ _ P.tone]; simp_rw [P.combo_L]; simp [C,DA,DL,DC,DK, Place.a,Place.l,Place.k,Place.c] -- t
lemma qK (r:R)(i:E): P.q r (K R i) = r • ∑ j:E,P.Z i j • A R j:=by rw [talks, Loft.connects _ _ P.tone]; simp_rw [P.combo_A]; simp [K,DA,DL,DC,DK, Place.a,Place.l,Place.k,Place.c]
lemma qL (r:R)(j:B): P.q r (L R j) = r • ∑ i:E,P.X i j • K R i:=by rw [talks, Loft.connects _ _ P.tone]; simp_rw [P.combo_C]; simp [L,DA,DL,DC,DK, Place.a,Place.l,Place.k,Place.c]
end Lot
end YM.MSBar.Cutis
