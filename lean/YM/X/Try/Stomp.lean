import YM.X.Try.Omen
/-! # call map for filtered open polynomial. Leibniz; first readings. -/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Tri
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter Set Asymptotics Gauge
open Source PertExtension LatticePT Braid Gauss ProjectorNext.Calibration
open Stems hiding X
open Heat.Top
open Jet hiding Word
open scoped Topology ContDiff BigOperators Pointwise Classical
variable {d n k:ℕ} {V W A B I:Type*}
local notation "P"=> poly V
local notation "E"=> poly (V⊕V)
variable (f:poly V→ₐ[ℂ] poly W)(a: V→poly W)
def spin := MvPolynomial.mkDerivation ℂ (Sum.elim (fun p:V=> X (R:=ℂ) (Sum.inr p)) (fun _:V=> (0:poly (V⊕V))))
def pullP : poly (V⊕V) →ₐ[ℂ] poly W:= MvPolynomial.aeval (Sum.elim (fun i:V=>f (X i)) a)
def call : poly V→ₗ[ℂ] poly W:= (pullP f a).toLinearMap ∘ₗ spin.toLinearMap ∘ₗ (rename Sum.inl).toLinearMap
lemma push (p:P): pullP f a ((rename Sum.inl) p)=f p:= by apply DFunLike.congr_fun (f:=(pullP f a).comp (rename Sum.inl)); ext1 i;rw [AlgHom.comp_apply,rename_X,pullP,aeval_X];rfl
lemma call_mul (p q:P): call f a (p*q)=call f a p*f q+f p*call f a q:= by
   change pullP f a (spin ((rename Sum.inl) _))=_; simp_rw [map_mul, Derivation.leibniz,map_add]; simp only [smul_eq_mul,map_mul,push]; unfold call;dsimp; ring
lemma call_X (i:V): call f a (X i)=a i:=by unfold call;change pullP f a (spin ((rename Sum.inl) (X i))) = _; rw [rename_X,spin,MvPolynomial.mkDerivation_X, pullP]; simp
lemma call_1 : call f a 1=0:= by unfold call;change pullP f a (spin ((rename Sum.inl) 1)) = _; rw [map_one,Derivation.map_one_eq_zero,map_zero]
lemma call_rename (T:B→ V)(p:poly B): call (f.comp (rename T)) (a ∘ T) p=call f a ((rename T) p):= by
   induction p using MvPolynomial.induction_on with
   | C x=> rw [← mul_one (C x),C_mul']; simp [call_1]
   | add p q h g=> rw [map_add,map_add,map_add,h,g]
   | mul_X p i ih=> rw [map_mul (rename T) p,call_mul, AlgHom.comp_apply,rename_X,call_mul,call_X,call_X,ih, AlgHom.comp_apply]; rfl
variable {G:Gauge} (w v: poly V→ₐ[ℂ] Curly G)(S:Submodule ℝ (Reed.Fan G)){r t: V→Curly G}
lemma call_stone (p:poly V)(h: HC p d)(he:∀ i:V, Stone S k (w (X i)) (v (X i)))(ht:∀ i, Stone S k (r i) (t i)): Stone S (k*d) (call w r p) (call v t p):= by
    have hx (l:ℕ)(z:Fin l→V)(s:Finset (Fin l)) : Stone S (k*s.card) (w (glyphs z s)) (v (glyphs z s)) ∧ Stone S (k*s.card) (call w r (glyphs z s)) (call v t (glyphs z s)):= by
        induction s using Finset.induction_on with
        | empty=> unfold glyphs; simp only [Finset.prod_empty,map_one,Finset.card_empty,mul_zero,call_1]; exact ⟨Stone.along Clove.verse_one,Stone.quiet (Submodule.zero_mem _)⟩
        | insert i s hi IH=> rw [Finset.card_insert_of_notMem hi,mul_add,mul_one,add_comm (k*s.card), show glyphs z (insert i s)=X (z i)* glyphs z s from Finset.prod_insert hi]; rw [map_mul,map_mul,call_mul,call_mul,call_X,call_X]; exact ⟨(he _).mul IH.1,((ht _).mul IH.1).add ((he _).mul IH.2)⟩
    rw [p.as_sum,map_sum,map_sum]; refine Stone.sums _ fun i hi=>?_ ; obtain ⟨Z,hZ⟩:= Common.letter i; let n:= i.sum fun _ c=>c; have hn: n=d:= (Heat.Top.degree_eq i).symm.trans (h (mem_support_iff.mp hi)); rw [show MvPolynomial.monomial i (coeff i p)=(coeff i p) • monomial i (1:ℂ) from ?_,map_smul,map_smul,hZ];
    · exact Stone.scalp _ (by convert! (hx n Z Finset.univ).2; rw [Finset.card_univ, Fintype.card_fin,hn])
    rw [← map_smul,smul_eq_mul,mul_one]
end YM.PositionX.Tri
