import YM.AllOrder.Ink.Brush
import Mathlib.Algebra.MvPolynomial.Funext
/-!
# insert polarized marker variables in REAL polynomials P before support accounting
 Geometric spends need not periodize at C=library near. Read scheduler germ.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Quipu.Turbin
open AllOrder AllOrder.Ink
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace Laplace.SigmaP Ker
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response Ink GaussianScore Module
open scoped BigOperators Topology Classical ContDiff
variable {n m:Side} {α : Type}[Fintype α]
open MvPolynomial hiding funext
abbrev Ch (α:Type):= MvPolynomial α ℝ
def guide (v:Ch α) (x: α→ℝ): ℝ:= aeval x v
lemma guide_add (v w:Ch α): guide (v+w)=guide v+guide w:=funext fun _=> _root_.map_add _ _ _
lemma guide_mul (v w:Ch α): guide (v*w)=guide v*guide w:=funext fun _=> _root_.map_mul _ _ _
lemma guide_scale (t:ℝ)(v:Ch α): guide (t•v)=t•guide v:= funext fun _=> _root_.map_smul (aeval _) _ _
lemma guide_col (i:α): guide (X (R:=ℝ) i)= fun x=> x i:=funext fun _=> aeval_X _ _ -- macro conflicts
lemma guide_const (c:ℝ): guide (α:=α) (C c)=fun _=> c:= funext fun _=> aeval_C ..
lemma guide_only : Injective (guide (α:=α)):= fun _ _ h=> MvPolynomial.funext fun x=> congr_fun h x
variable {f g :(α→ℝ)→ℝ}
lemma sold (h:Plausible f): ∃ P, guide P=f:= by
 induction h with
 | atom c=> exact ⟨C c,guide_const _⟩
 | times f L _ ih => obtain ⟨p,hp⟩:=ih; let u:=Pi.basisFun ℝ α; refine ⟨p*(∑ j:α,L (u j) • MvPolynomial.X j),?_⟩; rw [guide_mul,hp]; apply congr_arg (f * ·); ext1 s; unfold guide; rw [_root_.map_sum]; simp_rw [_root_.map_smul,aeval_X]; nth_rw 2 [←u.sum_repr s]; rw [_root_.map_sum]; refine Finset.sum_congr rfl fun j _=> ?_; rw [_root_.map_smul]; exact mul_comm (L (u j)) (s j) -- inspect instances
 | add h H i j=> obtain ⟨p,rfl⟩:=i; obtain ⟨q,rfl⟩:=j; exact ⟨p+q,guide_add ..⟩ -- rfl may rw motives
lemma bill (v:Ch α): Plausible (guide v):= by
 induction v using MvPolynomial.induction_on with
 | C v=> rw [guide_const]; exact Plausible.atom _
 | add h H hh ht=> rw [guide_add]; exact hh.add ht
 | mul_X q i hi=> rw [guide_mul,guide_col]; exact Plausible.times _ (Pi.basisFun ℝ α|>.coord i) hi
variable (f) in
def keeper := if h:Plausible f then (sold h).choose else 0
variable {G:Type}[CommSemiring G][Algebra ℝ G]
def wall (v:α→G)(f:(α→ℝ)→ℝ): G:= aeval v (keeper f)
variable (x:α→G)
lemma lives (p:Ch α): keeper (guide p)=p:= by rw [keeper, dif_pos (bill p)]; exact guide_only (sold (bill p)).choose_spec
lemma live (p:Ch α): wall x (guide p)=aeval x p:= by unfold wall; rw [lives]
lemma sky_c(c:ℝ): wall x (fun _=> c)=algebraMap ℝ G c:= by rw [← guide_const, live, aeval_C]
lemma sky_x(i:α): wall x (fun p=> p i)=x i:= by rw [← guide_col,live,aeval_X]
variable (h:Plausible f)(he:Plausible g)
include h he
lemma pours_a : wall x (f+g)=wall x f+wall x g := by obtain ⟨p,hp⟩:= sold h; obtain ⟨q,hq⟩:= sold he; rw [← hp,← hq,← guide_add, live,live,live,_root_.map_add]
lemma pours_m : wall x (f*g)=wall x f*wall x g := by obtain ⟨p,hp⟩:= sold h; obtain ⟨q,hq⟩:= sold he; rw [← hp,← hq,← guide_mul, live,live,live,_root_.map_mul]
omit he
lemma pours_s (r:ℝ): wall x (r•f)=r• wall x f:= by obtain ⟨p,hp⟩:= sold h; rw [← hp,← guide_scale,live,live,_root_.map_smul]
omit h
lemma pours {J:Type*} (s:Finset J)(p:J→(α→ℝ)→ℝ)(h:∀ i∈s,Plausible (p i)): wall x (∑ i∈s,p i)=∑ i∈s, wall x (p i):= by
 induction s using Finset.induction_on with
 | empty=>simp only [Finset.sum_empty]; exact (sky_c x 0).trans (_root_.map_zero (algebraMap ℝ G))
 | insert i s hi ih=> rw [sum_insert hi,sum_insert hi,pours_a _ (h _ (mem_insert_self ..)) (Plausible.sum (fun i hi=> h i (mem_insert_of_mem hi))), ih (fun i hi=> h i (mem_insert_of_mem hi))]
lemma products {J:Type*} (s:Finset J)(p:J→(α→ℝ)→ℝ)(h:∀ i∈s,Plausible (p i)): wall x (∏ i∈s,p i)=∏ i∈s, wall x (p i):= by
 induction s using Finset.induction_on with
 | empty=>simp only [Finset.prod_empty]; exact (sky_c x 1).trans (_root_.map_one (algebraMap ℝ G))
 | insert i s hi ih=> rw [prod_insert hi,prod_insert hi,pours_m _ (h _ (mem_insert_self ..)) (Plausible.prod (fun i hi=> h i (mem_insert_of_mem hi))), ih (fun i hi=> h i (mem_insert_of_mem hi))]
lemma talent (A:G→ₗ[ℝ]ℝ) (k:ℕ): LinTest (α→ℝ) k (A∘ wall x):= ⟨fun f g h H=>by simp only [Function.comp_apply,pours_a _ h.read H.read,_root_.map_add],fun f t h=>by simp only [Function.comp_apply,pours_s _ h.read,_root_.map_smul]; rfl⟩
end YM.Qlocal.Quipu.Turbin
