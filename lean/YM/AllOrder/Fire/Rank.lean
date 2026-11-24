import YM.AllOrder.Response.Thermal
/-!
# Rank-bounded real tensor polynomials. Physical charge not in this algebra.

Support/kernel costs supplied later. Use this at finite periods only, derivative recursion.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Fire
open Finset Function Laplace.SigmaP Laplace PositionX.Jet PertExtension PertExtension.Series PositionX.Gauss Radial Asymptotics MeasureTheory Response
open scoped Topology ContDiff BigOperators Classical
variable {Y X:Type} [NormedAddCommGroup X][NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
local notation "Ω"=>X×Y
-- Degree-positive includes constants. Will use birth for strict rank at (n,m) and derivative support.
inductive Rank (X:Type*) [NormedAddCommGroup X][NormedSpace ℝ X] : ℕ → (X→ℝ) → Prop where
  | nil (n:ℕ) (c:ℝ): Rank X n (fun _=>c)
  | dot (P:X→L[ℝ]ℝ)(n:ℕ){f:X→ℝ}: Rank X n f → Rank X (n+1) ((P:X→ℝ)* f)
  | add {n:ℕ}{f g:X→ℝ}: Rank X n f → Rank X n g → Rank X n (f+g)
variable {n k d:ℕ}{f g:X→ℝ}
namespace Rank
lemma up' (h:Rank X n f) : Rank X (n+1) f := by induction h with
   | nil=>apply Rank.nil
   | dot z n h H=> exact dot z _ H
   | add _ _ i j=> exact i.add j
lemma up (h:Rank X n f)(hk:n≤k) : Rank X k f:=by induction hk with | refl=>exact h | step _ h=>exact up' h
lemma scal (h:Rank X n f) (k:ℝ):Rank X n (k • f):= by induction h with
   | nil _ c=> exact Rank.nil _ (k*c)
   | @dot P i f _ H=>rw [← mul_smul_comm]; exact dot _ _ H
   | add h h' i j=> rw [smul_add]; exact i.add j
lemma neg (h:Rank X n f):Rank X n (-f):= neg_one_smul ℝ f ▸ h.scal (-1)
lemma sub (h: Rank X n f)(H:Rank X n g): Rank X n (f-g):= sub_eq_add_neg f g ▸ h.add H.neg
lemma mul (h:Rank X n f)(H: Rank X k g): Rank X (n+k) (f*g):= by induction H with
   | nil i c=> have he: f*(fun _=>c)= c• f:= funext fun i=>mul_comm (f i) c; rw [he]; exact (scal h c).up (by omega)
   | @dot P i g _ ih=> rw [mul_left_comm f (⇑P)]; exact Rank.dot _ (n+i) ih
   | add H H' i j=> rw [mul_add]; exact i.add j
lemma sum {ι:Type*}{s:Finset ι}{f : ι→ X→ℝ}(hf:∀ i∈s,Rank X n (f i)): Rank X n (∑ i∈s,f i) := by induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact Rank.nil n 0
  | insert i j hi ih=> rw [sum_insert hi]; exact (hf _ (mem_insert_self ..)).add (ih (fun a ha=> hf a (mem_insert_of_mem ha)))
lemma read (h:Rank X n f): Plausible f:= by induction h with
  | nil => apply Plausible.atom
  | dot P _ _ H=>exact (Plausible.line P.toLinearMap).mul H
  | add _ _ i j=> exact i.add j
lemma line (P:X→L[ℝ]ℝ):Rank X 1 (⇑P):= mul_one (⇑P:X→ℝ) ▸ Rank.dot P 0 (Rank.nil 0 1)
omit [NormedAddCommGroup Y] [NormedSpace ℝ Y] in
lemma lin_prod (X Y : Type) [NormedAddCommGroup X][NormedSpace ℝ X] [NormedAddCommGroup Y][NormedSpace ℝ Y] (P:Y→L[ℝ]X) (f:X→L[ℝ]ℝ): (fun x=> f (P x)) = ⇑(f∘L P):= rfl -- unused
lemma app (h:Rank X n f)(L:Y→L[ℝ]X)(x:X):Rank Y n (fun y=> f (x+L y)):= by
 induction h with
 | nil=>apply Rank.nil
 | @dot P m f h ih=>
    convert (((line (P ∘L L)).add (Rank.nil 1 (P x))).mul ih).up (le_of_eq (Nat.add_comm ..)) using 1; ext y; simp [add_comm]
 | add _ _ i j=> exact i.add j
lemma lead (h:Rank X n f)(L:Y→L[ℝ]X):Rank Y n (f ∘ L):= by simpa [Function.comp_def] using h.app L 0
variable [FiniteDimensional ℝ X]
omit [FiniteDimensional ℝ X] in
lemma asZero (h:Rank X n f)(hn:n=0): ∀ x y,f x=f y:= by
 induction h with
 | nil => exact fun _ _=> rfl
 | dot => omega
 | add _ _ h k=> exact fun x y=> congr_arg₂ (·+·) (h hn x y) (k hn x y)
lemma der (h:Rank X n f) (x:X): Rank X (n-1) (diff' x f) := by
 induction h with
 | nil i c=> convert (Rank.nil (X:=X) (i-1) (0:ℝ)) using 1; funext p; simp [diff']
 | add h h' i j=> convert i.add j using 1; ext p; rw [diff',fderiv_add (h.read.smooth.differentiable (by simp) p) (h'.read.smooth.differentiable (by simp) p)]; rfl
 | @dot P i f h ih=>
    rw [Nat.add_sub_cancel]
    have he : diff' x (P*f)= (P x) • f + (P:X→ℝ)*diff' x f:= by funext q; unfold diff'; rw [fderiv_mul P.differentiableAt (h.read.smooth.differentiable (by simp) q),P.fderiv]; simp [add_comm,mul_comm]
    rw [he]; apply (h.scal (P x)).add; rcases i with _|i
    · rw [show diff' x f=0 from ?_,mul_zero]; exact Rank.nil 0 0; clear ih; -- impossible induction on rank at fixed 0. prove lemma
      have he : f=(fun _=> f x):= funext fun i=> h.asZero rfl i x; unfold diff'; rw (occs:=.pos [1]) [he]; simp; rfl
    apply (Rank.dot _ _ (by simpa using ih))
-- rank on tensor diagonal
lemma hom {Y:Type} [NormedAddCommGroup Y][NormedSpace ℝ Y] [FiniteDimensional ℝ Y] (A: Y→L[ℝ] X) (f:ContinuousMultilinearMap ℝ (fun _:Fin n=>X) ℝ): Rank Y n (fun y=> f (fun _=> A y)):= by
   -- use curry at n=.
   induction n with
   | zero=> rw [show (fun y=> f (fun _=> A y))=(fun _=> f (fun _=>0)) from funext (fun x=> congr_arg (⇑f) (Subsingleton.elim ..))]; apply Rank.nil
   | succ n ih=>
      let B:=Module.finBasis ℝ X
      let L i:= (B.coord i).toContinuousLinearMap ∘L A; let g i:= f.curryLeft (B i)
      have he : (fun y=> f (fun _=> A y))= ∑ i:Fin (Module.finrank ℝ X), (L i:Y→ℝ)*(fun y=> g i (fun _=> A y)) := by
         funext y; let U := A y; let V i:=B.coord i U • B i
         rw [show (fun _:Fin (n+1)=>A y)= Fin.cons (∑ i,V i) (fun _=>A y) from ?_]; swap; · simp_rw [V, show ∑ i, B.coord i U • B i=U from B.sum_repr U]; ext1 i; exact Fin.cases rfl (fun i=> rfl) i -- edit
         rw [← ContinuousMultilinearMap.curryLeft_apply,map_sum, Finset.sum_apply]; simp only [_root_.sum_apply]; refine Finset.sum_congr rfl fun i _=> ?_; rw [show V i=B.coord i U • B i from rfl,map_smul,_root_.smul_apply]; rfl
      exact he.symm ▸ Rank.sum fun i _=> Rank.dot (L i) n (ih _)

end Rank
end YM.AllOrder.Fire
