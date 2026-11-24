import YM.MS.Local.Tile
/-!
# Honest separation of homogeneous polynomials into one-slot tensors
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Local
open Function Filter Set Finset Plane Koszul Real Momentum Wire Tensor
open scoped Topology ContDiff
variable {P A D R X E : Type} [Fintype D] [DecidableEq D] [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {r h d : ℕ} {w c:A→ℤ}
-- finite sums vary with arbitrary slot grouping
namespace Shape
lemma scalar_pow (h:ℕ) (u : E→L[ℝ] ℝ) : Plane.Shape (fun p=> ((u p:ℂ)^h)) (h:ℤ) := by
   induction h with
   | zero=> simp; exact ⟨contDiff_const,fun h=>by omega,fun _ _=>by simp⟩
   | succ k ih=>
       have hu : Plane.Shape (fun p=>(u p:ℂ)) 1 := ⟨Complex.ofRealCLM.contDiff.comp u.contDiff, fun h=>by omega, fun t x=> by simp [Complex.real_smul]⟩
       simp_rw [pow_succ]; convert! ih.mul hu using 1
lemma times {s:Finset A} {p:A→E→ℂ} (h : ∀ i ∈ s, Plane.Shape (p i) (w i)) : Plane.Shape (fun q=> ∏ i∈s,p i q) (∑ i∈s,w i) := by
    classical
    induction s using Finset.induction with
    | empty => simp; exact ⟨contDiff_const,fun h=>by omega,fun _ _=>by simp⟩
    | insert i s hi ih=> simp only [Finset.prod_insert hi,Finset.sum_insert hi]; exact (h i (mem_insert_self ..)).mul (ih fun j hj=> h j (mem_insert_of_mem hj))
end Shape

variable [Fintype X] [DecidableEq X]
-- Expand along coordinates (x∈ X labels state slot; d∈D direction).
def eye (s : X × D) : X → Momentum D:= Pi.single s.1 (Pi.single s.2 1)
lemma eye_expand (p : X→Momentum D): ∑ t : X×D, p t.1 t.2 • eye t=p:= by
   ext i j; simp [Finset.sum_apply,Fintype.sum_prod_type, eye,Pi.single_apply,ite_apply]
def lot (f : Fin d→ X×D) (x:X) : Finset (Fin d) := (Finset.univ (α:=Fin d)).filter (fun i=> (f i).1=x)
omit [Fintype D] [DecidableEq D] in
lemma lot_size (f : Fin d→X×D) : ∑ i:X,(lot f i).card=d:= by simpa [lot] using sum_card_fiberwise_eq_card_filter (g:=fun t:Fin d=> (f t).1) (Finset.univ (α:=Fin d)) (Finset.univ (α:=X))
def poly (f:Fin d→X×D) (p:X→Momentum D):= ∏ t,p (f t).1 (f t).2
def oneLot (f:Fin d→X×D) (x:X) (p:Momentum D) : ℂ := ∏ i∈lot f x, (p (f i).2 : ℂ)
omit [DecidableEq D] [Fintype X] in
lemma lot_form (f:Fin d→X×D) (x:X): Plane.Shape (oneLot f x) (lot f x).card:= by
   convert Shape.times (s:=lot f x) (fun i h=> Shape.scalar_pow 1 (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : D=>ℝ) (f i).2)) using 1; ext; simp [oneLot]; simp
omit [Fintype D] [DecidableEq D] in
lemma lots (f : Fin d→X×D) p : (poly f p:ℂ) = ∏ i:X,oneLot f i (p i):= by
   unfold oneLot poly; rw [Complex.ofReal_prod]
   have he:= prod_fiberwise_of_maps_to (s:=Finset.univ) (t:=Finset.univ) (g:=fun i:Fin d=> (f i).1) (fun _ _=> mem_univ _) (fun i:Fin d=> (p (f i).1 (f i).2:ℂ))
   rw [← he]; refine Finset.prod_congr rfl fun i _=> Finset.prod_congr rfl fun j hj=>?_ ; rw [(Finset.mem_filter.mp hj).2]

lemma tensor_spread (L : Tensor.T (X→Momentum D) ℂ d) (p:X→Momentum D) : Tensor.diagonal L p = ∑ f:Fin d→X×D,(poly f p:ℂ)* L (eye ∘ f):= by
   let Q (x : X×D):= p x.1 x.2
   let M:=L.toMultilinearMap
   have hm : L (fun _ : Fin d=>p)= M (fun _ : Fin d=>∑ t:X×D,Q t • eye t):=by simp [M,Q,eye_expand]
   unfold Tensor.diagonal; rw [hm,M.map_sum]; refine Finset.sum_congr rfl fun f _=>?_ ; simp only [M.map_smul_univ]; exact Complex.real_smul ..
end YM.MS.Local
