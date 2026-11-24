import YM.Frontier6.Multi.Diff.Transfer
import YM.Frontier6.Multi.Diff.Rough

/-!
# Vary **one** leaf; eventually all stencils in closed box. Raw derivative chain.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Road
open Function Filter Finset Set MergeProof.Ribbons MergeProof.Acme Fareway Tale Spec
open scoped Topology BigOperators ContDiff Classical
variable {I J V:Type} [Fintype V][DecidableEq V]{G:Gauge}{C:Family G}{F:Extraction.Order}{S: Table C.book}
variable (K:Final C F S) {T : Fareway I}{a b c r:ℝ}
set_option quotPrecheck false

abbrev rest (i:V) := {j:V// j≠i}
lemma erasing (p:V→ E4)(v:V→ S.Tag)(i:V): assembly S p v=letter S (p i) (v i)*assembly S (p ∘ (Subtype.val:rest i→V)) (v ∘ Subtype.val):=by
    let E:= Equiv.optionSubtypeNe i; rw [←reorders S E]; unfold assembly; rw [Fintype.prod_option]; rfl
section
variable (x:V→ E4)(v:V→S.Tag)(z:V × Axis) (k n:ℕ)(a:ℝ)(s:StateIndex K)
local notation "q"=> z.1
def route (k:ℕ) : V→ S.Tag:= update v z.1 (trek K.sector.derivatives z.2 (v z.1) k)
lemma route_same (p:V)(hh:p≠ z.1): route K v z k p=v p:= update_of_ne hh ..
lemma route_zero : route K v z 0=v:= update_eq_self ..
lemma revolve_cap: wages (route K v z k)=wages v+k:=by
   let g(l:V→ S.Tag):V→ℝ:=fun i=> ((l i).1:ℝ)+2; let v':=route K v z k
   have he(l:V→ S.Tag) : wages l=g l q+∑ i∈Finset.univ.erase q,g l i := (Finset.add_sum_erase Finset.univ (g l) (mem_univ _)).symm
   rw [he (route K v z k),he v, sum_congr (s₂:=Finset.univ.erase q) (g:=g v) rfl (fun i hi=>by dsimp only [g];rw [route_same ..]; exact ne_of_mem_erase hi)]; unfold g route; rw [update_self,trek_h]; push_cast; ring -- around dot?

lemma throwback (p:E4)(w:S.Tag)(x:V→E4)(v:V→ S.Tag) (i:V)(z:Fin (Fintype.card (rest i))≃ rest i):
   assembly S (update x i p) (update v i w)= assembly S (Fin.cons p (fun j=> x (z j))) (Fin.cons w (v ∘ Subtype.val ∘ z)):=by
   rw [erasing (i:=i),update_self,update_self, ← reorders S z]; rw [show ((update x i p ∘ Subtype.val)∘z)= (fun i=>x (z i)) from funext fun i=> update_of_ne (z i).property .., show ((update v i w ∘ Subtype.val)∘z)= v ∘ Subtype.val ∘ z from funext fun i=> update_of_ne (z i).property ..]; exact letter_head S _ _ (points (fun i=>x (z i))) _
lemma anointed {N:ℕ}(E:Fin N ≃ rest z.1){t:ℝ}(hp:Injective (wag x a z t)): Points.cons (chord z.2 (x z.1) a t) (points (fun i=>x (E i))) ∈conf (N+1):=by
   let Z:= wag x a z t; let Y:= Points.cons (chord z.2 (x z.1) a t) (points (fun i=>x (E i))); have hg:Y.ofLp=Z ∘ Fin.cons z.1 (fun i=> (E i).val):=by ext1 j; refine Fin.cases ?_ (fun i=>?_) j; exact (wag_eq ..).symm; exact (wag_untouched _ _ _ _ _ (E _).property).symm -- use E i
   change Injective Y.ofLp; rw [hg]; refine hp.comp ?_; have hN:Injective ((Subtype.val:rest z.1→V) ∘ E):=Subtype.val_injective.comp E.injective; refine Fin.cons_injective_of_injective ?_ hN
   rintro ⟨i,hp⟩; exact (E i).property hp

variable (i:StateIndex K)
lemma starter (t:ℝ)(hp:Injective (wag x a z t)): HasDerivAt
    (fun t=> a^k • poll S (state K i) (assembly S (wag x a z t) (route K v z k)))
    (a^(k+1) • poll S (state K i) (assembly S (wag x a z t) (route K v z (k+1)))) t:=by
    let η:= (Fintype.equivFin (rest q)).symm; let X:= x (z.1); let V':=points (fun i=> x (η i)); let W:= v ∘ Subtype.val ∘ η; let D:=trek K.sector.derivatives z.2 (v q)
    let f(n:ℕ)(u:ℝ):= reading K i (chord z.2 X a u) V' W (D n).1 (D n).2
    have he(u)(n:ℕ)(h:Injective (wag x a z u)): poll S (state K i) (assembly S (wag x a z u) (route K v z n)) = f n u:=by
       let K':= Points.cons (chord z.2 X a u) V'; have hX: K'∈ conf _:= anointed _ _ _ η h
       unfold wag route; rw [throwback (z:=η)]; change poll S _ (assembly S K'.ofLp (Fin.cons (D n) W))= f n u; rw [examines S _ (hierarchy K i).laws.toSymmetric K' _, if_pos hX]; exact (reads_at ..).symm
    rw [he t (k+1) hp]; refine (orbit_derives K (v q) W V' X z.2 a t i (anointed _ _ _ η hp) k).congr_of_eventuallyEq ?_; filter_upwards [larger (wag_cont ..|>.continuousAt) hp] with t h using congr_arg (fun x:ℂ=> a^k • x) (he t k h)
end
end YM.Frontier6.Road
