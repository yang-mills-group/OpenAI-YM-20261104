import YM.FormalBulk08.Dawn.Hill
import Mathlib.LinearAlgebra.Vandermonde

/-! Cube-extension along hyperplanes using finitely many negative tiny
reflections. Buys a bounded linear extension in the tested C^D norm
with no loss of derivatives; cost only by D. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Annex
open Function Filter Lattice Finset Dawn Set
open scoped BigOperators Topology ENNReal Classical ContDiff
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]{D k:ℕ}
lemma pieceD {s t:Set E}{f g e : E→ℝ}(hs:IsClosed s)(ht:IsClosed t)(h:s∪t=Set.univ)
     (hf:ContDiff ℝ D f)(hg:ContDiff ℝ D g)(hp:EqOn e f s)(he:EqOn e g t)
     (hc:∀ m:ℕ,m ≤ D→EqOn (iteratedFDeriv ℝ m f) (iteratedFDeriv ℝ m g) (s∩t)):
     ContDiff ℝ D e ∧ ∀ m:ℕ,m≤ D→EqOn (iteratedFDeriv ℝ m e) (iteratedFDeriv ℝ m f) s ∧ EqOn (iteratedFDeriv ℝ m e) (iteratedFDeriv ℝ m g) t:= by
   let j (m:ℕ)(f:E→ℝ) := iteratedFDeriv ℝ m f; let P (m:ℕ):= EqOn (j m e) (j m f) s ∧EqOn (j m e) (j m g) t
   obtain ⟨F,U⟩:= contDiff_nat_iff_continuous_differentiable.mp hf; obtain ⟨G,V⟩:= contDiff_nat_iff_continuous_differentiable.mp hg
   have hx (x:E): x∈s ∨ x∈t :=by change x∈ s∪t; rw [h]; exact mem_univ x
   have hm (m:ℕ)(hh:m<D)(p:P m): (∀ x∈ s, HasFDerivAt (j m e) (fderiv ℝ (j m f) x) x) ∧ (∀ x∈t,HasFDerivAt (j m e) (fderiv ℝ (j m g) x) x):= by
       have hU (x:E)(hi:x∈s): HasFDerivWithinAt (j m e) (fderiv ℝ (j m f) x) s x:= ((U _ hh x).hasFDerivAt.hasFDerivWithinAt).congr (fun _ h=>p.1 h) (p.1 hi)
       have hV (x:E)(hi:x∈t): HasFDerivWithinAt (j m e) (fderiv ℝ (j m g) x) t x:= ((V _ hh x).hasFDerivAt.hasFDerivWithinAt).congr (fun _ h=>p.2 h) (p.2 hi)
       have he (x:E)(u:x∈s)(v:x∈t): fderiv ℝ (j m f) x=fderiv ℝ (j m g) x:= by unfold j;rw [fderiv_iteratedFDeriv,fderiv_iteratedFDeriv];exact congr_arg (⇑(continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m+1)=> E) ℝ)) (hc (m+1) hh ⟨u,v⟩)
       have hh x (hy:x∈s) : HasFDerivAt (j m e) (fderiv ℝ (j m f) x) x:= by
          by_cases ht':x∈t
          · exact hasFDerivWithinAt_univ.mp (h ▸ ((hU _ hy).union (he _ hy ht' ▸ hV _ ht')))
          refine (hU _ hy).hasFDerivAt (mem_of_superset (ht.isOpen_compl.mem_nhds ht') ?_); intro u p; exact (hx u).resolve_right p
       refine ⟨hh,fun x hv=>?_⟩; by_cases hi : x∈s; exact he _ hi hv ▸ hh x hi
       apply (hV _ hv).hasFDerivAt (mem_of_superset (hs.isOpen_compl.mem_nhds hi) ?_); intro v p; exact (hx v).resolve_left p
   have hh m (hD:m≤ D): P m := by
      induction m with
      | zero=>
         refine ⟨fun x hx=> ?_,fun x hx=>?_⟩ <;> ext1 <;> unfold j <;> rw [iteratedFDeriv_zero_apply,iteratedFDeriv_zero_apply] <;> first|exact hp hx| exact he hx
      | succ m ih=>
         have ht:= hm m hD (ih (by omega)); refine ⟨fun x hx=> ?_,fun x hx=>?_⟩
         · unfold j; rw [iteratedFDeriv_succ_eq_comp_left,iteratedFDeriv_succ_eq_comp_left, Function.comp_apply,Function.comp_apply]; exact congr_arg _ (ht.1 x hx).fderiv
         unfold j; rw [iteratedFDeriv_succ_eq_comp_left,iteratedFDeriv_succ_eq_comp_left, Function.comp_apply,Function.comp_apply]; exact congr_arg _ (ht.2 x hx).fderiv
   refine ⟨contDiff_nat_iff_continuous_differentiable.mpr ⟨fun m hp=> ?_,fun m hp x=> (hx x).elim (fun p=> ((hm m hp (hh m hp.le)).1 x p).differentiableAt) (fun p=> ((hm m hp (hh m hp.le)).2 x p).differentiableAt)⟩,hh⟩
   apply continuousOn_univ.mp; rw [←h]; exact ((F m hp).continuousOn.congr (hh m hp).1).union_of_isClosed ((G m hp).continuousOn.congr (hh m hp).2) hs ht
end YM.FormalBulk08.Annex
