import YM.OPE.Compatible.Dale.Lip
import YM.PertExtension.GaussianIBP
/-!
# Real Polynomial Gaussian charges. Virtually dispense every order needed here but only order two x comparisons eventually claimed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra
open Function Filter Set Lattice Laurent Tree Woody Weir Cascade MeasureTheory LinearMap
open scoped Topology BigOperators ComplexConjugate Classical ContDiff ENNReal
open PertExtension Series GaussianScore
variable {E F:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]
local notation "V" => Module.Dual ℝ E
-- proof constructors
inductive Bond : (E→ℝ)→ Prop
  | keep (c:ℝ) : Bond fun _=> c
  | glyph (c:V) : Bond c
  | add {u v : E→ℝ}: Bond u→ Bond v→ Bond (u+v)
  | mul {u v : E→ℝ}: Bond u→ Bond v→ Bond (u*v)
namespace Bond
variable {u v:E→ℝ}
@[simp] lemma zero : Bond (0:E→ℝ):= keep 0
@[simp] lemma one : Bond (1:E→ℝ):= keep 1
protected lemma scale (c:ℝ)(h: Bond u): Bond (c • u):=(keep c).mul h
protected lemma neg (h:Bond u):Bond (-u):=by simpa using Bond.scale (-1) h
protected lemma sub (h:Bond u)(hh:Bond v):Bond (u-v):=by rw [sub_eq_add_neg]; exact h.add hh.neg
protected lemma pow (p:ℕ)(h:Bond u): Bond (u^p):=by induction p with | zero=>rw [pow_zero]; exact one | succ i ih=> rw [pow_succ]; exact ih.mul h
protected lemma sum {ι:Type*}(p:ι→E→ℝ)(s:Finset ι)(h:∀ i∈s,Bond (p i)): Bond (fun i=>∑ j∈s,p j i):=by
     rw [show (fun i=>∑ j∈s,p j i)=(∑ i∈s,p i) from funext fun i=>by simp only [Finset.sum_apply]]; induction s using Finset.induction_on with
     | empty=>rw [Finset.sum_empty]; exact zero
     | insert i s hi ih=> rw [Finset.sum_insert hi]; exact (h i (by simp)).add (ih fun j hj=> h _ (Finset.mem_insert_of_mem hj))
protected lemma product {ι:Type*}(p:ι→E→ℝ)(s:Finset ι)(h:∀ i∈s,Bond (p i)): Bond (fun i=>∏ j∈s,p j i):=by
     rw [show (fun i=>∏ j∈s,p j i)=(∏ i∈s,p i) from funext fun i=>by simp only [Finset.prod_apply]]; induction s using Finset.induction_on with
     | empty=>rw [Finset.prod_empty]; exact one
     | insert i s hi ih=> rw [Finset.prod_insert hi]; exact (h i (by simp)).mul (ih fun j hj=> h _ (Finset.mem_insert_of_mem hj))
variable [FiniteDimensional ℝ E]
protected lemma cost (hf:Bond u) : Zone.Invoice Radial.zone u:=by
    induction hf with
    | keep c=> exact Zone.Invoice.const c
    | glyph c=> exact Law.linearInvoice c
    | add _ _ p q=> exact p.add q
    | mul _ _ p q=> exact p.mul q
protected lemma smooth (hf:Bond u): ContDiff ℝ ω u:=by
    induction hf with
    | keep=> exact contDiff_const
    | glyph c=> exact (toContinuousLinearMap c).contDiff
    | add _ _ p q=> exact p.add q
    | mul _ _ p q=> exact p.mul q
lemma amount (w:E)(hf:Bond u): Bond fun i:E=> fderiv ℝ u i w:=by
    induction hf with
    | keep c=> simp; exact keep 0
    | glyph c=>
      have hh(i:E): fderiv ℝ (fun x=> c x) i w=c w:=congr_arg (fun h:E →L[ℝ] ℝ=>h w) (toContinuousLinearMap c |>.hasFDerivAt (x:=i) |>.fderiv)
      convert keep (E:=E) (c w) using 1; exact funext hh
    | @add p q h j ih wh=>
      convert ih.add wh using 1; funext i; rw [fderiv_add (h.smooth.differentiable (by simp)|>.differentiableAt) (j.smooth.differentiable (by simp)|>.differentiableAt)];rfl
    | @mul p q h j ih wh=>
      convert (h.mul wh).add (j.mul ih) using 1; funext i; rw [fderiv_mul (h.smooth.differentiable (by simp)|>.differentiableAt) (j.smooth.differentiable (by simp)|>.differentiableAt)]; rfl
variable [NormedAddCommGroup F][NormedSpace ℝ F]
omit [FiniteDimensional ℝ E] in protected lemma comp {w:F→E}(h:Bond u)(hh:∀ ℓ:V,Bond (fun x:F=>ℓ (w x))): Bond (fun x=> u (w x)) := by induction h with
    | keep c=> exact keep c
    | glyph c=> exact hh _
    | add _ _ p q=> exact p.add q
    | mul _ _ p q=> exact p.mul q
omit [FiniteDimensional ℝ E] in protected lemma compLinear (w:F→ₗ[ℝ] E)(h:Bond u) : Bond (u ∘ w):= h.comp fun c=> glyph (c.comp w)
-- tangent tensor reading, polarization dispose estimate afterwards
lemma multiline {ι:Type*}[Fintype ι](A:ContinuousMultilinearMap ℝ (fun _ : ι=> E) ℝ)(w:ι→F→E)(h:∀ i:ι,∀ ℓ:V,Bond (fun x:F=>ℓ (w i x))): Bond fun x=> A (fun i=> w i x):=by
    let b:= Module.finBasis ℝ E; let W:= Fin (Module.finrank ℝ E); have hu(x:F): A (fun i=>w i x)= ∑ p:ι→ W,(A (fun i=> b (p i)))*(∏ i,b.coord (p i) (w i x)):=by
        have hv : (fun i=> w i x)=fun i=> ∑ j:W, (b.coord j (w i x)) • b j:=funext fun i=>(b.sum_repr _).symm
        nth_rw 1 [hv]; -- `map_sum_finset` ?
        rw [show A (fun i=> _)= _ from A.map_sum_finset ..]; rw [show Fintype.piFinset (fun _ : ι=> (Finset.univ: Finset W))=Finset.univ from by ext; simp]; apply Finset.sum_congr rfl; intro p _; rw [A.map_smul_univ]; apply mul_comm
    rw [funext hu]; apply Bond.sum _ _; intro p _; exact (Bond.keep _).mul (Bond.product _ _ fun i _=> h _ _)
end Bond
end YM.OPE.Libra
