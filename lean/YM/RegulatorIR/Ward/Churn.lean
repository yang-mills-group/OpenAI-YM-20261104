import YM.RegulatorIR.Ward.Fount
import YM.RegulatorIR.Primitives.Firn

/-!
# Script of Ward substitution (finite arrays)

TPS with height k propagating across smooth paths at fixed regulator. This
step bounded k, not uniform for cost. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Ward
open Function Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim Finset PowerSeries Gradient Laplace
open scoped Topology ENNReal BigOperators Classical PowerSeries ContDiff
variable {I J E: Type}{G : Gauge}{i e k a b m:ℕ}{S T:PowerSeries ℝ}

section Eval
variable (x : ℝ→ I →ℝ)
abbrev Lift (x:ℝ→I→ℝ): Prop:=∀ i, ContDiffAt ℝ ∞ (fun t:ℝ=> x t i) 0

def churn : Jet I →ₐ[ℝ] ℝ⟦X⟧:= MvPolynomial.aeval (fun i=>tale (fun t=>x t i))
lemma ink (h:Lift x) (P:Jet I) : Script (churn x P) (fun t=>MvPolynomial.eval (x t) P):=by
 induction P using MvPolynomial.induction_on with
 | C k=> simp [churn]; exact Script.oneC k
 | add f g hf hg=> rw [map_add];simp_rw [map_add];exact Script.add hf hg
 | mul_X f i h' => rw [map_mul,show (churn x) (MvPolynomial.X i)= _ from MvPolynomial.aeval_X ..]; simp_rw [map_mul,MvPolynomial.eval_X];exact Script.mul h' (Script.actual (h i))
lemma script_sum (n:ℕ)(P:PowerSeries (Jet I))(h:Lift x) : Script (Cluster.sieve (churn x).toRingHom P n) (∑ i ∈ Finset.range (n+1), fun t:ℝ=> MvPolynomial.eval (x t) (coeff i P)*t^i) :=by
 let p:ℕ→PowerSeries ℝ:=fun i=>churn x (coeff i P)* PowerSeries.X^i; let f:=fun i (t:ℝ)=> MvPolynomial.eval (x t) (coeff i P)*t^i
 have hx (i:ℕ): Script (p i) (f i):=Script.mul (ink x h _) (Script.predicts_pow _)
 unfold Script; refine ((?_ : (∑ i∈Finset.range (n+1), term (p i))=term (Cluster.sieve (churn x).toRingHom P n)) ▸ Aspiration.sum _ _ _ fun i _=>hx i)
 ext1 i; simp_rw [Finset.sum_apply, term, sieve,map_sum]; rfl
end Eval

lemma scale_script (X: ℝ →ℝ)(HX:ContDiffAt ℝ ∞ X 0) (u:ℝ→ I→ ℝ) (H:Lift u)(P: PowerSeries (Jet I))(m:ℕ) : Bill (m+1) ((X*(∑ i∈Finset.range (m+1),fun t:ℝ=>MvPolynomial.eval (u t) (coeff i P)*t^i)) - peval (term (tale X * ocean (churn u) P)) m) := by
 have h:= Script.mul (Script.actual HX) (script_sum u m P H) m
 suffices he : peval (term (tale X*Cluster.sieve _ P m)) m=peval (term (tale X * ocean (churn u) P)) m from he ▸ h
 ext1 t; apply Finset.sum_congr rfl; intro i hi; apply congr_arg (_ • ·); apply Squares.maintains (e:=m) (show Squares m (tale X) (tale X) from fun _ _=>rfl) _ i (by rw [Finset.mem_range] at hi; omega)
 exact fun v hv=> Eq.symm (flows (churn u).toRingHom _ hv)
-- underscore fix

variable [Fintype J][Fintype E]
omit [Fintype J] in
lemma prolong (F:ℝ → Meadow G E → ℝ)(U:Meadow G E→ℕ→ℝ)(B:Rated G E F U)
  (K:Meadow G E→ℝ)(p:Meadow G E→(J→ℝ)) (T:PowerSeries (Jet J))
  (h:∀ w,PowerSeries.mk (U w)=PowerSeries.C (K w)*PowerSeries.map (MvPolynomial.eval (p w)) T)
  (y:ℝ→Meadow G E) (C: ContinuousAt y 0)(ht:ContDiffAt ℝ ∞ (K ∘ y) 0)(hq:Lift (p ∘ y)) : Script (tale (K ∘ y)*ocean (churn (p ∘ y)) T) (fun t=>F t (y t)):=by
 intro n
 let X:= (K ∘ y)*(∑ i∈ Finset.range (n+1), fun t:ℝ=>MvPolynomial.eval ((p ∘ y) t) (coeff i T)*t^i)
 let P:= peval (term (tale (K ∘ y)*ocean (churn (p ∘ y)) T)) n
 let Z:=fun t:ℝ=>F t (y t)
 have he(t:ℝ): X t=peval (U (y t)) n t:=by
    unfold X; rw [Pi.mul_apply, Finset.sum_apply]; unfold peval Zone.eval; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
    dsimp only; rw [show U (y t) i=coeff i (PowerSeries.mk _) from (coeff_mk i _).symm,h, coeff_C_mul,coeff_map]; simp only [Function.comp_apply,smul_eq_mul];ring
 have hu: Bill (n+1) (Z-X):=by
    let R:=‖y 0‖+1; obtain ⟨c,hc,H⟩:= B R (by unfold R;positivity) n; refine ⟨c,hc,?_⟩; have hs: ‖y 0‖<R:=by unfold R; linarith
    filter_upwards [H,(C.norm.tendsto.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds hs)] with t ht hr; rw [Pi.sub_apply,he]; exact ht _ (le_of_lt (show ‖y t‖<R from hr))
 change Bill _ (Z-P)
 rw [show Z-P= (Z-X)+(X-P) by abel]; exact bill_add hu (scale_script _ ht _ hq T _)
end YM.RegulatorIR.Ward
