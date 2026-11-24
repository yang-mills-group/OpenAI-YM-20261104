import YM.Contacts.Procession.Span
/-!
# Specialization of formal response in extra registers
-/
noncomputable section
namespace YM.Contacts.Procession.Sun
open Function Set Filter Pulse Pulse.Form Finset
open Milling Milling.Forge MvPolynomial
open scoped Classical Topology BigOperators NNReal
variable {α β : Type} {t k e i : ℕ}
section
variable (J:α ↪ β)(j:β→ℝ)
def sign (b:β): Plate α:= if H: b∈ Set.range J then MvPolynomial.X H.choose else MvPolynomial.C (j b)
def castP : Plate β→ₐ[ℝ] Plate α:= aeval (sign J j)
lemma sortPass (i:α) : sign J j (J i)=X i:=by
    unfold sign; split
    next h=> exact congr_arg _ (J.injective h.choose_spec)
    next h=> exact (h ⟨i,rfl⟩).elim
lemma pulses (q:Plate β)(i:α) : castP J j (pderiv (J i) q)=pderiv i (castP J j q):= by
   induction q using MvPolynomial.induction_on with
   | C a=> simp [castP]
   | add x y h hh=> simp [h,hh]
   | mul_X q v ih =>
     have he: castP J j (pderiv (J i) (X v)) = pderiv i (castP J j (X v)):= by
       by_cases h:v∈ Set.range J
       · obtain ⟨r,rfl⟩:= h; by_cases e:r=i <;> simp [castP, pderiv_X,e, Function.update_of_ne, sortPass (α:=α), J.injective.eq_iff, Pi.single_apply, eq_comm]
       simp [castP,sign,h,pderiv_X, Pi.single_apply, show v≠J i from fun e=> h ⟨_,e.symm⟩, eq_comm]
     simp only [Derivation.leibniz,smul_eq_mul,map_mul,map_add,he,ih]
lemma merch (x:α→ℝ)(r:β→ℝ) (h:∀ i:β, aeval x (sign J j i)=r i)(p:Plate β) : aeval x (castP J j p)=aeval r p:= by
   rw [show aeval r=(aeval x).comp (castP J j) from ?_]; rfl; ext i; simp only [AlgHom.comp_apply,castP,aeval_X,h]
variable {G:β→β→ℝ}{g:α→α→ℝ}
structure Pulses (G:β→β→ℝ) (g:α→α→ℝ) : Prop where
   here a b : G (J a) (J b)=g a b
   left a b : a∉ Set.range J → G a b=0
   right a b : b∉ Set.range J → G a b=0
variable [Fintype α][Fintype β]
private lemma hush (F:β→Plate α)(hf:∀ a,a∉ Set.range J → F a=0): ∑ i:β,F i=∑ i:α,F (J i):= by
    rw [← Finset.sum_map, Finset.sum_subset (subset_univ (univ.map J))]; intro x _ hx; apply hf x; simpa using hx
variable {J}
namespace Pulses
variable (h:Pulses J G g)
include h
private lemma taper (f:ℝ→ Plate α→ Plate α)(P:β→β→Plate α)(Q:α→α→Plate α) (hZ:∀ i,f 0 i=0)(hp:∀ i j,P (J i) (J j)=Q i j): ∑ i:β,∑ j:β,f (G i j) (P i j)=∑ i:α,∑ j:α, f (g i j) (Q i j) := by
    rw [hush J (fun i=> ∑ j:β,f (G i j) (P i j))]; refine sum_congr rfl fun i _=>?_ ; rw [hush J]; simp_rw [h.here,hp]; intro i hi; rw [h.right _ _ hi,hZ]; intro i hi; exact Finset.sum_eq_zero (fun l _=>by rw [h.left _ _ hi,hZ]) -- scoping
lemma tax (p:Plate β) : castP J j (lap G p)=lap g (castP J j p):= by
   simp only [lap_apply,map_sum,map_mul,castP,aeval_C]; apply taper h (fun x z=> C (x/2)*z) _ _ (fun i => by simp) (fun i k=>?_); change castP _ _ _ = _; rw [pulses,pulses]; rfl
lemma air (p q:Plate β) : castP J j (cross G p q)=cross g (castP J j p) (castP J j q):= by
   simp only [cross_apply,map_sum,map_mul,castP,aeval_C]; apply taper h (fun x z=> C (x/2)*z) _ _ (fun i=> by simp) (fun i k=>?_); exact congr_arg₂ (·*·) (pulses ..) (pulses ..)
lemma switch {A:House α}{H:House β} (hA:Snug A)(hH:Snug H)(i:ℕ)(hi:∀ i≤ e,castP J j (stage i (H i))= stage i (A i)) : castP J j (stage e (gathering G H i e))=stage e (gathering g A i e):= by
   induction i using Nat.strongRecOn generalizing e with| _ n ih=>
   cases n; · rw [gathering_start,gathering_start]; apply hi e le_rfl
   rename_i n; apply nsmul_right_injective (M:=Plate α) (n:=n+1) (by omega); -- name
   dsimp only; rw [← map_nsmul, staging G hH, staging g hA]; simp_rw [map_add,h.tax,map_sum,h.air]; rw [ih n (by omega) hi]; apply congr_arg; apply sum_congr rfl; intro i hiQ; apply sum_congr rfl; intro q hq; have he':=mem_antidiagonal.mp hq; have ht:=mem_antidiagonal.mp hiQ; rw [ih q.1 (by omega) (fun j hj=> hi j (by omega)), ih q.2 (by omega) (fun j hj=> hi j (by omega))]
lemma ramp {A:House α}{H:House β} (hA:Snug A)(hH:Snug H)(hi:∀ i≤ e,castP J j (stage i (H i))= stage i (A i)): castP J j (stage e (massaged G H e))= stage e (massaged g A e):= by
   have hv (i) := h.switch j hA hH i hi; have he (V:Type) (H:Fintype V)(Z:House V)(q:V→V→ℝ): stage e (massaged q Z e)= ∑ i∈Finset.range (3*e+1), stage e (gathering q Z i e):= by simp_rw [stage,massaged,verse_sum]; rw [sum_comm];
   rw [he β inferInstance,he α inferInstance,map_sum]; simp_rw [hv]
end Pulses
end
end YM.Contacts.Procession.Sun
