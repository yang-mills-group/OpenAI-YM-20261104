import YM.Contacts.Pulse.Pins
/-! Linear temporal/logarithmic nodes of the Wick calculus. Includes ordinary-rank
zero in finite dimensions. -/
noncomputable section
set_option autoImplicit false
namespace YM.Pulse
open Function Set Filter Finset RG MvPolynomial
open scoped Classical BigOperators Topology NNReal
variable {ι κ α β : Type*} {n p q : ℕ} (g:α→α→ℝ)
def squeeze (F:Field (Fin (n+1)) α) : Field (Option (Fin n)) α := reorder (finSuccEquiv n) F
def stretch (F:Field (Option (Fin n)) α): Field (Fin (n+1)) α:=reorder (finSuccEquiv n).symm F
def meter (g:α→α→ℝ)(F:Field (Fin (p+1)) α)(H:Field (Fin (q+1)) α) : Field (Fin (p+q)) α:=
  ((((p+1)*(q+1):ℕ):ℝ)/2) • printRun (reorder finSumFinEquiv (stitch g (squeeze F) (squeeze H)))
def spanLift (n : ℕ) : Fin (n+2) ≃ Option (Option (Fin n)) := (finSuccEquiv _).trans (Equiv.optionCongr (finSuccEquiv _))
def sway (F:Field (Fin (n+2)) α): Field (Option (Option (Fin n))) α:=reorder (spanLift n) F
def degree (g:α→α→ℝ)(F:Field (Fin (n+2)) α) : Field (Fin n) α:=
  ((((n+2)*(n+1):ℕ):ℝ)/2) • printRun (loop g (sway F))

@[simp] lemma squeeze_notch (F:Field (Fin (n+1)) α)(x:α)(p: Fin n→α): squeeze F (vertex x p)= notch x F p:= by
  unfold squeeze reorder notch; apply congr_arg; ext1 i; exact Fin.cases (by simp) (fun i=>by simp) i
@[simp] lemma sway_notch (F:Field (Fin (n+2)) α)(x y:α)(p: Fin n→α): sway F (vertex x (vertex y p))= notch y (notch x F) p:= by
  unfold sway reorder spanLift notch; apply congr_arg; ext1 i; exact Fin.cases (by simp) (fun i=>Fin.cases (by simp only [Function.comp_apply,Equiv.trans_apply,finSuccEquiv_succ,Equiv.optionCongr_apply, Option.map_some,finSuccEquiv_zero,v_tail,v_head,Fin.cons_succ,Fin.cons_zero]) (fun _=>by simp) i) i

variable [Fintype α]
def cross (g:α→α→ℝ) : Plate α →ₗ[ℝ] Plate α→ₗ[ℝ] Plate α:= by
  let F (P Q: Plate α) := ∑ i:α,∑ j:α, C (g i j/2) * (pderiv i P * pderiv j Q)
  refine LinearMap.mk₂ ℝ F ?_ ?_ ?_ ?_
  all_goals intros; simp only [F,map_add,add_mul,mul_add,sum_add_distrib]
  · simp only [Derivation.map_smul,smul_mul_assoc,mul_smul_comm,Finset.smul_sum]
  · simp only [Derivation.map_smul,mul_smul_comm,Finset.smul_sum]
def lap (g:α→α→ℝ) : Plate α→ₗ[ℝ] Plate α := ∑ i:α,∑ j:α,(g i j/2) • (pderiv j).toLinearMap.comp (pderiv i).toLinearMap
lemma lap_apply (v:Plate α) : lap g v = ∑ i:α,∑ j:α, C (g i j/2) * pderiv j (pderiv i v):=by unfold lap; simp only [LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.comp_apply, ← C_mul']; rfl
lemma cross_apply (v w:Plate α): cross g v w=∑ i:α,∑ j:α,C (g i j/2) * (pderiv i v*pderiv j w) := rfl

private theorem align (F:Field (Fin (n+2)) α): loop g (sway F) = ∑ i:α,∑ j:α,g i j • notch j (notch i F):= by
  ext1 x; simp only [loop, tsum_fintype,Fintype.sum_prod_type,Finset.sum_apply, sway_notch]; rfl
private def buddy (F:Field ι α)(G:Field κ α) : Field (ι⊕κ) α := fun x=> F (x∘ Sum.inl)*G (x∘Sum.inr)
private theorem along (F:Field (Fin (p+1)) α)(H:Field (Fin (q+1)) α): stitch g (squeeze F) (squeeze H)=∑ i:α, ∑ j:α, g i j • buddy (notch i F) (notch j H) := by
  ext1 x; simp only [stitch,tsum_fintype,Fintype.sum_prod_type,Finset.sum_apply, squeeze_notch,buddy,Pi.smul_apply,smul_eq_mul,mul_assoc,mul_left_comm]
lemma lap_slot {F:Field (Fin (n+2)) α}(h:Poem F): verse (degree g F)=lap g (verse F):= by
  rw [degree,verse_scale',verse_print,align]; simp_rw [verse_sum,verse_scale',lap_apply, ← C_mul',C_mul',verse_pderiv h,map_nsmul,verse_pderiv (h.notched _),Finset.smul_sum]
  apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; simp_rw [← Nat.cast_smul_eq_nsmul ℝ]; module
lemma association [Fintype ι][Fintype κ](F:Field ι α)(G:Field κ α): verse (buddy F G)= verse F*verse G:= by
  let L:= Equiv.sumPiEquivProdPi (fun _:ι⊕κ=>α); unfold verse; trans ∑ i:(ι→α)×(κ→α), C (buddy F G (L.symm i))*∏ j:ι⊕κ,X (L.symm i j)
  · convert! (Equiv.sum_comp L.symm (fun x=>C (buddy F G x)*∏ j,X (x j))).symm using 1; congr 1; exact congr_arg (fun i : Fintype _ => @Finset.univ _ i) (Subsingleton.elim ..)
  simp_rw [Fintype.prod_sum_type,Fintype.sum_prod_type]; rw [sum_mul]; simp_rw [mul_sum]
  refine sum_congr rfl (fun i _=> sum_congr rfl (fun j _=>?_));
  change C (F i * G j) * ((∏ k:ι,X (i k)) * (∏ k:κ,X (j k)))=_; rw [map_mul]; ring
lemma cross_slot {F:Field (Fin (p+1)) α}{H:Field (Fin (q+1)) α}(h: Poem F)(hp:Poem H): verse (meter g F H)=cross g (verse F) (verse H):= by
  rw [meter,verse_scale',verse_print,verse_renew,along]; simp_rw [verse_sum,verse_scale',association, Finset.smul_sum,cross_apply, C_mul', verse_pderiv h,verse_pderiv hp]
  apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; simp_rw [← Nat.cast_smul_eq_nsmul ℝ, smul_mul_assoc,mul_smul_comm]; module
end YM.Pulse
