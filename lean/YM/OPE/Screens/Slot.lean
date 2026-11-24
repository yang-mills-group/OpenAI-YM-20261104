import YM.OPE.Screens.Booking
/-! # Rebuild a whole row after matching. All physical components -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open Function Filter Finset MeasureTheory Lattice RG Wilson Next.UVStress Spec
open scoped Topology BigOperators Classical ContDiff
namespace Prescription
variable {I J Z : Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J] {G: Gauge}
  {S:Register G}{T:Table S}{M:DiffPlan T}(R:Prescription M)(h:T.Symmetric)(hp:M.Inclusions T)(hR:R.Coherent)
  (w: Mode M){z z':E4}{x:I→ E4}{v:I→ S.Token} {k:ℕ} (b:S.Ref k)
include h hp hR
lemma one_atom (p: Exterior S)(z z':E4) (b:S.Ref k) : reading T (sole z) (sole ⟨k,b⟩) z' p = ∑ i∈ bands M k,R.test i k (T.project k b)*reading T (sole z) (sole (R.letter i)) z' p:=by
    let u(i:Unit):= z-z'; by_cases hx:Injective (beside u (bearing p))
    · unfold reading; change Injective (beside (fun i=> sole z i - z') (bearing p)) at hx; dsimp only; simp_rw [if_pos hx]; exact (sumAll (z:=z-z') T R p.letter hp h (fun _=>le_rfl) hx hR b).symm
    unfold reading; change ¬ Injective (beside (fun i=> sole z i - z') (bearing p)) at hx; dsimp only; simp_rw [if_neg hx,mul_zero]; simp
-- slot arbitrary order. Use sumAssoc to reorder filtered word after translation.
lemma two_at (p:Exterior S)(z z':E4)(x:I→E4)(v:I→ S.Token)(b:S.Ref k) : reading T (beside (sole z) x) (beside (sole (⟨k,b⟩:S.Token)) v) z' p = ∑ i∈ bands M k,R.test i k (T.project k b)* reading T (beside (sole z) x) (beside (sole (R.letter i)) v) z' p:=by
    let u:= beside (fun i=> beside (sole z) x i - z') (bearing p); by_cases ht:Injective u
    · let e:=Equiv.sumAssoc Unit I (Fin p.n); let y:= beside (away x z') (bearing p); let w:= beside v p.letter; let o:= z-z'; have he: u=beside (sole o) y ∘ e:=funext fun j=>by rcases j with (j|j)|j<;>rfl
      have hx:Injective (beside (sole o) y):= by rw [he] at ht; intro i j h; obtain ⟨i,rfl⟩:=e.surjective i; obtain ⟨j,rfl⟩:=e.surjective j; exact congr_arg e (ht h)
      have hf(g:S.Token): reading T (beside (sole z) x) (beside (sole g) v) z' p=observe T (beside (sole o) y) (beside (sole g) w):=by
          unfold reading; rw [if_pos ht]; let L:= beside (sole g) w; change observe T u _= _; rw [he,show beside (beside (sole g) v) p.letter= L ∘ e from (by funext i; rcases i with (i|i)|i <;>rfl)]; exact perm_observe T h _ _ hx
      simp_rw [hf]; exact (sumAll T R _ hp h (fun _=>le_rfl) hx hR b).symm
    unfold reading; unfold u at ht; dsimp only; simp_rw [if_neg ht,mul_zero]; simp
lemma phaseAtOne (z z':E4) : R.ope w (sole z) (sole ⟨k,b⟩) z'=∑ i∈ bands M k,R.test i k (T.project k b)* R.ope w (sole z) (sole (R.letter i)) z':=by unfold ope; simp_rw [one_atom (b:=b) R h hp hR,mul_sum]; rw [sum_comm]; exact sum_congr rfl fun i _=>sum_congr rfl fun j _=>mul_left_comm ..
lemma phaseAtRows (z z':E4)(x:I→E4)(v:I→ S.Token) : R.ope w (beside (sole z) x) (beside (sole ⟨k,b⟩) v) z'=∑ i∈ bands M k,R.test i k (T.project k b)* R.ope w (beside (sole z) x) (beside (sole (R.letter i)) v) z':=by unfold ope; simp_rw [two_at (b:=b) R h hp hR, mul_sum]; rw [sum_comm]; exact sum_congr rfl fun i _=>sum_congr rfl fun j _=>mul_left_comm ..
end Prescription
end YM.OPE
