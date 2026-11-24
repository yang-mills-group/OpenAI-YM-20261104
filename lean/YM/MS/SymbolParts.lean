import YM.MS.Symbol

/-! Partial symbol estimates for inductive proofs of kernel bounds. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS
open Set Function Real
open scoped ContDiff
variable {ι E F G H α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  {S : Scale ι} {T : Cost ι E} {f f' : Kern ι E F} {g g' : Kern ι E ℝ}
variable {j : ℕ}
namespace Cost.Part
lemma start : T.Part S f g 0 ↔ T.Le (fun i p=> ‖f i p‖) g := by simp [Cost.Part]
lemma next : T.Part S f g (j+1) ↔ T.Part S (fun i=> _root_.fderiv ℝ (f i)) (fun i p=>g i p*S.length i) j := by
  simp only [Part, norm_iteratedFDeriv_fderiv]
  congr! 2; rw [pow_succ]; funext; ring
lemma adjust (h : T.Part S f g j) (h' : T.Le g g') : T.Part S f g' j :=
  Cost.Le.trans h (h'.cancel (fun _ _ _=>pow_nonneg (S.pos _).le _))
lemma add (h : T.Part S f g j) (hf : ∀ i, ContDiff ℝ ∞ (f i)) (t : T.Part S f' g j) (hf' : ∀ i, ContDiff ℝ ∞ (f' i)) :
    T.Part S (fun i p=> f i p+ f' i p) g j :=
  (Cost.Le.add h t (Cost.nn_of_le h (fun _ _ _=>norm_nonneg _))).left fun i p _=> by
     change ‖iteratedFDeriv ℝ j (f i+ f' i) p‖ ≤ _
     rw [iteratedFDeriv_add ((hf _).of_le (by exact_mod_cast le_top)) ((hf' _).of_le (by exact_mod_cast le_top)), Pi.add_apply]; exact norm_add_le ..
protected lemma bilinear {u : Kern ι E G} (A : F →L[ℝ] G →L[ℝ] H) (hf : ∀ i, ContDiff ℝ ∞ (f i)) (hu : ∀ i, ContDiff ℝ ∞ (u i))
    (hh : ∀ k≤ j, T.Part S f g k) (ht : ∀ k≤j,T.Part S u g' k) : T.Part S (fun i p => A (f i p) (u i p)) (fun i p => g i p * g' i p) j := by
    let F' (k : ℕ) := fun i p => (j.choose k:ℝ)*‖iteratedFDeriv ℝ k (f i) p‖ * ‖iteratedFDeriv ℝ (j-k) (u i) p‖
    let R i p := g i p*g' i p*S.length i^j
    have hR : T.NN R := fun i p hx => mul_nonneg (mul_nonneg (Part.nonneg _ (hh _ le_rfl) i p hx) (Part.nonneg _ (ht _ le_rfl) i p hx)) (pow_nonneg (S.pos _).le _)
    have h (k : ℕ) (hk : k ∈ Finset.range (j+1)) : T.Le (F' k) R := by
      have hle : k ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have hm := Cost.Le.mul (hh k hle) (ht (j-k) (by omega)) (fun _ _ _ => norm_nonneg _) (fun _ _ _ => norm_nonneg _)
      refine Cost.Le.left (Cost.Le.const_mul (Cost.Le.right hm (u:=R) (fun i p _ => ?_)) (j.choose k : ℝ) (by positivity) hR) fun i p _ => (mul_assoc _ _ _).le
      unfold R; conv_rhs => rhs; arg 2; rw [← Nat.add_sub_of_le hle]
      rw [pow_add]; ring_nf; rfl
    refine ((Cost.Le.finset_sum (Finset.range (j+1)) h hR).const_mul ‖A‖ (norm_nonneg A) hR).left fun i p _ => ?_
    exact A.norm_iteratedFDeriv_le_of_bilinear (hf i) (hu i) p (by exact_mod_cast le_top)
end Cost.Part
namespace Costs
lemma fderiv (h : Costs T S f g) : Costs T S (fun i=> _root_.fderiv ℝ (f i)) (fun i p=>g i p*S.length i) where
  smooth i := (contDiff_infty_iff_fderiv.1 (h.smooth i)).2
  quoted _ := Cost.Part.next.1 (h.quoted _)
lemma scalar {p : ι → F} (hg : T.Le (fun i _ => ‖p i‖) g) : Costs T S (fun i _ => p i) g := by
  refine ⟨fun _ => contDiff_const, fun j=>?_⟩; cases j
  exact Cost.Part.start.mpr hg
  apply Cost.of_le; intro i x hx
  simp only [iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero]; exact mul_nonneg (Cost.nn_of_le hg (fun _ _ _=> norm_nonneg _) i x hx) (pow_nonneg (S.pos _).le _)

variable {u v : Kern ι E ℝ}
lemma smul (h : Costs T S u g') (h' : Costs T S f g) : Costs T S (fun i p=>u i p • f i p) (fun i p=>g' i p*g i p) :=
  Costs.bilinear (ContinuousLinearMap.lsmul ℝ ℝ (E:=F)) h h'
lemma rmul (h : Costs T S u g) (h' : Costs T S v g') : Costs T S (fun i p=>u i p * v i p) (fun i p=>g i p*g' i p) :=
  Costs.bilinear (ContinuousLinearMap.mul ℝ ℝ) h h'
lemma pow (h : Costs T S u g) (b : ℕ) : Costs T S (fun i p=>u i p^b) (fun i p=>g i p^b) := by
  induction b with
  | zero => simp; exact Costs.scalar (p:=fun _ => (1:ℝ)) (Cost.of_le (by simp))
  | succ j ih => simp_rw [pow_succ]; exact ih.rmul h
lemma ofReal (h : Costs T S u g) : Costs T S (fun i p => (u i p : ℂ)) g := h.L Complex.ofRealCLM
lemma exp_full {f:Kern ι E ℝ} (h : Costs T S f fun _ _=> 1) : Costs T S (fun i p=>exp (f i p)) (fun i p=>exp (f i p)) := by
  let G i p:= exp (f i p); let F i p:= _root_.fderiv ℝ (f i) p
  have H i : ContDiff ℝ ∞ (G i) := (h.smooth i).exp
  refine ⟨H, ?_⟩; intro j; induction j using Nat.strong_induction_on with
  | _ j IH =>
    cases j with
    | zero => exact Cost.Part.start.2 (Cost.of_le fun _ _ _=> (norm_of_nonneg (exp_pos _).le).le) -- adjust namespace
    | succ n =>
      apply Cost.Part.next.2; change T.Part S (fun i=> _root_.fderiv ℝ (G i)) _ n
      have hξ : (fun i=> _root_.fderiv ℝ (G i)) = fun i p=> G i p • F i p := by
         funext; exact _root_.fderiv_exp ((h.smooth _).differentiable (by simp) _)
      rw [hξ]; change T.Part S (fun i p=> G i p • F i p) (fun i p=> G i p * S.length i) n
      apply Cost.Part.bilinear (A:=ContinuousLinearMap.lsmul ℝ ℝ) H h.fderiv.smooth (fun i hi=> IH i (by omega))
        (g':=fun i _=>S.length i)
      exact fun i _=> by simpa [F] using h.fderiv.quoted i
end Costs
end YM.MS
