import YM.Next.FOUNDATIONS.TestBounds

/-! Spatially cropped nonlinear original source probes with their genuine volume-independent derivative price. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichCroppedProbe
open Function Filter Lattice Wilson Source RG Labels Next.Foundations
open scoped Topology Classical ContDiff BigOperators Matrix.Norms.Frobenius
open private mixed_budget from YM.Next.FOUNDATIONS.TestBounds
variable {G:Gauge} {n:Side}

def mask (A : Finset (Edge (Site n))) : Directions G n →L[ℝ] Directions G n :=
  ContinuousLinearMap.pi (fun e=>if e∈A then ContinuousLinearMap.proj e else 0)

lemma mask_on (A : Finset (Edge (Site n))) {e} (he:e∈A) (W:Directions G n) : mask A W e = W e := by
  simp [mask,he]
lemma mask_off (A : Finset (Edge (Site n))) {e} (he:e∉A) (W:Directions G n) : mask A W e = 0 := by
  simp [mask,he]

lemma masked_jet (A : Finset (Edge (Site n))) {z:ℝ→Directions G n} (h : ContDiffAt ℝ ω z 0) (k:ℕ) :
    iteratedDeriv k (mask A ∘ z) 0 = mask A (iteratedDeriv k z 0) := by
  unfold iteratedDeriv
  rw [(mask A).iteratedFDeriv_comp_left h le_top];rfl

def fields (A : Finset (Edge (Site n))) (H:Hol G) (d : ℕ) (o:Site n) (J:Jet G) (t:ℝ) : Config G n :=
  increment 1 (mask A (testLog H d o J t))

lemma agree {X:Support n} {f:Config G n→ℂ} (sites : LocalOn X f) (A : Finset (Edge (Site n)))
    (covers : ∀ (e:Edge (Site n)),e.1∈X → e.1+Lattice.step e.2∈X → e∈A)
    (H:Hol G) (d:ℕ) (o:Site n) (J:Jet G) : f ∘ fields A H d o J =ᶠ[𝓝 0] f ∘ H.testLinks d o J := by
  filter_upwards [increment_testLog H d o J] with t ht
  apply sites;intro e hr hs
  change increment 1 (mask A (testLog H d o J t)) e=H.testLinks d o J t e
  rw [ht];simp [increment,mask_on A (covers e hr hs)]

theorem price (H : Hol G) (J : Jet G) (d k : ℕ) (hk : k ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : Side) (o : Site n) (X : Support n) (B : BudgetPoint)
        (f : Config G n → ℂ) (c : ℝ) (A : Finset (Edge (Site n))),
      d ≤ B.order → d ≤ B.power → B.Regular X f → B.supBounds o X f c →
        ‖iteratedDeriv k (f ∘ fields A H d o (B.threshold • J)) 0‖ ≤ C*c := by
  choose a ha h using fun i : ℕ => testLog_bound H d i J
  choose b hb e using fun r : OrderedFinpartition k => mixed_budget G r.length
    (fun i => a (r.partSize i)) (fun i => (ha _).le)
  refine ⟨∑ i, b i, Finset.sum_nonneg fun i _ => hb i, fun n o X B f c A hv hP hf hc => ?_⟩
  let z := testLog H d o (B.threshold • J)
  let Z := mask (G:=G) A ∘ z
  let F := f ∘ increment (1 : Config G n)
  have hz : Z 0 = 0 := by dsimp [Z,z];rw [testLog_zero,map_zero]
  have hU := one_healthy (G:=G) X B.threshold B.threshold_pos.le
  have hg : ContDiffAt ℝ (B.order : WithTop ℕ∞) F (Z 0) := hz.symm ▸ hf.smooth 1 hU
  have hd : ContDiffAt ℝ (B.order : WithTop ℕ∞) Z 0 := ((mask (G:=G) A).contDiff.contDiffAt.comp 0 (testLog_diff H d o (B.threshold • J))).of_le le_top
  change ‖iteratedDeriv k (F ∘ Z) 0‖ ≤ _
  rw [iteratedDeriv_vcomp_eq_sum_orderedFinpartition hg hd
    (Nat.cast_le.mpr (hk.trans hv)), hz, Finset.sum_mul]
  apply le_trans (norm_sum_le ..)
  refine Finset.sum_le_sum fun r _ => e r B n X o f c (r.length_le.trans (hk.trans hv)) hf hc _ ?_
  intro i l
  let j := r.partSize i
  have hj : j ≤ B.power := (r.partSize_le i).trans (hk.trans hP)
  let y : ℝ := 1+(separation l.1 o : ℝ)
  have hy : 1 ≤ y := by simp [y]
  rw [show iteratedDeriv (r.partSize i) Z 0 = mask A (iteratedDeriv (r.partSize i) z 0) from masked_jet A (testLog_diff H d o (B.threshold • J)) _]
  by_cases member : l∈A
  · rw [mask_on A member]
    apply (h (r.partSize i) n o l _ B.threshold_pos.le B.threshold_le).trans
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hy ((Nat.sub_le j 1).trans hj))
      (mul_nonneg (ha _).le B.threshold_pos.le)
  · rw [mask_off A member,norm_zero]
    exact mul_nonneg (mul_nonneg (ha _).le B.threshold_pos.le) (pow_nonneg (zero_le_one.trans hy) _)

end YM.Integration.WilsonMacroscopicRichCroppedProbe
