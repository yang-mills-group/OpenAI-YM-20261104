import YM.RGComparison.Core16.HistoryIntegral

/-! A terminal Wilson field and a second field inserted at the next observed
date are integrated over one actual forest and one common Haar history. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.WilsonTwoAgePath
open Lattice RG Tree Wilson Filter MeasureTheory RGComparison.Core16 RGComparison.Core16.Descent
open YM.Push.BetaTransport
open scoped Topology BigOperators Classical
variable {G : Gauge} {n c f : Side} (S : StepData c f) (T : Forest S.ratio) (D : Descent n f)
local notation "P" => Descent.push S T D

def middle (x : Fields G P) : Config G f := T.drape (x ∘ Sum.inl)

def joint (β : ℕ → ℝ) (A : Config G n → ℝ) (B : Config G f → ℝ) (V : Config G c) : ℝ :=
  S.push (β 1) (fun U => B U * D.weighted (upβ β) A U) V

def integrand (β : ℕ → ℝ) (t : (P).Tags) (A : Config G n → ℝ) (B : Config G f → ℝ)
    (V : Config G c) (x : Fields G P) : ℝ :=
  B (middle S T D x) * (P).integrand β t A V x

private theorem compose_env {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {u : X → ℝ} {v : Y → X} (h : Envelope u) (mv : Measurable v) : Envelope (u ∘ v) :=
  ⟨h.meas.comp mv,h.cost.choose,fun y => h.cost.choose_spec (v y)⟩

private theorem kernel (b : ℝ) (U : Config G f) (V : Config G c) :
    S.density b U V = Next.Fluctuations.Sector.prefactor S G b *
      ∑ t, S.likelihood U t * Real.exp (-(b * tagEnergy S t U V)) := by
  unfold StepData.density
  simp_rw [noise_factor]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  unfold tagEnergy YM.Push.BetaTransport.Gibbs.factor
  rw [neg_mul,mul_left_comm]

private theorem divided {u : Fields G P → ℝ} (hu : Integrable u ((P).measure G)) :
    ∫ z, u z ∂(P).measure G = ∫ a, ∫ x, u (Sum.elim a x) ∂D.measure G ∂T.order G := by
  let e := MeasurableEquiv.sumPiEquivProdPi (fun (_ : T.Free ⊕ D.Links) => G.El)
  have he : MeasurePreserving e.symm ((T.order G).prod (D.measure G)) ((P).measure G) :=
    measurePreserving_sumPiEquivProdPi_symm (fun _ => G.probHaar)
  exact (he.integral_comp' u).symm.trans
    (integral_prod _ ((he.integrable_comp_emb e.symm.measurableEmbedding).mpr hu))

private theorem cells (β : ℕ → ℝ) (a : S.Choices) (b : D.Tags) (A : Config G n → ℝ)
    (B : Config G f → ℝ) (V : Config G c) (U : T.Slice G) (w : Fields G D) :
    integrand S T D β (a,b) A B V (Sum.elim U w) =
      (B (T.drape U) * (S.likelihood (T.drape U) a * Real.exp (-(β 1 * tagEnergy S a (T.drape U) V)))) *
        D.integrand (upβ β) b A (T.drape U) w := by
  unfold integrand middle Descent.integrand
  rw [account, probability, fine]
  dsimp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, Prod.fst, Prod.snd]
  rw [neg_add,Real.exp_add]
  ring

private def palm (β : ℕ → ℝ) (t : S.Choices) (V : Config G c) (U : Config G f) :=
  S.likelihood U t * Real.exp (-(β 1 * tagEnergy S t U V))

private def terminal (β : ℕ → ℝ) (t : D.Tags) (A : Config G n → ℝ) (U : Config G f) :=
  ∫ w, D.integrand (upβ β) t A U w ∂D.measure G

private theorem entry (h : (P).OK G) (β : ℕ → ℝ) (t : (P).Tags)
    (A : Config G n → ℝ) (B : Config G f → ℝ) (hA : Continuous A) (hB : Continuous B)
    (V : Config G c) : Envelope (integrand S T D β t A B V) := by
  obtain ⟨L,hL⟩ := isCompact_univ.exists_bound_of_continuousOn hB.continuousOn
  have cap : Envelope B := ⟨hB.measurable,L,fun U=>hL U (Set.mem_univ _)⟩
  have mx : Measurable (middle S T D (G:=G)) :=
    T.continuous_drape.measurable.comp (measurable_pi_lambda _ fun _ => measurable_pi_apply _)
  have left : Envelope (fun x : Fields G (P) => B (middle S T D x)) :=
    compose_env (u:=B) (v:=middle S T D) cap mx
  have right : Envelope (fun x : Fields G (P) => (P).integrand β t A V x) :=
    compose_env (u:=fun z : Config G c × Fields G (P) => (P).integrand β t A z.1 z.2)
      (v:=fun x => (V,x)) (path_envelope h β t A hA) (measurable_const.prodMk measurable_id)
  exact left.mul right

private theorem cell_integral (β : ℕ → ℝ) (a : S.Choices) (b : D.Tags)
    (A : Config G n → ℝ) (B : Config G f → ℝ) (V : Config G c) (U : T.Slice G) :
    ∫ w, integrand S T D β (a,b) A B V (Sum.elim U w) ∂D.measure G =
      B (T.drape U) * palm S β a V (T.drape U) * terminal D β b A (T.drape U) := by
  simp_rw [cells,integral_const_mul]; rfl

private theorem outer (h : (P).OK G) (β : ℕ → ℝ) (a : S.Choices) (b : D.Tags)
    (A : Config G n → ℝ) (B : Config G f → ℝ) (hA : Continuous A) (hB : Continuous B)
    (V : Config G c) :
    Integrable (fun U=>B (T.drape U) * palm S β a V (T.drape U) * terminal D β b A (T.drape U)) (T.order G) := by
  simp_rw [← cell_integral S T D]
  have hm : Measurable fun z : T.Slice G × Fields G D => (Sum.elim z.1 z.2 : T.Free ⊕ D.Links → G.El) := by
    refine measurable_pi_lambda _ ?_
    intro i
    cases i
    · exact (measurable_pi_apply _).comp measurable_fst
    · exact (measurable_pi_apply _).comp measurable_snd
  exact ((compose_env (entry S T D h β (a,b) A B hA hB V) hm).integrable ((T.order G).prod (D.measure G))).integral_prod_left

private theorem kernel_sum (h : (P).OK G) (β : ℕ → ℝ) (A : Config G n → ℝ) (ha : Continuous A)
    (ga : GaugeInvariant A) (V : Config G c) (U : Config G f) :
    S.density (β 1) U V * D.weighted (upβ β) A U =
      (P).scalar G β * ∑ t : (P).Tags, palm S β t.1 V U * terminal D β t.2 A U := by
  rw [kernel, path_formula h.2 (upβ β) ha ga U]
  change (_ * _) * (D.scalar G (upβ β) * _) = _ * ∑ t : S.Choices × D.Tags,
    S.likelihood U t.1 * Real.exp (-(β 1 * tagEnergy S t.1 U V)) * ∫ w, D.integrand (upβ β) t.2 A U w ∂D.measure G
  conv_rhs => rhs; rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  rw [scalar]; ring

private theorem observed_sum (h : (P).OK G) (β : ℕ → ℝ) (A : Config G n → ℝ) (B : Config G f → ℝ)
    (ha : Continuous A) (ga : GaugeInvariant A) (V : Config G c) (U : Config G f) :
    S.density (β 1) U V * (B U * D.weighted (upβ β) A U) =
      (P).scalar G β * ∑ t : (P).Tags, B U * palm S β t.1 V U * terminal D β t.2 A U := by
  rw [mul_left_comm, kernel_sum S T D h β A ha ga V U,mul_left_comm,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem original (h : (P).OK G) (β : ℕ → ℝ) (A : Config G n → ℝ) (B : Config G f → ℝ)
    (hA : Continuous A) (gA : GaugeInvariant A) (hB : Continuous B) (gB : GaugeInvariant B)
    (V : Config G c) :
    joint S D β A B V = (P).scalar G β * ∑ t, ∫ x, integrand S T D β t A B V x ∂(P).measure G := by
  obtain ⟨L,hL⟩ := isCompact_univ.exists_bound_of_continuousOn hB.continuousOn
  have hi : Integrable ((bare ((upβ β) D.depth) : Config G n → ℝ) • A) (prior G n) :=
    ((bare_cont ((upβ β) D.depth)).smul hA).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have gi : GaugeInvariant ((bare ((upβ β) D.depth) : Config G n → ℝ) • A) :=
    fun k U=>congr_arg₂ (· * ·) (bare_gauge ..) (gA k U)
  have ia : Integrable (D.weighted (upβ β) A) (prior G f) := output_integrable h.2 _ hi
  have ga : GaugeInvariant (D.weighted (upβ β) A) := output_invariant h.2 _ hi gi
  change S.push (β 1) (fun U=>B U * D.weighted (upβ β) A U) V = _
  rw [T.pushing (S.isKernel h.1 (β 1)) _ V (fun k U=>congr_arg₂ (· * ·) (gB k U) (ga k U))
    (ia.bdd_mul hB.aestronglyMeasurable (Eventually.of_forall fun U=>hL U (Set.mem_univ _)))
    (fun k U=>S.covary h.1 k _ U V)]
  simp_rw [smul_eq_mul,observed_sum S T D h β A B hA gA V,integral_const_mul]
  rw [integral_finsetSum]
  · congr 1
    apply Finset.sum_congr rfl
    intro t _
    change S.Choices × D.Tags at t
    rw [divided S T D ((entry S T D h β t A B hA hB V).integrable ((P).measure G))]
    exact integral_congr_ae (Eventually.of_forall fun U=>(cell_integral S T D β t.1 t.2 A B V U).symm)
  intro t _
  exact outer S T D h β t.1 t.2 A B hA hB V

end YM.Integration.WilsonTwoAgePath
end
