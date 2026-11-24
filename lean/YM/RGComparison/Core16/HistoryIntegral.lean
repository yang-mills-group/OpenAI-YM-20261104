import YM.RGComparison.Core16.Descent
import YM.Push.BETA_TRANSPORT.Noise

/-!
# The full history, including common tag measure, in tree slices

Unfold a finite history back to the unmasked Wilson input, performing all intermediate gauge
eliminations. *Every* coefficient and the vacuum use the same integral. This exact-identity
aspect of RG03 is for evaluated densities in the finite history, complementary to adjustments of
their `Lawful` representations (not supplied by equality of denotations). In particular, no
disconnected product manipulation at intermediate scales. Real-valued here; combine real &
imaginary parts later to use full complex marks.
-/
set_option autoImplicit false
noncomputable section

namespace YM.RGComparison.Core16.Descent
open Lattice RG Tree Wilson
open YM.Push.BetaTransport
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators
open MeasureTheory Filter
variable {G : Gauge} {n c f : Side}

abbrev Fields (G : Gauge) (d : Descent n c) := d.Links → G.El

/-- `top` of a path. Retain *one* x across the integrand. -/
def fine : {c : Side} → (d : Descent n c) → Config G c → Fields G d → Config G n
  | _, .nil, V, _ => V
  | _, .push _ T d, _, x => d.fine (T.drape (x ∘ Sum.inl)) (x ∘ Sum.inr)

/-- The likelihoods in the actual branches, including unused tags. -/
def probability : {c : Side} → (d : Descent n c) → d.Tags → Fields G d → ℝ
  | _, .nil, _, _ => 1
  | _, .push S T d, t, x => S.likelihood (T.drape (x ∘ Sum.inl)) t.1 *
      d.probability t.2 (x ∘ Sum.inr)

/-- `account 1` will be the unscaled energy for Taylor and Gaussian calculations. -/
def account : {c : Side} → (d : Descent n c) → (ℕ → ℝ) → d.Tags →
    Config G c → Fields G d → ℝ
  | _, .nil, β, _, V, _ => β 0 * energy V
  | _, .push S T d, β, t, V, x => β 1 * tagEnergy S t.1 (T.drape (x ∘ Sum.inl)) V +
      d.account (upβ β) t.2 (T.drape (x ∘ Sum.inl)) (x ∘ Sum.inr)

/-- Product of the actual noise normalizations. -/
def scalar (G : Gauge) : {c : Side} → (d : Descent n c) → (ℕ → ℝ) → ℝ
  | _, .nil, _ => 1
  | _, .push S _ d, β => Next.Fluctuations.Sector.prefactor S G (β 1) * scalar G d (upβ β)

variable (d : Descent n c)

def integrand (β : ℕ → ℝ) (t : d.Tags) (g : Config G n → ℝ) (V : Config G c)
    (x : Fields G d) := d.probability t x * Real.exp (-d.account β t V x) * g (d.fine V x)

/-- Product of actual probability Haar on the path links. -/
def measure (G : Gauge) (d : Descent n c) := Measure.pi fun _ : d.Links => G.probHaar
instance : IsProbabilityMeasure (d.measure G) := by unfold measure; infer_instance

lemma fine_continuous : Continuous fun z : Config G c × Fields G d => d.fine z.1 z.2 := by
  induction d with
  | nil => exact continuous_fst
  | @push m i S T d ih =>
    have hs : Continuous fun x : Fields G (push S T d) => T.drape (x ∘ Sum.inl) :=
      T.continuous_drape.comp (continuous_pi fun j => continuous_apply _)
    exact ih.comp ((hs.comp (continuous_snd (X := Config G m))).prodMk
      ((continuous_pi (fun i : d.Links => continuous_apply (A := fun _ : (push S T d).Links => G.El) (Sum.inr i))).comp continuous_snd))

variable {d} (h : d.OK G)

lemma probability_nonneg (d : Descent n c) (t : d.Tags) (x : Fields G d) : 0 ≤ d.probability t x := by
  induction d with
  | nil => exact zero_le_one
  | push S T d ih => exact mul_nonneg (S.likelihood_pos ..) (ih ..)

include h in
lemma prob_measurable (t : d.Tags) : Measurable (d.probability (G := G) t) := by
  induction d with
  | nil => exact measurable_const
  | @push m i S T d ih =>
    have hc : Measurable fun x : Fields G (push S T d) => T.drape (x ∘ Sum.inl) :=
      T.continuous_drape.measurable.comp (measurable_pi_lambda _ fun _ => measurable_pi_apply _)
    have he : Measurable fun x : Fields G (push S T d) => fun i : d.Links => x (Sum.inr i) :=
      measurable_pi_lambda _ fun _ => measurable_pi_apply _
    exact ((S.likelihood_meas h.1 t.1).comp hc).mul ((ih h.2 t.2).comp he)

include h in
lemma total_probability (x : Fields G d) : ∑ t, d.probability t x = 1 := by
  induction d with
  | nil =>
    -- t : Unit
    change ∑ _t : Unit, (1:ℝ) = _
    simp
  | @push m i S T d ih =>
    change ∑ t : S.Choices × d.Tags, S.likelihood _ t.1 * d.probability t.2 (x ∘ Sum.inr) = _
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, ih h.2, mul_one]
    exact S.chosen h.1 _

include h in
lemma prob_envelope (t : d.Tags) : Envelope (d.probability (G := G) t) := by
  refine ⟨prob_measurable h t, 1, fun x => ?_⟩
  rw [Real.norm_of_nonneg (probability_nonneg d ..), ← total_probability h x]
  exact Finset.single_le_sum (fun i _ => probability_nonneg d i x) (Finset.mem_univ _)

/-- Single tagged energy is bounded and measurable off the Taylor patch too. -/
lemma tagEnergy_envelope {S : StepData c f} (h : S.patch.Branches S.kernel G) (t : S.Choices) :
    Envelope (fun p : Config G f × Config G c => tagEnergy S t p.1 p.2) := by
  refine ⟨tagEnergy_meas S h t, noiseCap S, fun p => ?_⟩
  unfold tagEnergy
  rw [Real.norm_of_nonneg ((energy_estimate S _).nonneg _)]
  exact (energy_estimate S _).bound _

private lemma pullback {α α' X : Type*} [MeasurableSpace α] [MeasurableSpace α'] [MeasurableSpace X] [Norm X]
    {f : α → X} {g : α' → α} (h : Envelope f) (hg : Measurable g) : Envelope (f ∘ g) :=
  ⟨h.meas.comp hg, h.cost.choose, fun i => h.cost.choose_spec (g i)⟩

private lemma from_compact {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
    [BorelSpace X] {f : X → ℝ} (h : Continuous f) : Envelope f :=
  ⟨h.measurable, let H := isCompact_univ.exists_bound_of_continuousOn h.continuousOn;
    ⟨H.choose, fun x => H.choose_spec x (Set.mem_univ _)⟩⟩

include h in
lemma account_envelope (β : ℕ → ℝ) (t : d.Tags) :
    Envelope fun z : Config G c × Fields G d => d.account β t z.1 z.2 := by
  induction d generalizing β with
  | nil => exact pullback (g := Prod.fst) (f := fun x => β 0 * energy x) (from_compact (energy_cont.const_mul (β 0))) measurable_fst
  | @push m i S T d ih =>
    have hm : Measurable fun x : Fields G (push S T d) => T.drape (x ∘ Sum.inl) :=
      T.continuous_drape.measurable.comp (measurable_pi_lambda _ fun _ => measurable_pi_apply _)
    have hv : Measurable fun x : Fields G (push S T d) => fun i : d.Links => x (Sum.inr i) :=
      measurable_pi_lambda _ fun _ => measurable_pi_apply _
    exact Envelope.add ((Envelope.const (β 1)).mul
        (pullback (g := fun z : Config G m × Fields G (push S T d) => (T.drape (z.2 ∘ Sum.inl), z.1))
          (tagEnergy_envelope h.1 t.1) ((hm.comp measurable_snd).prodMk measurable_fst)))
      (pullback (g := fun z : Config G m × Fields G (push S T d) => (T.drape (z.2 ∘ Sum.inl), fun i : d.Links => z.2 (Sum.inr i)))
        (ih h.2 (upβ β) t.2) ((hm.comp measurable_snd).prodMk (hv.comp measurable_snd)))

include h in
lemma path_envelope (β : ℕ → ℝ) (t : d.Tags) (g : Config G n → ℝ) (hg : Continuous g) :
    Envelope fun z : Config G c × Fields G d => d.integrand β t g z.1 z.2 :=
  ((pullback (prob_envelope h t) measurable_snd).mul (account_envelope h β t).neg.exp).mul
    (pullback (from_compact hg) (fine_continuous d).measurable)

include h in
lemma path_integrable (β : ℕ → ℝ) (t : d.Tags) (g : Config G n → ℝ) (hg : Continuous g) (V) :
    Integrable (d.integrand β t g V) (d.measure G) :=
  (pullback (path_envelope h β t g hg) (measurable_const.prodMk measurable_id)).integrable _

lemma scalar_pos (G : Gauge) (d : Descent n c) (β : ℕ → ℝ) : 0 < d.scalar G β := by
  induction d generalizing β with
  | nil => exact one_pos
  | push S T d ih => exact mul_pos (pow_pos (inv_pos.mpr (S.penaltyZ_pos ..)) _) (ih _)

section main
variable {S : StepData c f} {T : Forest S.ratio} {D : Descent n f}

private lemma kernel (β : ℝ) (U : Config G f) (V : Config G c) :
    S.density β U V = Next.Fluctuations.Sector.prefactor S G β *
      ∑ t, S.likelihood U t * Real.exp (-(β * tagEnergy S t U V)) := by
  unfold StepData.density
  simp_rw [noise_factor]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  unfold tagEnergy YM.Push.BetaTransport.Gibbs.factor
  rw [neg_mul,mul_left_comm]

private lemma append_integral
    {g : Fields G (push S T D) → ℝ} (hg : Integrable g ((push S T D).measure G)) :
    ∫ z, g z ∂((push S T D).measure G) =
      ∫ a, ∫ x, g (Sum.elim a x) ∂D.measure G ∂T.order G := by
  let e := MeasurableEquiv.sumPiEquivProdPi (fun (_ : T.Free ⊕ D.Links) => G.El)
  have he : MeasurePreserving e.symm ((T.order G).prod (D.measure G)) ((push S T D).measure G) :=
    measurePreserving_sumPiEquivProdPi_symm (fun _ => G.probHaar)
  have hx := he.integral_comp' g
  refine hx.symm.trans ?_
  exact integral_prod _ ((he.integrable_comp_emb e.symm.measurableEmbedding).mpr hg)

private lemma weighted_gauge {u : Config G n → ℝ} (β : ℝ) (h : GaugeInvariant u) :
    GaugeInvariant ((bare β : Config G n → ℝ) • u) := by
  intro t U
  exact congr_arg₂ (· * ·) (bare_gauge ..) (h t U)

private lemma integ_split (β : ℕ → ℝ) (a : S.Choices) (b : D.Tags) (g : Config G n → ℝ)
    (V : Config G c) (U : T.Slice G) (x : Fields G D) :
    (push S T D).integrand β (a,b) g V (Sum.elim U x) =
      (S.likelihood (T.drape U) a * Real.exp (-(β 1 * tagEnergy S a (T.drape U) V))) *
        D.integrand (upβ β) b g (T.drape U) x := by
  unfold integrand
  rw [account, probability, fine]
  dsimp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, Prod.fst, Prod.snd]
  rw [neg_add, Real.exp_add]
  ring

include h in
/-- Make the common input/output explicit, retaining every normalizer, on the SAME step sequence as
in `vacuum_eq` and the mark and denominator identities (specialize `β` to `line`). Integrable
fixed torus calculation. All kernel tags and one branch choice array for all sources. Often apply
to real/imag parts of products on `C`.
-/
theorem path_formula (β : ℕ → ℝ) {g : Config G n → ℝ} (hg : Continuous g) (hi : GaugeInvariant g)
    (V : Config G c) : d.weighted β g V = d.scalar G β *
      ∑ t, ∫ x, d.integrand β t g V x ∂d.measure G := by
  induction d generalizing β with
  | nil =>
    let U := (nil : Descent n n)
    have hx (x : Fields G U) : U.integrand β () g V x = bare (β 0) V * g V := by
      unfold U
      simp only [integrand, probability, account, fine, bare, neg_mul, one_mul]
    change (nil : Descent n n).weighted β g V = 1 * ∑ t : Unit,
      ∫ x, (nil : Descent n n).integrand β t g V x ∂U.measure G
    change (nil : Descent n n).weighted β g V = 1 * ∑ t : Unit, ∫ x, U.integrand β t g V x ∂U.measure G
    rw [one_mul, Fintype.sum_unique]
    simp_rw [show (default : Unit)=() from rfl, hx]
    rw [weighted, output_nil]
    rw [integral_const,probReal_univ,one_smul]; rfl
  | @push m i S T d ih =>
    let x := upβ β
    let Z := T.order G
    let Φ (U : T.Slice G) (t : S.Choices) := S.likelihood (T.drape U) t *
      Real.exp (-(β 1 * tagEnergy S t (T.drape U) V))
    let W := d.measure G
    let f (U : T.Slice G) (s : d.Tags) := ∫ w, d.integrand x s g (T.drape U) w ∂W
    have he (t : S.Choices) (s : d.Tags) : Envelope fun z : T.Slice G × Fields G d =>
        (push S T d).integrand β (t,s) g V (Sum.elim z.1 z.2) := by
      have hm : Measurable fun z : T.Slice G × Fields G d => (Sum.elim z.1 z.2 : T.Free ⊕ d.Links → G.El) := by
        refine measurable_pi_lambda _ ?_
        intro j
        cases j
        · exact (measurable_pi_apply _).comp measurable_fst
        · exact (measurable_pi_apply _).comp measurable_snd
      have hk : Measurable fun z : T.Slice G × Fields G d => (V, (Sum.elim z.1 z.2 : Fields G (push S T d))) := measurable_const.prodMk hm
      have hi := pullback (path_envelope h β (t,s) g hg) hk
      exact hi
    have hd (t : S.Choices) (s : d.Tags) (U : T.Slice G) :
        (∫ w, (push S T d).integrand β (t,s) g V (Sum.elim U w) ∂W) = Φ U t * f U s := by
      simp_rw [integ_split, integral_const_mul]; rfl
    have hs (t : S.Choices) (s : d.Tags) : Integrable (fun U => Φ U t * f U s) Z := by
      simp_rw [← hd]
      exact ((he t s).integrable (Z.prod W)).integral_prod_left
    have hy (q : Config G i) : S.density (β 1) q V * d.weighted x g q =
      (push S T d).scalar G β * ∑ t : (push S T d).Tags,
        S.likelihood q t.1 * Real.exp (-(β 1 * tagEnergy S t.1 q V)) *
          (∫ w, d.integrand x t.2 g q w ∂W) := by
      rw [kernel, ih h.2 x q]
      change (_ * _) * (d.scalar G x * _) = _ * ∑ t : S.Choices × d.Tags,
        S.likelihood q t.1 * Real.exp (-(β 1 * tagEnergy S t.1 q V)) * ∫ w, d.integrand x t.2 g q w ∂W
      conv_rhs => rhs; rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]
      unfold W x; rw [scalar]; ring
    change S.push (β 1) (d.weighted x g) V = _
    have HH := h.1
    rw [T.pushing (S.isKernel HH (β 1)) (d.weighted x g) V
      (output_invariant h.2 _ (((bare_cont _).smul hg).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)) (weighted_gauge _ hi))
      (output_integrable h.2 _ (((bare_cont _).smul hg).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))) (fun k U => S.covary HH k _ U V)]
    simp_rw [smul_eq_mul, hy, integral_const_mul]
    rw [integral_finsetSum]
    · congr 1
      apply Finset.sum_congr rfl
      intro t _
      change S.Choices × d.Tags at t
      rw [append_integral (path_integrable h β t g hg V)]
      exact integral_congr_ae (Filter.Eventually.of_forall fun U => (hd t.1 t.2 U).symm)
    intro t _
    exact hs t.1 t.2
end main
end YM.RGComparison.Core16.Descent
