import YM.WilsonMS.XSpace.FixedProfile
/-!
# Quantitative currency for normalization argument
Use a single filter: known populated (e.g. `Run.step`). Larger-order and
horizon compat are exact eventual equalities per fixed horizon. Exponents
may shrink.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.VisitH
open Function Set Filter MeasureTheory Real Finset Metric
open XSpace XSpace.Normalize XSpace.Expense XSpace.TestBudget XSpace.Cirrus Lattice Asymptotics
open scoped Topology BigOperators
local notation "𝕄" => XSpace.Mesh
variable {V X W I : Type} [NormedAddCommGroup X] [NormedAddCommGroup V]

def RateAt (a : ℝ) (p : 𝕄 → X) (x : X) :=
  (fun i => p i - x) =O[Front] FareP a

def Fast (p : 𝕄 → X) (x : X) :=
  ∃ a : ℝ, 0 < a ∧ RateAt a p x
variable {p p' : 𝕄 → X} {f : 𝕄 → V} {x y : X} {z : V} {R : ℝ}

lemma fare_limit (ht : 0 < R) : Tendsto (FareP R) Front (𝓝 0) :=
  Real.tendsto_exp_atBot.comp
    (show Tendsto (fun x : 𝕄 => -R * height x) Front atBot from
      (attained frontier).const_mul_atTop_of_neg (by linarith : -R < 0))

lemma fare_spacing (p : 𝕄) (a : ℝ) : FareP a p = p.spacing ^ a := by
  rw [small_p p]
  unfold FareP
  rw [← Real.exp_mul]
  congr 1
  ring

lemma FareO {a b : ℝ} (h : b ≤ a) : FareP a =O[Front] FareP b :=
  IsBigO.of_bound'
    ((fare_lower a b h).mono fun i hi => by
      simp only [norm_of_nonneg (exp_pos _).le]
      exact hi)

lemma Fast.limit (h : Fast p x) : Tendsto p Front (𝓝 x) := by
  obtain ⟨a, ha, hp⟩ := h
  have he := IsBigO.trans_tendsto hp (fare_limit ha)
  have hh : Tendsto (fun i => p i - x + x) Front (𝓝 (0 + x)) := he.add tendsto_const_nhds
  simpa using hh

lemma Fast.change (h : Fast p x) (hh : p =ᶠ[Front] p') : Fast p' x := by
  obtain ⟨a, ha, h⟩ := h
  exact ⟨a, ha, IsBigO.congr' h (hh.sub (EventuallyEq.refl _ _)) (EventuallyEq.refl _ _)⟩

lemma Fast.const (x : X) : Fast (fun _ => x) x :=
  ⟨1, zero_lt_one, IsBigO.of_bound 0 (Eventually.of_forall fun _ => by simp)⟩

lemma Fast.one (h : Rate Front id p (fun _ => x)) : Fast p x := by
  exact
    ⟨1, zero_lt_one,
      IsBigO.congr_right h fun i => by
        rw [fare_spacing, Real.rpow_one]
        rfl⟩

lemma Fast.fed {a : ℝ} {C : ℝ} (h : 0 < a) (hx : ∀ᶠ i in Front, ‖p i - x‖ ≤ C * FareP a i) :
    Fast p x := by
  refine ⟨_, h, IsBigO.of_bound C (hx.mono fun i hi => ?_)⟩
  rwa [Real.norm_of_nonneg (exp_pos _).le]

lemma lowerA {a' : ℝ} (h : RateAt a' p x) (ht : R ≤ a') : RateAt R p x :=
  IsBigO.trans h (FareO ht)

lemma Fast.prod_mk (h : Fast p x) (he : Fast f z) : Fast (fun i => (p i, f i)) (x, z) := by
  obtain ⟨a, ha, hp⟩ := h
  obtain ⟨b, hb, h⟩ := he
  exact
    ⟨min a b, lt_min ha hb,
      IsBigO.prod_left (lowerA hp (min_le_left a b)) (lowerA h (min_le_right a b))⟩

lemma Fast.add (h : Fast p x) (he : Fast p' y) : Fast (p + p') (x + y) := by
  obtain ⟨a, ha, hp⟩ := h
  obtain ⟨b, hb, h⟩ := he
  refine
    ⟨min a b, lt_min ha hb,
      IsBigO.congr_left (IsBigO.add (lowerA hp (min_le_left a b)) (lowerA h (min_le_right a b)))
        fun i => ?_⟩
  simp only [Pi.add_apply]
  abel

lemma Fast.neg (h : Fast p x) : Fast (-p) (-x) := by
  obtain ⟨a, ha, h⟩ := h
  exact
    ⟨a, ha,
      (IsBigO.neg_left h).congr_left fun i => by
        simp
        abel⟩

lemma Fast.sub (h : Fast p x) (he : Fast p' y) : Fast (p - p') (x - y) := by
  rw [sub_eq_add_neg, sub_eq_add_neg x]
  exact h.add he.neg

lemma Fast.p_sum (S : Finset I) {x : I → X} {f : I → 𝕄 → X} (h : ∀ i ∈ S, Fast (f i) (x i)) :
    Fast (fun p => ∑ i ∈ S, f i p) (∑ i ∈ S, x i) := by
  classical
    induction S using Finset.induction with
  | empty =>
    simp_rw [Finset.sum_empty]
    exact Fast.const _
  | insert i s hi ih =>
    simp_rw [Finset.sum_insert hi]
    exact (h i (by simp)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
section diff
variable [NormedSpace ℝ X] [NormedSpace ℝ V]

lemma Fast.mode (h : Fast p x) {f : X → V} (hv : DifferentiableAt ℝ f x) :
    Fast (fun i => f (p i)) (f x) := by
  obtain ⟨a, ha, hT⟩ := h
  have he := IsBigO.comp_tendsto hv.isBigO_sub (Fast.limit (p := p) (x := x) ⟨a, ha, hT⟩)
  exact ⟨a, ha, IsBigO.trans he hT⟩

lemma Fast.map (h : Fast p x) (L : X →L[ℝ] V) : Fast (fun i => L (p i)) (L x) :=
  h.mode L.differentiableAt

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
lemma Fast.sm (h : Fast p x) {f : 𝕄 → ℝ} {z : ℝ} (he : Fast f z) :
    Fast (fun i => f i • p i) (z • x) :=
  (he.prod_mk h).mode (differentiableAt_fst.smul differentiableAt_snd)
end diff

lemma Fast.mul {f g : 𝕄 → ℂ} {a b : ℂ} (h : Fast f a) (ht : Fast g b) :
    Fast (fun i => f i * g i) (a * b) :=
  (h.prod_mk ht).mode (f := fun (p : ℂ × ℂ) => p.1 * p.2)
    (differentiableAt_fst.mul differentiableAt_snd)

lemma Fast.p_prod (S : Finset I) {f : I → 𝕄 → ℂ} {x : I → ℂ} (h : ∀ i ∈ S, Fast (f i) (x i)) :
    Fast (fun p => ∏ i ∈ S, f i p) (∏ i ∈ S, x i) := by
  classical
    induction S using Finset.induction with
  | empty =>
    simp_rw [Finset.prod_empty]
    exact Fast.const _
  | insert i s hi ih =>
    simp_rw [Finset.prod_insert hi]
    exact (h i (by simp)).mul (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
section pi
variable [Fintype I] {E : I → Type} [∀ i, NormedAddCommGroup (E i)] {f : 𝕄 → ∀ i, E i} {g : ∀ i, E i}

lemma fast_pi (h : ∀ j, Fast (fun i => f i j) (g j)) : Fast f g := by
  have hs : ∀ s : Finset I, ∃ a : ℝ, 0 < a ∧ ∀ i ∈ s, RateAt a (fun p => f p i) (g i) := by
    classical
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | insert i s hi ih =>
      obtain ⟨c, hc, H⟩ := ih
      obtain ⟨d, hd, h⟩ := h i
      refine ⟨min c d, lt_min hc hd, ?_⟩
      intro j hj
      obtain rfl | hj := Finset.mem_insert.mp hj
      exact lowerA h (min_le_right ..)
      exact lowerA (H j hj) (min_le_left ..)
  obtain ⟨a, hA, h⟩ := hs Finset.univ
  exact ⟨a, hA, isBigO_pi.mpr fun i => h i (Finset.mem_univ _)⟩
end pi

section prime
variable {U J : Type} [Fintype U] [Fintype J]
local notation "Λ" => (U → ℂ)
local notation "Ζ" => (J → ℂ)

variable {K : 𝕄 → (U → ℂ) →ₗ[ℂ] (J → ℂ)} {M : (U → ℂ) →ₗ[ℂ] (J → ℂ)}

lemma Tendsto_matrix (h : ∀ (j : Λ), ∀ n : J, Fast (fun p => K p j n) (M j n)) :
    Tendsto (fun p => LinearMap.toContinuousLinearMap (K p)) Front
      (𝓝 (LinearMap.toContinuousLinearMap M)) := by
  classical
  let B := Pi.basisFun ℂ U
  let P (Q : Λ →ₗ[ℂ] Ζ) (i : U) : Ζ := Q (B i)
  let L (x : U → Ζ) : Λ →L[ℂ] Ζ := LinearMap.toContinuousLinearMap (B.constr ℂ x)
  have hp (q : Λ →ₗ[ℂ] Ζ) : L (P q) = LinearMap.toContinuousLinearMap q :=
    congr_arg (fun z : Λ →ₗ[ℂ] Ζ => LinearMap.toContinuousLinearMap z)
      (B.ext fun i => B.constr_basis ..)
  have he : Continuous L := by
    apply continuous_clm_apply.mpr
    intro v
    have he (p : U → Ζ) : L p v = ∑ i : U, B.repr v i • p i := by
      change B.constr ℂ p v = _
      exact B.constr_apply_fintype ..
    simp_rw [he]
    exact
      continuous_finsetSum _
        (fun i _ =>
          (continuous_const (y := B.repr v i)).smul (continuous_apply (A := fun _ : U => Ζ) i))
  simp_rw [← hp]
  exact
    he.continuousAt.tendsto.comp
      (show Tendsto (fun x => P (K x)) Front (𝓝 (P M)) from
        tendsto_pi_nhds.mpr fun i => (fast_pi (fun j => h (B i) j)).limit)

lemma decoderA (h : ∀ (j : Λ), ∀ n : J, Fast (fun p => K p j n) (M j n)) (hp : Injective M)
    (p : 𝕄 → Λ) (ht : ∀ i, Fast (fun v => K v (p v) i) 0) : Fast p 0 := by
  let A := M.leftInverse
  let L := LinearMap.toContinuousLinearMap A
  let D := fun i => LinearMap.toContinuousLinearMap (K i)
  have he : L.comp (LinearMap.toContinuousLinearMap M) = 1 :=
    ContinuousLinearMap.ext fun i =>
      LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr hp) i
  let H (i) := L.comp (D i)
  have hL : Tendsto H Front (𝓝 1) := by
    rw [← he]
    exact
      (show Continuous (fun v : Λ →L[ℂ] Ζ => L.comp v) from
            continuous_const.clm_comp continuous_id).continuousAt.tendsto.comp
        (Tendsto_matrix h)
  have hI : (1 : Λ →L[ℂ] Λ).IsInvertible := ⟨ContinuousLinearEquiv.refl .., rfl⟩
  have hq := hI.contDiffAt_map_inverse (n := 1)
  have hY : Expense.Cap Front (fun p => (H p).inverse) := by
    apply Expense.Cap.of_bounds (‖(1 : Λ →L[ℂ] Λ).inverse‖ + 1)
    filter_upwards [(hq.continuousAt.tendsto.comp hL).norm.eventually
        (ge_mem_nhds (lt_add_one (‖(1 : Λ →L[ℂ] Λ).inverse‖)))] with
      i hi
    exact hi
  have hu : Fast (fun i => H i (p i)) 0 := by
    have ho : Fast (fun i => D i (p i)) 0 := fast_pi (fun i => ht i)
    have he := ho.map (L.restrictScalars ℝ)
    rw [map_zero] at he
    exact he
  obtain ⟨c, hc, hT⟩ := hu
  obtain ⟨B, hB, hb⟩ := hY.bounds
  obtain ⟨E, hE, Hx⟩ := (show _ =O[Front] _ from hT).exists_pos
  refine Fast.fed (C := B * E) hc ?_
  filter_upwards [hL.eventually (Units.isOpen.mem_nhds (show IsUnit (1 : Λ →L[ℂ] Λ) from isUnit_one)),
    hb, Hx.bound] with i hi hm hx
  change IsUnit (H i) at hi
  have hV := ContinuousLinearMap.isUnit_iff_bijective.mp hi
  have ht : (H i).IsInvertible :=
    ⟨ContinuousLinearEquiv.ofBijective _ (LinearMap.ker_eq_bot.mpr hV.1)
        (LinearMap.range_eq_top.mpr hV.2),
      rfl⟩
  have hP : ‖H i (p i)‖ ≤ E * FareP c i := by
    simpa only [sub_zero, Real.norm_of_nonneg (exp_pos _).le] using hx
  rw [sub_zero]
  exact
    le_trans (le_of_eq (congr_arg norm (ht.inverse_apply_self ..).symm))
      (((ContinuousLinearMap.le_opNorm (H i).inverse (H i (p i))).trans
            (mul_le_mul hm hP (norm_nonneg _) hB.le)).trans_eq
        (by rw [mul_assoc]))
end prime
end YM.WilsonMS.VisitH
