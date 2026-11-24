import YM.WilsonMS.Top.Lagrangian

/-!
# The half restriction of the top exponent (positions)

Formula using **based** gauge first. The factor of 1/2 affects the measure
term as well (pay the Haar series only *once* at a link orbit).
-/

set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Quo
open Function Filter Set Finset Matrix Complex Lattice XSpace
open MS MS.Orbit MS.Bare MS.Koszul MS.Cylinder MS.Cylinder.Taylor MS.Native Root Position Darboux
open MS.Orbit.Cog MS.Swirl
open scoped Topology ContDiff Matrix.Norms.Frobenius

section
variable {P : Period} (T : P.Tree) (G : Gauge)
local notation "Nm'" => LinksI G P
local notation "Qm'" => GhostI T G
local notation "n" => P.side
local notation "J'" => liftJ P G
local notation "M'" => Root.Mode T G
local notation "U'" => SiteField G P.side
local notation "T₀" => MS.Native.Chart.City G P.Sites
local notation "T₁" => LogSpace G P
local notation "A0" => Native.glow G (Site P.side)
local notation "R0" => coordinates T G

def expander (P : Period) (G : Gauge) : LogSpace G P →L[ℝ] Native.Chart.City G P.Sites :=
  LinearMap.toContinuousLinearMap (Root.liftedA P G)

abbrev RealEntries {X Y : Type} (A : Matrix X Y ℂ) : Prop :=
  ∀ i j, ↑((A i j).re) = A i j

lemma real_lift : RealEntries (liftJ P G) := by
  intro i j
  rcases covered G i with ⟨k, rfl⟩ | ⟨k, rfl⟩
  rw [jV]
  split <;> simp
  rw [jW, jV]
  split <;> simp

lemma real_based : RealEntries (liftN T G) := fun _ _ => rfl

lemma real_average : RealEntries (averageM T G) := by
  intro i j
  rcases i with ⟨c, i⟩
  rw [averageM, Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, arithmeticMean]
  unfold liftN scaleZ
  rw [← Complex.ofReal_sum, ← Complex.ofReal_mul, ← Complex.ofReal_sub, ofReal_re]

lemma real_location {S : Matrix (GaugeField G P.side) (GhostI T G) ℂ} (h : RealEntries S) :
    RealEntries (location T G S) := by
  intro i j
  obtain ⟨i, rfl⟩ := (eIso G P.side).surjective i
  change (↑((location T G S (includeF G n i) j).re) : ℂ) = location T G S (includeF G P.side i) j
  rw [locationF]
  rcases i with (i | i) | (i | i) <;> rcases j with (j | j) | (j | j) <;>
    first
    | exact real_lift _ _ _
    | exact h _ _
    | exact Complex.ofReal_zero.trans rfl

lemma restrict_germ {S : Matrix (GaugeField G P.side) (GhostI T G) ℂ} (hs : RealEntries S)
    (f : T₀ → ℝ) (hf : germ f) :
    specialize (location T G S) (ink (A0).e0 f) = ink (R0).e0 (f ∘ expander P G) := by
  let C := location T G S
  let R := coordinates T G
  let U := glow G (Site P.side)
  let Y := expander P G
  rw [ink_ctrl_one _ _ hf,
    show specialize (location T G S) (ink U.e0 f) = _ from
      specialize_shade C (region.symm (ink U.e0 f))]
  let W : Matrix M' (FixedMode G P.side) ℝ := Cᵀ.map Complex.re
  have hv : Cᵀ = W.map Complex.ofReal :=
    funext fun i =>
      funext fun j => by
        rw [show (W.map Complex.ofReal) i j = _ from (rfl : (W.map Complex.ofReal) i j = _)]
        exact (real_location T G hs _ _).symm
  rw [hv]
  symm
  refine scale_pos U.e0 _ (fun i j => W i j) (fun i => ?_) hf
  rw [← Equiv.sum_comp (eIso G P.side)]
  change Y (R.e0 i) = ∑ j : LetterFull G n, (C (includeF G n j) i).re • U.e0 (includeF G n j)
  unfold C
  simp_rw [locationF]
  rcases i with (i | i) | (i | i) <;>
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type (α₁ := SiteField G n)]
  all_goals simp only [legs, zero_re, zero_smul, Finset.sum_const_zero, zero_add, add_zero]
  · exact links_basis _ _
  · simp_rw [show R.e0 (_) = (0 : T₁) from (rfl : R.e0 (Sum.inl (Sum.inr i)) = 0), map_zero,
      show ∀ j : GaugeField G P.side, U.e0 (includeF G n (Sum.inl (Sum.inr j))) = 0 from fun j => rfl,
      smul_zero, Finset.sum_const_zero]
  · simp_rw [show R.e0 (_) = (0 : T₁) from (rfl : R.e0 (Sum.inr (Sum.inl i)) = 0), map_zero,
      show ∀ j : SiteField G P.side, U.e0 (includeF G n (Sum.inr (Sum.inl j))) = 0 from fun j => rfl,
      smul_zero, Finset.sum_const_zero]
  exact map_zero Y

lemma link_exp (A : T₁) :
    (Native.Chart.rent (Native.Chart.drive P.side) ∘ expander P G) A = (2 : ℝ) * energyE P G A := by
  rw [cover_exp]
  change Native.Chart.rent _ (liftedA P G _) = _
  ring

lemma restrict_action {S : Matrix (GaugeField G P.side) (GhostI T G) ℂ} (h : RealEntries S) :
    ((2 : ℂ)⁻¹) •
        specialize (location T G S) (ink (A0).e0 (Native.Chart.rent (Native.Chart.drive P.side))) =
      ink (R0).e0 (energyE P G) := by
  rw [restrict_germ _ _ h _ (Native.Chart.rent_s _),
    show Native.Chart.rent (Native.Chart.drive n) ∘ expander P G = (2 : ℝ) • energyE P G from
      funext fun A => link_exp G _,
    ink_smul _ (energy_germ P G), Complex.ofReal_ofNat, inv_smul_smul₀ (by norm_num : (2 : ℂ) ≠ 0)]

private lemma both_sides {X : Type} [AddCommMonoid X] (f : P.Bonds → X) :
    ∑ i : P.Bonds, f i = (∑ i : P.Link, f i.val) + ∑ i : P.Link, f (P.reflect i.val) := by
  classical
  rw [← Fintype.sum_subtype_add_sum_subtype P.Chosen]
  congr 1
  let V : { e : P.Bonds // ¬P.Chosen e } ≃ P.Link :=
    { toFun x := ⟨P.reflect x.val, (P.choice_reflect _).2 x.property⟩,
      invFun x := ⟨P.reflect x.val, by simp [x.property]⟩,
      left_inv i := Subtype.ext (P.reflect_invol _), right_inv i := Subtype.ext (P.reflect_invol _) }
  rw [← Equiv.sum_comp V (fun i => f (P.reflect i.val))]
  simp_rw [show ∀ i, P.reflect (V i).val = i.val from fun i => P.reflect_invol i.val]

lemma halfHaar {S : Matrix (GaugeField G P.side) (GhostI T G) ℂ} (h : RealEntries S) :
    ((2 : ℂ)⁻¹) • specialize (location T G S) (ink (A0).e0 Native.Chart.totalH) = Root.haarLog T G := by
  have hf : Native.Chart.totalH ∘ expander P G =ᶠ[𝓝 0] (2 : ℝ) • Root.orbitLog G := by
    filter_upwards [eventually_all.mpr
        (fun i : P.Link =>
          (continuous_apply (A := fun _ : P.Link => G.Color) i |>.tendsto (0 : T₁)).eventually
            Maurer.opposite)] with
      x hx
    change ∑ i : Edge (Site P.side), Maurer.lac _ = 2 * ∑ i : P.Link, Maurer.lac _
    rw [both_sides]
    simp_rw [show ∀ i : P.Link, expander P G x i.val = x i from fun _ => P.extend_at _ _,
      show ∀ i : P.Link, expander P G x (P.reflect i.val) = -(x i) from fun i =>
        (P.extend_reflect x i.val).trans (by rw [P.extend_at]),
      hx]
    ring
  rw [restrict_germ _ _ h _ Native.Chart.nice_totalH, inkit _ hf, ink_smul _ (orbit_germ G),
    Complex.ofReal_ofNat, inv_smul_smul₀ (by norm_num : (2 : ℂ) ≠ 0)]
  rfl

lemma discardReads (f : LogSpace G P → ℝ) (h : germ f) :
    specialize (discard T G) (ink (R0).e0 f) = ink (R0).e0 f := by
  let Q := specialize (discard T G)
  have hh (j i : M') (hz : j ≠ i) : discard T G j i = 0 := by
    rcases i with (i | i) | (i | i) <;> rcases j with (j | j) | (j | j) <;>
      first
      | rfl
      | (simpa [Matrix.one_apply, discard, legs] using hz)
  classical
  ext l
  induction l generalizing f with
  | nil => rfl
  | cons i l ih =>
    rw [D_eval i (specialize _ _), specialize_deriv, sum_eq_single_of_mem i (mem_univ _)]
    swap
    · intro j _ hj
      rw [hh j i hj, zero_smul]
    rw [Pi.smul_apply, inktip, ih _ (germ_layer h _)]
    rcases i with (i | i) | (i | i)
    all_goals
      first
      | ( simp only [discard, legs, Matrix.one_apply_eq, one_smul]
          rfl)
      | skip
    rw [show discard T G _ _ = 0 from rfl, zero_smul]
    exact (congr_fun (ink_off (R0).e0 (i := b i) rfl f) l).symm
end
end YM.WilsonMS.Quo
