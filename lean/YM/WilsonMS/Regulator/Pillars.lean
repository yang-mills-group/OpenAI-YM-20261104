import YM.WilsonMS.Regulator.HoldsMS
import YM.WilsonMS.ScalePath.Schedule
import YM.XSpace.Costs
/-!
# Actual geometry for the MS estimates -- samples filling the center box

Centers lie sufficiently far away even from the half-inversion fixed lattice pts. No
consistency claims involving ambiguous lifts on fundamental domain boundary
are necessary. Use all p large about the support. No change to sizes or
multiplicities. Goal for `Run.step` but useful with `Expense.Stretched`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.VisitH
open Function Set Filter MeasureTheory Real Finset
open MS MS.Latch MS.Latch.Job MS.Tone MS.Landau MS.Landau.Detect MS.Plane MS.Land
open MS.Theater MS.Tide MS.Dial MS.High MS.Rake MS.Orbit MS.Fleet MS.Vista MS.Vane
open MS.Local.Physical Lattice XSpace XSpace.Expense Schedule
open scoped Topology BigOperators ContDiff
variable {n : ℕ}
local notation "𝕄" => XSpace.Mesh

def height (p : 𝕄) :=
  -Real.log p.spacing

lemma small_p (p : 𝕄) : p.spacing = exp (-(height p)) := by rw [height, neg_neg, exp_log p.positive]

lemma reciprocal (p : 𝕄) : exp (height p) = p.spacing⁻¹ := by rw [height, exp_neg, exp_log p.positive]
variable {p : 𝕄} {z : Four ℝ}

abbrev tall (p : 𝕄) :=
  16 ≤ p.p.side.val

abbrev mid (p : 𝕄) (z : Four ℝ) :=
  roundP (height p) z

lemma height0 (hp : p.spacing ≤ 1) : 0 ≤ height p :=
  neg_nonneg.mpr (Real.log_nonpos p.positive.le hp)
variable {I : Type} {l : Filter I} {u : I → 𝕄}

lemma attained (p : Stretched l u) : Tendsto (fun i => height (u i)) l atTop := by
  apply
    tendsto_neg_atBot_atTop.comp
      (Real.tendsto_log_nhdsGT_zero.comp
        (tendsto_nhdsWithin_iff.mpr ⟨p.endpt, Eventually.of_forall fun i => (u i).positive⟩))

lemma toll (h : Stretched l u) : ∀ᶠ i in l, tall (u i) := by
  filter_upwards [h.horizon.eventually (eventually_ge_atTop 16)] with i hi
  exact_mod_cast (show (16 : ℝ) ≤ (u i).p.side.val from hi)

lemma superb (h : Stretched l u) : Super l (fun i => Schedule.half (u i).p) (fun i => height (u i)) := by
  intro r
  obtain ⟨k, hk⟩ := exists_nat_gt r
  filter_upwards [h.smaller, (h.pay k).eventually_ge_atTop 1] with i hi hp
  unfold tickA dimT
  dsimp only
  rw [Schedule.twice, ← Real.exp_le_exp, exp_log (by exact_mod_cast (u i).p.side.pos)]
  apply
    le_trans
      (show exp (r * height (u i)) ≤ exp (k * height (u i)) from
        exp_monotone (mul_le_mul_of_nonneg_right hk.le (height0 hi)))
  have hv := (u i).positive
  rw [Real.exp_nat_mul, reciprocal, inv_pow]
  exact
    (inv_le_iff_one_le_mul₀ (pow_pos hv k)).mpr
      (by
        rw [mul_comm]
        exact hp)

lemma pay_mid (hp : tall p) (hz : z ∈ p.Box) (i : Axis) :
    let v := mid p z i;
    (p.p.side.val : ℤ) ≤ 16 * v ∧ 4 * v ≤ p.p.side.val := by
  intro v
  let x := p.spacing
  have hx : x > 0 := p.positive
  let B : ℝ := p.p.side.val
  have hB : 16 ≤ B := by
    unfold B
    exact_mod_cast hp
  have hk : x * B / 8 ≤ z i ∧ z i ≤ x * B / 4 := ⟨hz.1 i, hz.2 i⟩
  have he : exp (height p) * z i = z i / x := by rw [reciprocal, div_eq_mul_inv, mul_comm]
  have hh : v = ⌊z i / x⌋ := congr_arg Int.floor he
  have hg : B / 8 ≤ z i / x ∧ z i / x ≤ B / 4 :=
    ⟨(le_div_iff₀ hx).mpr (by linarith [hk.1]), (div_le_iff₀ hx).mpr (by linarith [hk.2])⟩
  have H := Int.floor_le (z i / x)
  have hT := Int.lt_floor_add_one (z i / x)
  rw [← hh] at H hT
  have hh := (show B ≤ 16 * (v : ℝ) ∧ 4 * (v : ℝ) ≤ B from (by constructor <;> linarith [hg.1, hg.2]))
  unfold B at hh
  exact_mod_cast hh

lemma mid_here (hp : tall p) (hz : z ∈ p.Box) (hN : Side) (h : p.p.side = hN) :
    Lattice.lift (wrap hN (mid p z)) = mid p z := by
  apply lift_eq_iff.mpr
  refine ⟨rfl, fun i => ?_⟩
  obtain ⟨hv, hT⟩ := pay_mid hp hz i
  have he := p.p.side.pos
  rw [← h]
  omega

lemma mid_mine (hp : tall p) (hz : z ∈ p.Box) (L : Side) (h : p.p.side = periodN L) (k : Half) :
    mine (periodN L) (wrap (periodN L) (mid p z) - thin L k) := by
  have ht := p.p.side.pos
  let n := periodN L
  let x := wrap n (mid p z)
  let w := thin L k
  have hm : ∀ i, Lattice.lift x i = mid p z i := congr_fun (mid_here hp hz n h)
  have hv : n.val ≤ 16 * pdist x := by
    obtain hh := component_le x 0
    rw [hm] at hh
    obtain ⟨hZ, hT⟩ := pay_mid hp hz 0
    rw [show n.val = p.p.side.val from congr_arg (·.val) h.symm]
    omega
  by_cases he : k = 0
  · unfold mine
    rw [he, map_zero, sub_zero]
    exact hv
  have hq : pdist w = L.val := by
    unfold w
    rw [show pdist _ = L.val * pdist k from caress .., bornlf k he, mul_one]
  have hH : pdist x ≤ n.val / 4 := by
    apply Finset.sup_le
    intro i _
    rw [hm]
    obtain ⟨hZ, hT⟩ := pay_mid hp hz i
    rw [show n.val = p.p.side.val from congr_arg (·.val) h.symm]
    omega
  have ht : pdist w ≤ pdist (x - w) + pdist x := by
    nth_rw 1 [show w = x + -(x - w) by abel]
    exact (pdist_triangle ..).trans_eq (by rw [pdist_neg, Nat.add_comm])
  change n.val ≤ 16 * pdist (x - w)
  have hQ : n.val = 2 * L.val := cap_val L
  omega

variable (K : Set (Points n))

structure Study where
  mesh : 𝕄
  forever : tall mesh
  small : mesh.spacing ≤ 1
  pos : Fin n → Cover
  center : Four ℝ
  wind : center ∈ mesh.Box
  bright : mesh.rel pos center ∈ K

private def GeoH (μ : ℝ) : Geo (Study K) :=
  { θ := fun i => height i.mesh
    η := fun i => μ - height i.mesh
    room i := height0 i.small }

def trial (μ : ℝ) : Trial (Study K) (Fin n)
    where
  profile := GeoH K μ
  side i := Schedule.half i.mesh.p
  head i := mid i.mesh i.center
  off w i := i.pos w - mid i.mesh i.center

def actual (p : Points n) (w : Fin n) :=
  Theater.out (p w)

lemma actC (i : Fin n) : Continuous (fun p : Points n => actual p i) :=
  (PiLp.continuous_ofLp 2 _).comp (show Continuous (fun p : Points n => p i) from (by fun_prop))
local notation "ζ" => lifted

lemma act_test (μ : ℝ) (i : Study K) (w : Fin n) :
    testP (trial K μ) i w =
      actual (i.mesh.rel i.pos i.center) w +
        (i.center - i.mesh.spacing • Tone.embed (mid i.mesh i.center)) := by
  let M := mid i.mesh i.center
  change
    exp (-height i.mesh) • Tone.embed (i.pos w - M) =
      i.mesh.spacing • Tone.embed (i.pos w) - i.center + _
  rw [show Tone.embed (i.pos w - M) = Tone.embed (i.pos w) - Tone.embed M from
      funext fun i => Int.cast_sub ..,
    smul_sub, ← small_p]
  unfold M
  abel

lemma upright (μ : ℝ) (i : Study K) : dimT (trial K μ).side i = i.mesh.p.side :=
  twice _

lemma group_visit {K : Set (Points n)} (h : IsCompact K) (hp : K ⊆ conf n) (μ : ℝ) {v : I → Points n}
    (hv : ∀ i, v i ∈ K) : Rake.Mesh (frameF I μ) (fun w i => actual (v i) w) := by
  intro a b H
  cases isEmpty_or_nonempty I with
  | inl he =>
    exact ⟨⟨1, zero_lt_one, fun i => isEmptyElim i⟩, ⟨1, zero_lt_one, fun i => isEmptyElim i⟩⟩
  | inr ht =>
    obtain ⟨i⟩ := ht
    let f (p : Points n) := ‖actual p a - actual p b‖
    have he : Continuous f := ((actC a).sub (actC b)).norm
    have hk : K.Nonempty := ⟨_, hv i⟩
    obtain ⟨x, hx, hQ⟩ := h.exists_isMinOn hk he.continuousOn
    obtain ⟨y, hy, hY⟩ := h.exists_isMaxOn hk he.continuousOn
    have hM (p : Points n) (hi : p ∈ K) : 0 < f p :=
      norm_pos_iff.mpr
        (sub_ne_zero.mpr (Theater.out.injective.ne ((show Injective p.ofLp from hp hi).ne H)))
    refine ⟨⟨f y, hM y hy, fun j => ?_⟩, ⟨f x, hM x hx, fun j => ?_⟩⟩ <;>
      simp only [Geo.roots, Pi.sub_apply, Pi.zero_apply, exp_zero, mul_one]
    · exact hY (hv j)
    exact hQ (hv j)

lemma growing (h : IsCompact K) (hp : K ⊆ conf n) (μ : ℝ) {l : Filter (Study K)}
    (ht : Stretched l Study.mesh) : Dial.Uses (trial K μ) l μ := by
  refine
    ⟨fun w => ?_, ?k, fun _ => rfl, attained ht, superb ht, fun i k =>
      mid_mine i.forever i.wind _ (Schedule.twice _).symm k,
      centered_size _ _ fun i => (mid_here i.forever i.wind _ (Schedule.twice _).symm).symm⟩
  case k =>
    let V := trial K μ
    apply unpose (v := μ) V.off
    intro i j hij
    let F (i : Study K) := i.mesh.rel i.pos i.center
    obtain ⟨⟨C, hC, Q⟩, ⟨D, hD, T⟩⟩ :=
      group_visit h hp μ (fun i : Study K => show F i ∈ K from i.bright) i j hij
    have hx (x : Study K) : (testP V x) i - (testP V x) j = actual (F x) i - actual (F x) j := by
      rw [show V = _ from rfl, act_test, act_test, add_sub_add_right_eq_sub]
    refine ⟨⟨C, hC, fun x => ?_⟩, ⟨D, hD, fun x => ?_⟩⟩
    · change ‖testP _ x i - testP _ x j‖ ≤ _
      rw [hx]
      exact Q x
    change _ ≤ ‖testP _ x i - testP _ x j‖
    rw [hx]
    exact T x
  obtain ⟨C, hC⟩ := (h.image (actC w |>.norm)).bddAbove
  refine ⟨max C 0 + 1, by linarith [le_max_right C 0], fun i => ?_⟩
  let A := trial K μ
  let z := exp (height i.mesh)
  let β := Tone.embed (A.off w i)
  let f := i.mesh.rel i.pos i.center
  have he : ‖testP A i w‖ ≤ max C 0 + 1 := by
    rw [show A = _ from rfl, act_test]
    apply (norm_add_le ..).trans
    refine
      add_le_add (le_trans (hC (mem_image_of_mem _ i.bright)) (le_max_left ..)) (le_trans ?_ i.small)
    rw [norm_sub_rev, small_p i.mesh]
    exact roundP_test ..
  apply
    (le_trans (le_of_eq (b := z * ‖testP A i w‖) ?_))
      ((mul_le_mul_of_nonneg_left he (exp_pos _).le).trans_eq (mul_comm ..))
  change ‖β‖ = exp _ * ‖exp _ • β‖
  rw [norm_smul_of_nonneg (exp_pos _).le, ← mul_assoc]
  unfold A trial GeoH
  dsimp only
  rw [exp_neg, mul_inv_cancel₀ (exp_pos _).ne', one_mul]
end YM.WilsonMS.VisitH
