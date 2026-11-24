import YM.WiderProfiles.Geometry
import YM.FVA2.O.Enh.Venue
/-! # Two-zone layouts satisfy §F polynomial geometry -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.WiderProfiles
open Function Filter Set Metric Real
open MS MS.Theater
open XSpace XSpace.Cirrus Arrival.Schedule
open O.Enh
open O.Score (squeeze)
open scoped Topology BigOperators Classical

variable {n m : ℕ}
variable {K : Set (Points n)} {S : Set (Points m)}

private lemma low_fin {I : Type*} [Finite I] {f : I → ℝ} (h : ∀ i, 0 < f i) :
    ∃ c : ℝ, 0 < c ∧ ∀ i, c ≤ f i := by
  let A := Set.Ioi (0:ℝ)
  have : Nonempty (↥A) := ⟨⟨1,(show (0:ℝ) < 1 from zero_lt_one)⟩⟩
  obtain ⟨p, hp⟩ := Finite.exists_ge (fun i : I => (⟨f i, h i⟩ : ↥A))
  exact ⟨p.val,p.property, hp⟩

lemma compact_extent (hK : IsCompact K) :
    ∃ A : ℝ, 0 < A ∧ ∀ x ∈ K, ∀ w, ‖plot x w‖ ≤ A := by
  choose f _ hf using Legs K hK
  obtain ⟨A,hA⟩ := Finite.exists_le f
  exact ⟨max A 1, lt_max_of_lt_right zero_lt_one, fun x hx w =>
    (hf w x hx).trans ((hA w).trans (le_max_left ..))⟩

lemma compact_separation (hK : IsCompact K) (h : K ⊆ conf n) :
    ∃ b : ℝ, 0 < b ∧ ∀ x ∈ K, ∀ w z, w ≠ z → b ≤ ‖plot x w-plot x z‖ := by
  let I := {i : Fin n × Fin n // i.1 ≠ i.2}
  choose f hf hw using fun i : I => storyH hK h i.val.1 i.val.2 i.property
  obtain ⟨b,hb,hB⟩ := low_fin hf
  exact ⟨b,hb,fun x hx w z he => (hB ⟨(w,z),he⟩).trans (hw ⟨(w,z),he⟩ x hx)⟩

lemma compact_outside (hS : IsCompact S) (h : S ⊆ Outside m) :
    ∃ b : ℝ, 0 < b ∧ ∀ y ∈ S, ∀ w, b ≤ ‖plot y w‖ := by
  choose f hf hp using storyY hS h
  obtain ⟨b,hb,hB⟩ := low_fin hf
  exact ⟨b,hb,fun y hy w => (hB w).trans (hp w y hy)⟩

/-- `T = exp t`, layouts exactly as in F.O (no displacing one end of a test).
Enough for ANY fixed power a. No lattice hypothesis on the positions except that we
ask the comparison on actual Sized samples realizing these layouts (as at the
recrop step). Large `T` threshold here is independent of mesh and x,y. -/
lemma forest_admits (hK : IsCompact K) (hx : K ⊆ conf n) (hS : IsCompact S)
    (hy : S ⊆ Outside m) (d : ℝ) (_hd : 0 < d) :
    ∃ c D : ℝ, 0 < c ∧ 1 ≤ D ∧ ∀ᶠ r : ℝ in atTop, ∀ t ≥ r, ∀ (a : ℕ),
    ∀ x ∈ K, ∀ y ∈ S, ∀ s : Sample (n+m), Sized s →
    exp t ≤ d*(1+theta s.F)^a → familiar s=forest x (squeeze (-t) y) → Admits a c D s := by
  obtain ⟨A,hA,hAX⟩ := compact_extent hK
  obtain ⟨B,hB,hBY⟩ := compact_extent hS
  obtain ⟨p,hp,hpX⟩ := compact_separation hK hx
  obtain ⟨q,hq,hqY⟩ := compact_separation hS (fun y hy' => room (hy hy'))
  obtain ⟨b,hb,hbY⟩ := compact_outside hS hy
  have h' := (Real.tendsto_exp_atTop.atTop_mul_const hb).eventually (eventually_ge_atTop (A+p))
  let c := min p q; let D := max (max A (d*B)) 1
  refine ⟨c, D, lt_min hp hq, le_max_right .., ?_⟩
  filter_upwards [h', eventually_ge_atTop (0:ℝ)] with r hr hr0 t ht a x hX y hY s hs hT he
  let F := forest x (squeeze (-t) y)
  have hR : 1 ≤ exp t := Real.one_le_exp (hr0.trans ht)
  have hw : 1 ≤ (1+theta s.F)^a := one_le_pow₀ (le_add_of_nonneg_right (le_max_right ..))
  have hL (w : Fin n) : plot (familiar s) (Fin.castAdd m w) = plot x w := by
    rw [he]; simp only [plot, forest_left]
  have hQ (w : Fin m) : plot (familiar s) (Fin.natAdd n w) = exp t • plot y w := by
    rw [he]; simp only [plot, forest_right, norm_g]
  have cross (w : Fin m) (z : Fin n) :
      p ≤ ‖exp t • plot y w - plot x z‖ := by
    apply le_trans _ (norm_sub_norm_le ..); rw [norm_smul_of_nonneg (exp_pos _).le]
    have ha : A + p ≤ exp t * ‖plot y w‖ := le_trans (show A+p ≤ exp r * b from hr)
      (mul_le_mul (exp_monotone ht) (hbY _ hY w) hb.le (exp_pos _).le)
    linarith [hAX _ hX z]
  refine ⟨hs,?_,?_⟩
  · intro w; induction w using Fin.addCases with
    | left w => rw [hL]
                exact (hAX _ hX w).trans ((le_mul_of_one_le_right hA.le hw).trans
                  (mul_le_mul_of_nonneg_right ((le_max_left ..).trans (le_max_left ..))
                    (zero_le_one.trans hw)))
    | right w =>
      rw [hQ,norm_smul_of_nonneg (exp_pos _).le]; calc
        _ ≤ d*(1+theta s.F)^a*B := mul_le_mul hT (hBY y hY w) (norm_nonneg _)
          ((exp_pos _).le.trans hT)
        _ = d*B*(1+theta s.F)^a := by ring
        _ ≤ D*(1+theta s.F)^a := mul_le_mul_of_nonneg_right
          ((le_max_right ..).trans (le_max_left ..)) (zero_le_one.trans hw)
  intro w z; induction w using Fin.addCases with
  | left w =>
    induction z using Fin.addCases with
    | left z =>
      intro h; rw [hL,hL]; exact (min_le_left ..).trans
        (hpX x hX w z (fun he => h (congr_arg _ he)))
    | right z => intro _; rw [hL,hQ,norm_sub_rev]; exact (min_le_left ..).trans (cross z w)
  | right w =>
    induction z using Fin.addCases with
    | left z => intro _; rw [hL,hQ]; exact (min_le_left ..).trans (cross w z)
    | right z =>
      intro h; rw [hQ,hQ, ← smul_sub, norm_smul_of_nonneg (exp_pos _).le]
      exact (min_le_right ..).trans ((hqY y hY w z (fun he => h (congr_arg _ he))).trans
        (le_mul_of_one_le_left (norm_nonneg _) hR))
end YM.FVA2.WiderProfiles
