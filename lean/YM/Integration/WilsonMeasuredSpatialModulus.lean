import YM.FullVolume.Literal
import YM.FullVolume.Connect
import YM.Extraction.Held
import YM.Extra.WEAK_SCALING_ACTLAW.Comparisons

/-! Original finite Wilson equicontinuity on compact subsets of the full
separated configuration space, for all periods and all fine placements. -/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredSpatialModulus
open Function Filter Set Metric MeasureTheory Lattice Wilson RG Source Extraction Extraction.Gaps
open FullVolume PhysicalNext.Repeat.Legato
open scoped Classical BigOperators Topology ContDiff
variable {G : Gauge} (R : Run G) (hG : G.Simple) {n : ℕ}

include hG in
theorem purchased (f : Extraction.Order) (v : Fin n → R.family.book.Token)
    (K : Set (Points n)) (hk : IsCompact K) (sep : K ⊆ conf n) :
    ∃ a B : ℝ, 0<a ∧ 0≤B ∧ ∀ᶠ i : ℕ×ℕ in f.fuse,
      ∀ x y : Positions n, tag (R.family.S.a i.1) x ∈ K →
        dist (tag (R.family.S.a i.1) y) (tag (R.family.S.a i.1) x) ≤ a →
        dist (lifted R.family i.1 i.2 v y) (lifted R.family i.1 i.2 v x) ≤
          B*dist (tag (R.family.S.a i.1) y) (tag (R.family.S.a i.1) x) := by
  let C := R.family
  obtain ⟨a,ha,hA⟩ := hk.exists_cthickening_subset_open (conf_open n) sep
  let V := cthickening a K
  have hV : IsCompact V := hk.cthickening
  obtain ⟨r,hr,outer⟩ := someGrows C.S hV hA
  choose M hM cost using fun j : MotionIndex n =>
    (FullVolume.genuine R hG).bounds n v [j] r hr
  let B : ℝ := ∑ j,M j
  have pos : 0≤B := Finset.sum_nonneg fun j _ => hM j
  have le (j : MotionIndex n) : M j ≤ B :=
    Finset.single_le_sum (fun j _ => hM j) (Finset.mem_univ j)
  refine ⟨a,B*Fintype.card (MotionIndex n),ha,mul_nonneg pos (Nat.cast_nonneg _),?_⟩
  filter_upwards [(Extra.WeakScaling.cofin_snd f).eventually outer,
    (Extra.WeakScaling.cofin_fst f).eventually (eventually_all.mpr cost)] with i P N x y hx hy
  refine stroll (C.S.a_pos _) (lifted C i.1 i.2 v) x y a B pos hy ?_
  intro u j hu
  have inside : tag (C.S.a i.1) u ∈ V := mem_cthickening_of_dist_le _ _ _ K hx hu
  have gap : spaceout C r i (wrap _ ∘ u) :=
    fun b c neq => gridSeparation C.S _ rfl (P _ inside) _ _ neq.symm
  have charge := (N j i.2 u gap).trans (le j)
  rw [dist_eq_norm,unique_units _ (C.S.a_pos _) j u,norm_smul,Real.norm_of_nonneg (C.S.a_pos _).le]
  exact mul_le_mul_of_nonneg_left charge (C.S.a_pos _).le

end YM.Integration.WilsonMeasuredSpatialModulus

