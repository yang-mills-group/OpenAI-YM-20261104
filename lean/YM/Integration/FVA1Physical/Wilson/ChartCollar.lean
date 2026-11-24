import YM.Integration.FVA1Physical.Wilson.CopiedGeometry
import YM.MSbar.Cottage.Posture

/-! Uniform exponential-chart and motion estimates for a copied forest. The
number of moving Wilson coordinates depends only on the rooted support. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter MeasureTheory Set Finset Lattice RG YM.Wilson Tree Precision Exterior RGComparison.Core16
open FVA2.CityHistory PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested
open MSbar MSbar.Lis MSbar.Whisk MSbar.Rolling MSbar.Midpoint MSbar.Wave MSbar.Bakery Comparison.RG02 Push Push.Uniform
open MSbar.Heath MSbar.Heath.Cottage MSbar.Bulk SectorNext.Vacuum Metric
open scoped Classical Topology Matrix.Norms.Frobenius
variable {G : Gauge} {f c : Side}

lemma chord_to_regular {J : Voice G} (cle : Clear G J) {v g w : ℝ} (hg : 0 < g) (hw : 0 ≤ w)
    (near : v ≤ J.δ) (chart : J.C*v<(LocalH.geom_patch G).choose) (size : J.C*v ≤ g*w)
    (U : Config G f) (small : ∀ e,G.chord (U e) ≤ v) : U∈regularInputs g w := by
  have C₀ := zero_le_one.trans cle.cost
  have decoded (e : Edge (Site f)) := cle.near (U e) ((small e).trans near)
  have normed (e : Edge (Site f)) : ‖J.decode (U e)‖ ≤ J.C*v :=
    (decoded e).2.2.trans (mul_le_mul_of_nonneg_left (small e) C₀)
  have inside (e : Edge (Site f)) : J.decode (U e)∈ball 0 (LocalH.geom_patch G).choose :=
    mem_ball_zero_iff.mpr ((normed e).trans_lt chart)
  have entered (e : Edge (Site f)) : U e∈exponentialPatch G := ⟨_,inside e,(decoded e).2.1⟩
  have decodedLog (e : Edge (Site f)) : logWithin G (U e)=J.decode (U e) := by
    rw [logWithin,Set.piecewise_eq_of_mem _ _ _ (entered e)]
    exact ((congrArg (LocalH.snap G) (decoded e).2.1).symm).trans
      (((LocalH.geom_patch G).choose_spec.2 _ le_rfl).2.2.1 (inside e))
  refine ⟨Set.mem_univ_pi.mpr entered,(pi_norm_le_iff_of_nonneg hw).mpr ?_⟩
  intro i
  change |g⁻¹ * (logWithin G (U (rope i))) i.2| ≤ w
  rw [decodedLog,abs_mul,abs_of_nonneg (inv_nonneg.mpr hg.le)]
  apply (mul_le_mul_of_nonneg_left ((PiLp.norm_apply_le (J.decode (U (rope i))) i.2).trans
    ((normed _).trans size)) (inv_nonneg.mpr hg.le)).trans_eq
  exact inv_mul_cancel_left₀ hg.ne' w

/-- The maximum scalar sum changed by a supported forest motion. Its coefficient
contains no torus cardinality. -/
def motionCost (G : Gauge) {f : Side} (X : Support f) (w : ℝ) : ℝ :=
  ((X.card * 81 * Fintype.card Axis * Fintype.card G.ColorIndex : ℕ):ℝ)*(2*w)

lemma spine_coordinates {X : Support f} {U V : Config G f} (moved : Spine X U V)
    (g w : ℝ) (hu : ‖chartLog g U‖ ≤ w) (hv : ‖chartLog g V‖ ≤ w) :
    (∑ i, |(chartLog g U-chartLog g V) i|) ≤ motionCost G X w := by
  let E := (halo 1 X).product (Finset.univ : Finset Axis)
  let T := E.product (Finset.univ : Finset G.ColorIndex)
  let I := T.image (fun v=> primary v.1 v.2)
  have outside (i : Primary f G) (hi : i∉I) : (chartLog g U-chartLog g V) i=0 := by
    let e := rope i
    have far : e.1∉halo 1 X := by
      intro h
      exact hi (Finset.mem_image.mpr ⟨(e,i.2), Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨h,mem_univ _⟩,mem_univ _⟩,curr i⟩)
    have left : e.1∉X := fun h=> far (halo_subset _ _ h)
    have right : e.1+step e.2∉X := fun h=> far (halo_spec.mpr ⟨_,h,
      (separation_comm _ _).le.trans (Work.E01.sep_step_le ..)⟩)
    let J : Support f := {e.1,e.1+step e.2}
    have dis : Disjoint J X := by
      rw [Finset.disjoint_left]
      intro a h z; rcases Finset.mem_insert.mp h with he|he
      · exact left (he ▸ z)
      exact right (Finset.mem_singleton.mp he ▸ z)
    have eq : U e=V e := moved J dis e (by simp [J]) (by simp [J])
    change g⁻¹*(logWithin G (U e)) i.2-g⁻¹*(logWithin G (V e)) i.2=0
    rw [eq,sub_self]
  have count : I.card ≤ X.card*81*Fintype.card Axis*Fintype.card G.ColorIndex := by
    apply (Finset.card_image_le).trans
    change (((halo 1 X) ×ˢ (univ : Finset Axis)) ×ˢ (univ : Finset G.ColorIndex)).card ≤ _
    rw [Finset.card_product,Finset.card_product,card_univ,card_univ]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Corona.halo_size X 1))
  have hw := (norm_nonneg _).trans hu
  calc
    (∑ i, |(chartLog g U-chartLog g V) i|) = ∑ i∈I, |(chartLog g U-chartLog g V) i| := by
      symm; exact Finset.sum_subset (Finset.subset_univ _) fun i _ hi=> by rw [outside i hi,abs_zero]
    _ ≤ ∑ _∈I, 2*w := Finset.sum_le_sum fun i _ =>
      (norm_sub_le (chartLog g U i) (chartLog g V i)).trans
        ((add_le_add ((norm_le_pi_norm ..).trans hu) ((norm_le_pi_norm ..).trans hv)).trans_eq (two_mul w).symm)
    _ ≤ motionCost G X w := by
      rw [Finset.sum_const,nsmul_eq_mul,motionCost]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast count) (mul_nonneg zero_le_two hw)

variable {S : StepData c f} {R : Rep G f} {F : Forest S.ratio} {X Y : Support f} {J : Voice G} {P : Palisade}
variable {x : Positions (Primary c G)} {μ : Positions (Key F G)} {a b v K : ℝ} {M d : ℕ}
local notation "W" => (represent (tint G (Exterior.Body 1 c) x))
/-- The chord bound on the *actual chamber copy*, including its fixed coarse replica. -/
lemma posture_chord (cle : Clear G J) (post : Posture P J F a b v K M d X Y x μ R.p)
    {U : Config G f} (inside : U∈hotel F X Y J W μ a b) (e : Edge (Site f)) :
    G.chord (chambers F Y J W μ U e) ≤ J.C*(shade G*K)+v/4 := by
  let z := rented F Y J W μ U
  have hk : ‖z‖ ≤ K := (Posture.pose cle post inside).1
  have hK : 0 ≤ K := (norm_nonneg _).trans hk
  have base : G.chord (Precision.replica S.ratio W e) ≤ v/4 := by
    unfold Precision.replica; split
    · rw [G.chord_one]; exact div_nonneg post.lights.le (by norm_num)
    exact post.folds _ (Set.mem_univ _)
  have hC := zero_le_one.trans cle.cost
  unfold chambers lifting
  by_cases he : e∈F.trunks
  · rw [show ∀ Z:F.Slice G,F.drape Z e=1 from fun Z=> F.on_tree Z ⟨e,he⟩,G.chord_one]
    exact add_nonneg (mul_nonneg hC (mul_nonneg (shade_pos G).le hK)) (div_nonneg post.lights.le (by norm_num))
  let u : F.Free := ⟨e,he⟩
  rw [show ∀ Z:F.Slice G,F.drape Z e=Z u from fun Z=> F.off_tree Z u]
  let y := tint G _ z u
  change G.chord (G.lieExp y * _) ≤ _
  have hy : ‖y‖ ≤ shade G*K := (norm_le_pi_norm (tint G _ z) u).trans
    ((tint_le z).trans (mul_le_mul_of_nonneg_left hk (shade_pos G).le))
  exact (G.chord_triangle ..).trans (add_le_add (((cle.small y (hy.trans post.smoke)).2).trans
    (mul_le_mul_of_nonneg_left hy hC)) base)

end YM.Integration.FVA1Physical.Wilson
