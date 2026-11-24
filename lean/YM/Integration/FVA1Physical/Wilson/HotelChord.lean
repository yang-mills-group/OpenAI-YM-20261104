import YM.Integration.FVA1Physical.Wilson.ChartCollar
import YM.MSbar.Lease.Ticket

/-! The radius of the physical chart copies measured from their actual coarse
field and localization centre. This bound exploits the native hotel width. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter MeasureTheory Set Finset Lattice RG YM.Wilson Tree Precision Exterior RGComparison.Core16
open FVA2.CityHistory PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested
open MSbar MSbar.Lis MSbar.Whisk MSbar.Rolling MSbar.Midpoint MSbar.Wave MSbar.Bakery Comparison.RG02 Push Push.Uniform
open MSbar.Heath MSbar.Heath.Cottage MSbar.Bulk SectorNext.Vacuum Metric
open scoped Classical Topology Matrix.Norms.Frobenius
variable {G : Gauge} {f c : Side} {S : StepData c f} {R : Rep G f} {F : Forest S.ratio}
variable {X Y : Support f} {J : Voice G} {P : Palisade}
variable {x : Positions (Primary c G)} {μ : Positions (Key F G)} {a b v K : ℝ} {M d : ℕ}
local notation "W" => (represent (tint G (Exterior.Body 1 c) x))

/-- Uniform linkwise radius from the coordinates actually measured in the cell.
Both near and remote chart copies have this bound. -/
lemma hotel_chord (cle : Clear G J) (post : Posture P J F a b v K M d X Y x μ R.p)
    {U : Config G f} (inside : U∈hotel F X Y J W μ a b) (e : Edge (Site f)) :
    G.chord (chambers F Y J W μ U e) ≤ J.C*shade G*(‖μ‖+b+‖x‖) := by
  let z := rented F Y J W μ U
  have near : ‖z-μ‖ ≤ b := leanOn F X Y J W μ cle post.extendsX inside post.goes post.height
  have distance : ‖z‖ ≤ ‖μ‖+b := by
    calc ‖z‖ = ‖z-μ+μ‖ := (congrArg norm (sub_add_cancel ..)).symm
         _ ≤ ‖z-μ‖+‖μ‖ := norm_add_le .. 
         _ ≤ ‖μ‖+b := by linarith only [near]
  have hC := zero_le_one.trans cle.cost
  have sh := (shade_pos G).le
  have hx : shade G*‖x‖ ≤ J.r := (mul_le_mul_of_nonneg_left post.awake sh).trans post.smoke
  have coarse (q : Edge (Site c)) : G.chord (W q) ≤ J.C*(shade G*‖x‖) := by
    let t := tint G _ x (q.1,Exterior.coord q.2)
    have ht : ‖t‖ ≤ shade G*‖x‖ := (norm_le_pi_norm (tint G (Exterior.Body 1 c) x) (q.1,Exterior.coord q.2)).trans (tint_le x)
    change G.chord (G.lieExp t * 1) ≤ _
    rw [mul_one]
    exact ((cle.small _ (ht.trans hx)).2).trans (mul_le_mul_of_nonneg_left ht hC)
  have base : G.chord (Precision.replica S.ratio W e) ≤ J.C*(shade G*‖x‖) := by
    unfold Precision.replica; split
    · rw [G.chord_one]; exact mul_nonneg hC (mul_nonneg sh (norm_nonneg _))
    exact coarse _
  unfold chambers lifting
  by_cases he : e∈F.trunks
  · rw [show ∀ Z:F.Slice G,F.drape Z e=1 from fun Z=>F.on_tree Z ⟨e,he⟩,G.chord_one]
    exact mul_nonneg (mul_nonneg hC sh) (add_nonneg (add_nonneg (norm_nonneg _) post.height) (norm_nonneg _))
  let u : F.Free := ⟨e,he⟩
  rw [show ∀ Z:F.Slice G,F.drape Z e=Z u from fun Z=>F.off_tree Z u]
  let y := tint G _ z u
  change G.chord (G.lieExp y*_) ≤ _
  have hz : ‖y‖ ≤ shade G*‖z‖ := (norm_le_pi_norm (tint G _ z) u).trans (tint_le z)
  have fine := (cle.small _ (hz.trans ((mul_le_mul_of_nonneg_left (Posture.pose cle post inside).1 sh).trans post.smoke))).2
  have both := (G.chord_triangle ..).trans (add_le_add (fine.trans (mul_le_mul_of_nonneg_left
    (hz.trans (mul_le_mul_of_nonneg_left distance sh)) hC)) base)
  exact both.trans_eq (by ring)

end YM.Integration.FVA1Physical.Wilson
