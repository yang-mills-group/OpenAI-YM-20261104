import YM.Integration.WilsonCapturedPrimaryWardHome
import YM.Integration.WilsonCapturedPrimaryWardTiling

/-! One fine Wilson chessboard inside the original fixed filing tiling for every
occupied subset of each member of the submitted compact test. -/
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWardNest
open Function Set Filter Finset MeasureTheory Lattice Wilson RG Labels Source Push
open Extraction Extra.Histories PhysicalNext.Repeat.Legato
open RG12 RG17 Climb Trace.Pilot MergeProof Next.Extract PhysicalNext.Repeat Legato Bandage
open MergeProof.Ribbons MergeProof.Ribbons.ManyCopies Cells
open XSpace XSpace.Rose Push.GridApprox OPE OPE.Orbits
open WilsonCapturedPrimaryPhysicalArray
open private supported from YM.Integration.WilsonCapturedPrimaryPhysicalArray
open scoped Topology BigOperators Classical
variable {G : Gauge} (R : Run G) {n : ℕ}
local notation "CF" => R.family
local notation "B" j:max => ( (CF).path.levels.budget j).B

/-- The intermediate date is the elected separation stop. Both fine dates are
fixed at each physical radius before the UV and volume regulators. -/
theorem original (simple : G.Simple) (slow : WilsonWindowReportingPace.Slow R.kit)
    (v J : ℕ) (wide : 4 < v) (φ : Test n) :
    ∀ᶠ r : ℝ in 𝓝[>]0, let j := WilsonMeasuredWindow.stop  (CF).path.levels simple v r
    ∃ early : J ≤ j, ∀ᶠ k : ℕ in atTop, ∃ fine : j ≤ k,
    ∀ N p (live : k ≤ N) (z : Fin n → Site ( (CF).side N p)),
      WilsonCenteredCompactBooking.mass R φ r (N,p) z ≠ 0 →
      ∀ (axis : Option (Fin n)) (s : Finset (Fin n))
        (Y : s → Config G ( (CF).side N p) → ℂ) (fee : s → ℝ),
        (∀ i, BlockCost (Q:= (CF).S) (Y i) k ( (CF).beta N p) (fee i)) →
        (center  (CF).S p (early.trans (fine.trans live)) 0).rootTest ( (CF).beta N p)
          (Contacts.Nested.clusterAt (fun i : s => registered z axis i) Y) ≤ ∏ i, fee i := by
  have go := WilsonMeasuredWindow.stop_tendsto  (CF).path.levels simple v (by omega)
  have grow := (Multi.Wage.ranges simple  (CF).path.levels).comp go
  have shrinks :=  (CF).S.shrinks.comp go
  have hJ :=  (CF).S.a_pos J
  filter_upwards [go.eventually_ge_atTop J, grow.eventually_ge_atTop 2,
    shrinks.eventually (gt_mem_nhds (half_pos hJ)),
    WilsonCapturedPrimaryPhysicalChamber.original R J φ,
    WilsonCapturedPrimarySeparatedStop.translated R simple slow v wide φ] with r early radius narrow chamber apart
  let j := WilsonMeasuredWindow.stop  (CF).path.levels simple v r
  change  (CF).S.a j <  (CF).S.a J / 2 at narrow
  change 2 ≤ B j at radius
  dsimp only
  refine ⟨early,?_⟩
  let count : ℝ := Fintype.card (Signed × Fin n)
  have pay :=  (CF).S.shrinks.eventually (gt_mem_nhds (show 0 <  (CF).S.a j / (10*(1+count)) by
    exact div_pos ( (CF).S.a_pos j) (mul_pos (by norm_num) (add_pos_of_pos_of_nonneg one_pos (Nat.cast_nonneg _)))))
  filter_upwards [eventually_ge_atTop j,eventually_ge_atTop (WilsonCapturedPrimarySupportedHalo.date R r),pay] with k fine date loan
  refine ⟨fine,?_⟩
  intro N p live z charged axis s Y fee paid
  let run := fine.trans live
  let q :=  (CF).S.toDepth run p
  let o (i:s) := registered z axis (i : Fin n)
  have inside i := chamber N p (date.trans live) z charged axis i
  have shell (i i':s) : ‖ (CF).S.place (o i)‖+‖ (CF).S.place (o i')‖+ (CF).S.a j <  (CF).S.a J := by
    dsimp [o]
    linarith only [inside i, inside i', narrow, hJ]
  obtain ⟨x,hx,places⟩ := supported R φ r z charged
  have pos (i : Fin n) : wrap ( (CF).side N p) (address ( (CF).S.a N) (r • x) i) = z i := congrFun places i
  have room (i i' : s) (ne : i ≠ i') : 2* (CF).S.a j < ‖ (CF).S.place (o i - o i')‖ := by
    have lower := apart N p run x hx (axis.elim 0 z) i i' (fun h=>ne (Subtype.ext h))
    rw [pos i,pos i'] at lower
    change (B j)^2 < separation (q.parent (o i)) (q.parent (o i')) at lower
    have four : 4 ≤ separation (q.parent (o i)) (q.parent (o i')) := by nlinarith only [radius,lower]
    have compare := Corona.foreshorten q (o i) (o i')
    have many := Nat.mul_le_mul_left q.count.val four
    have dpos : 0 < q.count.val := q.count.property
    have dist : 2*q.count.val < separation (o i) (o i') := by
      have step : 2*q.count.val+q.count.val < q.count.val*4 := by omega
      exact Nat.lt_of_add_lt_add_right (step.trans_le (many.trans compare))
    have hs :  (CF).S.a N*(q.count.val:ℝ)= (CF).S.a j :=  (CF).S.embeds_scale q
    have cost := mul_lt_mul_of_pos_left (show (2:ℝ)*(q.count.val:ℝ) < separation (o i) (o i') by exact_mod_cast dist) ( (CF).S.a_pos N)
    have spatial := (normC  (CF) N p (o i - o i')).1
    simp only [separation,sub_zero] at spatial
    change  (CF).S.a N*(separation (o i) (o i') : ℝ) ≤ _ at spatial
    nlinarith only [hs,cost,spatial]
  have many : Fintype.card (Signed × s) ≤ Fintype.card (Signed × Fin n) :=
    Fintype.card_le_of_injective (fun t : Signed × s => (t.1,(t.2 : Fin n)))
      (fun _ _ h=>Prod.ext (congrArg (fun v : Signed × Fin n => v.1) h) (Subtype.ext (congrArg (fun v : Signed × Fin n => v.2) h)))
  have eff : (Fintype.card (Signed × s):ℝ)*10* (CF).S.a k <  (CF).S.a j := by
    have c0 : 0 ≤ count := Nat.cast_nonneg _
    have posd : 0 < 10*(1+count) := mul_pos (by norm_num) (add_pos_of_pos_of_nonneg one_pos c0)
    change  (CF).S.a k <  (CF).S.a j/(10*(1+count)) at loan
    have maxc : (Fintype.card (Signed × s):ℝ) ≤ count := by dsimp [count]; exact_mod_cast many
    have bounded := mul_le_mul_of_nonneg_right maxc ( (CF).S.a_pos k).le
    nlinarith only [bounded, (lt_div_iff₀ posd).mp loan,  (CF).S.a_pos k]
  obtain ⟨hx,ht,hf⟩ := Contacts.Nested.cast_cutoff (C:=R.family) early fine live shell room eff
  exact Contacts.Nested.coarser_product early fine live R.makes o Y fee hx ht hf paid

end YM.Integration.WilsonCapturedPrimaryWardNest
