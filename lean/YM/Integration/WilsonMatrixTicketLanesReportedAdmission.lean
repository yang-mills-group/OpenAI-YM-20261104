import YM.Integration.WilsonMatrixTicketLanesReportedMaster
import YM.Integration.WilsonReportingMeasuredAdmission

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesReportedAdmission
open Function Filter Set Metric Real OPE Labels RG12 RG17 Extraction Spec Wilson Table
open RGComparison.Core16.Astage Next.Rank.Price PhysicalNext.Repeat.Legato SharpGram.Lenses
open WilsonMatrixTicketLanesReportedMaster Pier.Lair OPE.Orbits
open Climb Ward Next.UVStress PhysMS Trace.Pilot SharpGram
open scoped Topology BigOperators Classical
variable {G : Gauge} (R : Run G) {f : Extraction.Order} {S : Table R.family.book}
  (F : Spec.Final R.family f S) (L : RG17.Layout F)

def frameCost (d : ℕ) : ℝ :=
  ∑ j : (R.family.labels.level d).Index, (2:ℝ) ^ ((R.family.labels.level d).grades j).2

theorem scale (d : ℕ) (t : ℝ) (positive : 0 ≤ t) (bound : t ≤ 2) (x : R.family.label d) :
    ‖(R.family.labels.level d).scaled t x‖ ≤ frameCost R d * RG12.mass R.family d x := by
  have cost : 0 ≤ frameCost R d := Finset.sum_nonneg fun _ _ => pow_nonneg zero_le_two _
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg cost (RG12.mass_nonneg ..))).2
  intro j
  rw [Labels.Frame.scaled_apply,norm_mul,Complex.norm_real,Real.norm_of_nonneg (pow_nonneg positive _)]
  have row : (2:ℝ)^((R.family.labels.level d).grades j).2 ≤ frameCost R d :=
    Finset.single_le_sum (fun (k : (R.family.labels.level d).Index) _ =>
      pow_nonneg (zero_le_two : (0:ℝ) ≤ 2) ((R.family.labels.level d).grades k).2) (Finset.mem_univ j)
  exact mul_le_mul ((pow_le_pow_left₀ positive bound _).trans row)
    ((norm_le_pi_norm x j).trans (RG12.norm_le_mass R.family d x)) (norm_nonneg _) cost

/-- The true deposited cutoff field has an exact quota at every subsequent mesh and period. -/
theorem quota (d : ℕ) (r : ℝ) (w : R.family.label d) (hm : R.family.ref d ≤ L.level r)
    (N p : ℕ) (hN : L.level r ≤ N) :
    Next.UVStress.quota R.family d (L.level r) N p (RG17.atRef L d r (N,p) w) =
      R.family.S.a (L.level r)^d * RG12.mass R.family d (L.shift d r w) := by
  unfold RG17.atRef
  rw [SharpGram.quota_smul,RG12.quota_atK R.family F.room.cutoff d _ (N,p) hm hN,
    Complex.norm_real,Real.norm_of_nonneg (pow_nonneg (R.family.S.a_pos _).le d)]
  · exact R.makes
  · exact hm
  · exact hN

variable (J : ℝ → PhysMS.tower S) (lead : PhysMS.Leading F J)
  {K : (Bel R.family.book).Hierarchy}
  (aligned : ∀ d : ℕ, ∀ᶠ r in trail, AlignO F.sector F.room.kernel.spin K d (J r d))
  {u : Filter (ℕ×ℕ)} (B : Mantle F u) (E : Services R.family f S)
  (pegs : Pegs B L) (near : ∀ᶠ r in trail, R.family.S.a (L.level r) ≤ r ∧
    r ≤ R.family.S.a (L.level r) * R.family.path.levels.clock.hatBeta (L.level r)^2)
local notation "β" => R.family.path.levels.clock.hatBeta
include lead aligned E pegs near in
/-- The original measured Maxwell fields have uniformly paid raw inputs on the same
ultrafilter. The free field can be chosen after the reporting distance. -/
theorem original (U : Ultrafilter (ℕ×ℕ)) (cut : (U : Filter (ℕ×ℕ)) ≤ L.lens)
    (A : Axle.TransferLimit R.family R.makes U) :
    ∃ τ : ℕ → ℝ, ∀ d : ℕ, ∃ e : ℕ, ∀ᶠ r in trail, ∀ v : RG17.Free R.family d,
      ∃ w : R.family.label d,
        Axle.full (C:=R.family) F d A (L.level r)
          ((R.family.labels.level d).scaled (τ (L.level r)) (L.shift d r w)) = J r d v ∧
        ‖(R.family.labels.level d).scaled (τ (L.level r)) (L.shift d r w)‖ ≤
          frameCost R d * (β (L.level r)^e * ‖v‖) ∧
        ∀ N p, L.level r ≤ N →
          Axle.root (C:=R.family) R.makes d (L.level r) N p
            (color R d (L.level r) N p (L.shift d r w)) = RG17.atRef L d r (N,p) w ∧
          ‖color R d (L.level r) N p (L.shift d r w)‖ ≤ frameCost R d *
            (β (L.level r)^e * ‖v‖) ∧
          Next.UVStress.quota R.family d (L.level r) N p (RG17.atRef L d r (N,p) w) ≤
            R.family.S.a (L.level r)^d * (β (L.level r)^e * ‖v‖) := by
  have hu := cut.trans L.certified
  obtain ⟨τ,docs⟩ := units R U hu
  refine ⟨τ,fun d => ?_⟩
  obtain ⟨e,earn⟩ := WilsonReportingMeasuredTender.entry B E
    (WilsonReportingMeasuredAdmission.present F J lead aligned) pegs near d
  refine ⟨e,?_⟩
  filter_upwards [earn,pegs.level.growing.eventually_ge_atTop (R.family.ref d)] with r paid hm
  intro v
  obtain ⟨w,price,name⟩ := paid v
  have cost : 0 ≤ frameCost R d := Finset.sum_nonneg fun _ _ => pow_nonneg zero_le_two _
  have avail := mul_le_mul_of_nonneg_left price cost
  refine ⟨w,(WilsonMatrixTicketLanesReportedMaster.measured R F L U hu cut A τ (fun m => (docs m).2.2) d r w hm).trans name,
    (scale R d _ (docs _).1.le (docs _).2.1 _).trans avail,?_⟩
  intro N p hN
  exact ⟨WilsonMatrixTicketLanesReportedMaster.finite R F L d r w N p hm hN,
    (scale R d _ (shrink_pos R.family R.makes hN p).le
      (RG12.Arche.shrink_current (C:=R.family) (p:=p) R.makes hN) _).trans avail,
    (quota R F L d r w hm N p hN).trans_le
      (mul_le_mul_of_nonneg_left price (pow_nonneg (R.family.S.a_pos _).le _))⟩

end YM.Integration.WilsonMatrixTicketLanesReportedAdmission
