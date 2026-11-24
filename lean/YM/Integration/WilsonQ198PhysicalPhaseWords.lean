import YM.GradedFar.Sunlight

noncomputable section
namespace YM.Integration.WilsonQ198PhysicalPhaseWords
open Function Filter Set PowerSeries
open YM.Integration.GradedFar
open Extraction Table Spec PhysMS Trace.Pilot OPE OPE.Orbits
open FVA2 XSpace XSpace.Normalize XSpace.Structure1 FVA2.Scale FVA2.Scale.Facets
open FVA2.Scale.Equator FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh
open MS MS.Native MS.Land MS.Fleet
open YM.Integration.GradedFar.Tariff YM.Integration.GradedFar.Tariff.Sunshine
open scoped Topology BigOperators Classical ContDiff

variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable (F : Final C f S) (P : ℝ → tower S) {n : ℕ}

/-- A single actual compact chart, including any admitted translations of its centre. -/
def Priced (K : Set (Points n)) (chart : ℝ → Points n → E4 → Points n)
    (γ : ℝ) (L : TraceOrder n) (h : ℕ) (v : ListInput G n h) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ r in trail, ∀ x ∈ K, ∀ o : E4, ∀ t u : Viewers F,
    ‖δ L (fun y => frank F P t h r y v) (chart r x o) -
      δ L (fun y => frank F P u h r y v) (chart r x o)‖ ≤ ε * r ^ γ

theorem original (K : Set (Points n)) (chart : ℝ → Points n → E4 → Points n)
    (separated : ∀ r : ℝ, 0 < r → ∀ x ∈ K, ∀ o, chart r x o ∈ conf n)
    (γ : ℝ) (pos : ∀ᶠ r : ℝ in trail, 0 < r)
    (going : ∀ h, ∀ᶠ r in trail, Going F P h r)
    (wages : ∀ h (a : Axis) (v : Sec G h) (j : Toon G (h+1)), ∃ B : ℝ,
      0 ≤ B ∧ ∀ᶠ r in trail, ‖coord j (push F P h a r v)‖ ≤ B)
    (value : ∀ h v, Priced F P K chart γ [] h v)
    (L : TraceOrder n) : ∀ h v, Priced F P K chart γ L h v := by
  classical
  induction L with
  | nil => exact value
  | cons q L ih =>
    intro h v ε hε
    let raised (j : Toon G (h+1)) : ListInput G n (h+1) :=
      update (climbing v) q.1 (theory j)
    choose B nonnegative bounds using wages h q.2 (v q.1)
    let total : ℝ := ∑ j, B j
    have htotal : 0 ≤ total := Finset.sum_nonneg (fun j _ => nonnegative j)
    let fee : ℝ := ε / (1 + total)
    have hfee : 0 < fee := div_pos hε (by linarith)
    have allRaised : ∀ᶠ r in trail, ∀ j : Toon G (h+1), ∀ x ∈ K, ∀ o : E4,
        ∀ t u : Viewers F,
          ‖δ L (fun y => frank F P t (h+1) r y (raised j)) (chart r x o) -
            δ L (fun y => frank F P u (h+1) r y (raised j)) (chart r x o)‖ ≤
              fee * r ^ γ :=
      Filter.eventually_all.mpr (fun j => ih (h+1) (raised j) fee hfee)
    filter_upwards [pos, going h, Filter.eventually_all.mpr bounds, allRaised]
      with r hr admitted costs rows
    intro x hx o t u
    have hy := separated r hr x hx o
    rw [physical_cons F P hy hr admitted t L q v, physical_cons F P hy hr admitted u L q v,
      ← Finset.sum_sub_distrib]
    simp_rw [← mul_sub]
    calc
      _ ≤ ∑ j, ‖coord j (push F P h q.2 r (v q.1)) *
          (δ L (fun y => frank F P t (h+1) r y (raised j)) (chart r x o) -
           δ L (fun y => frank F P u (h+1) r y (raised j)) (chart r x o))‖ :=
        norm_sum_le _ _
      _ ≤ ∑ j, B j * (fee * r ^ γ) := Finset.sum_le_sum (fun j _ => by
        rw [norm_mul]
        exact mul_le_mul (costs j) (rows j x hx o t u) (norm_nonneg _) (nonnegative j))
      _ = total * (fee * r ^ γ) := (Finset.sum_mul _ _ _).symm
      _ ≤ (1 + total) * (fee * r ^ γ) :=
        mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hfee.le (Real.rpow_nonneg hr.le _))
      _ = ε * r ^ γ := by dsimp [fee]; field_simp [ne_of_gt (by linarith : 0 < 1 + total)]

end YM.Integration.WilsonQ198PhysicalPhaseWords
