import YM.Integration.FVA1Physical.CenteredVacuum
import YM.MSbar.Ballet.Rove
import YM.Next.MULTISOURCE.Wage

/-! Centering and the actual kinetic reset along the same selected unmarked
trajectory. The small-field onset precedes all periods and upper cutoffs. -/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical
open Filter Lattice RG Wilson Precision Push.Uniform MSbar MSbar.Midpoint
open PhysicalNext.Repeat.Legato
open scoped BigOperators Topology

theorem centered_on_calibrated_family {G : Gauge} (hG : G.Simple) (d : ℝ) (hd : 0 < d) :
    ∃ (C : Family G) (Z : Horizon C.path.levels) (u : G.ColorIndex)
      (K : Kin Z (Next.Foundations.chart G)),
      C.path.levels.clock.kernel.penalty = d ∧ Spec.Calibrated C ∧ C.Makes ∧
      ∀ (s p m : ℕ), 6 ≤ s → 4 ≤ m → p+2 ≤ m → ∀ᶠ k : ℕ in atTop,
        ∀ (N i : ℕ), k ≤ N → ∃ S : Scene C.path.levels i p,
          Realized K N i k p (Lis.sun G u) S ∧
          (∀ j, k ≤ j → j ≤ N →
            let Q := C.path.rep N i j
            let β := C.path.levels.clock.hatBeta j
            let F := Aqua.film Q (S.Poly j) (Heath.Stock.cue Q.beta) p
            ∀ x ∈ Metric.closedBall 0 (Mosaic.vol β),
              ‖F x - F 0‖ ≤ 5 * Mosaic.goalP β p / Mosaic.vol β * ∑ a, ‖x a‖) ∧
          ∀ j, k ≤ j → j < N →
            |Heath.Stock.cue (C.path.rep N i j).beta / Heath.Stock.cue (C.path.rep N i (j+1)).beta -
              Bakery.taste p (S.action j) (Heath.Stock.cue (C.path.rep N i j).beta)| ≤
              Mosaic.goalP (C.path.levels.clock.hatBeta j) p := by
  obtain ⟨C, penalty, calibrated, makes, _, _, ⟨Z, u, K, docket⟩, _⟩ := newyearV hG hd
  refine ⟨C, Z, u, K, penalty, calibrated, makes, ?_⟩
  intro s p m hs hm hp
  have grows := Alto.broad.comp (Multi.Wage.hat_tend hG C.path.levels)
  obtain ⟨k₀, hk₀⟩ := Filter.eventually_atTop.mp (grows.eventually_gt_atTop 0)
  filter_upwards [docket.purse s p m hs hm hp, eventually_ge_atTop k₀] with k paid hwide
  intro N i hkN
  obtain ⟨⟨S, hS⟩, covers⟩ := paid N i hkN
  obtain ⟨tickets, reset, _⟩ := covers S hS
  refine ⟨S, hS, ?_, reset⟩
  intro j hkj hjN
  dsimp only
  intro x hx
  exact centered_vacuum_bound (tickets j hkj hjN) hm
    (div_pos (hk₀ j (hwide.trans hkj)) (by norm_num : (0 : ℝ) < 32)) x hx

end YM.Integration.FVA1Physical
