import YM.Integration.WilsonPositionThermometerStationSubpower

/-! The normalized original cutoff coordinate is paid directly in the norm
of the physical source, uniformly before the period and the ultraviolet cutoff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionThermometerStationNorm
open Function Set Filter Finset RG Labels Source Lattice Wilson Next.Rank Next.Rank.East Next.Rank.Price
open Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress MergeProof.East
open scoped BigOperators Classical Topology
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {H : (Bel C.book).Hierarchy}

def cost (C : Family G) (d : ℕ) : ℝ :=
  (Fintype.card ((C.labels.level d).Index) : ℝ) * ‖Further.CorrectedLift.ladder C d‖

theorem ladder (C : Family G) (d : ℕ) (w : (Bel C.book).Field d) :
    (C.labels.level d).coeffSize (Further.CorrectedLift.ladder C d w) ≤ cost C d * ‖w‖ := by
  let L := Further.CorrectedLift.ladder C d
  unfold Labels.Frame.coeffSize
  calc
    _ ≤ ∑ i, ‖L‖*‖w‖ := Finset.sum_le_sum fun i _ =>
      (norm_le_pi_norm (L w) i).trans (L.le_opNorm w)
    _ = _ := by simp [cost,L]; ring

theorem original (smooth : G.Simple) (construction : C.Makes) (d : ℕ) (ε : ℝ) (positive : 0<ε) :
    ∀ᶠ k in atTop, ∀ {D : ℕ} (V : Vane C D) (j : Fin (D+1)), j.val=d → V.k=k →
      V.checked f H D → ∀ (w : (Bel C.book).Field j) (N p : ℕ), k<N →
      (C.labels.level j).coeffSize (awake C j k N p (V.wheel.atCut (N,p) j w)) ≤
        (C.path.levels.clock.hatBeta k)^ε * (cost C d * ‖w‖) := by
  filter_upwards [WilsonPositionThermometerStationSubpower.original (f:=f) (H:=H) smooth construction d ε positive,
    (Next.Rank.Station.hat_rate C.path.levels smooth).eventually_ge_atTop 0] with k price pos D V j hj date checked w N p upper
  refine (price V j hj date checked w N p upper).trans (mul_le_mul_of_nonneg_left ?_ ?_)
  · rw [←hj]
    exact ladder C j w
  · exact Real.rpow_nonneg pos _

end YM.Integration.WilsonPositionThermometerStationNorm
end
