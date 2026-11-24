import YM.Integration.WilsonPositionHomogeneousLeading
import YM.PhysMS.Frame.Phases

/-! Changing the measuring fields before comparing original character viewers. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionPhaseProfile
open Function Filter Set Finset MeasureTheory Extraction Table Spec OPE OPE.Orbits Climb RG17
  Trace.Pilot PhysMS
open scoped Topology ContDiff Classical BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
  (F : Final C f S) (J : ℝ → PhysMS.tower S) {n : ℕ} {d : Caps n}

private abbrev choices (C : Family G) {n : ℕ} (d : Caps n) :=
  (i : Fin n) → Fin (Module.finrank ℂ (RG17.Free C (d i)))

private abbrev b (C : Family G) (d : ℕ) := Module.finBasis ℂ (RG17.Free C d)
private def word (k : choices C d) : MaxwellSlots C d := fun i => b C (d i) (k i)
private def weight (v : MaxwellSlots C d) (k : choices C d) : ℂ :=
  ∏ i, (b C (d i)).coord (k i) (v i)

private theorem expansion (L : MultilinearMap ℂ (fun i => RG17.Free C (d i)) ℂ)
    (v : MaxwellSlots C d) : L v = ∑ k : choices C d, weight v k * L (word k) := by
  have h : v = fun i => ∑ k, ((b C (d i)).coord k (v i)) • (b C (d i)) k :=
    funext fun i => ((b C (d i)).sum_repr (v i)).symm
  conv_lhs => rw [h]
  rw [MultilinearMap.map_sum]
  exact Finset.sum_congr rfl fun k _ => L.map_smul_univ ..

private def cash (v : MaxwellSlots C d) : ℝ := ∑ k : choices C d, ‖weight v k‖

private theorem cash_cont : Continuous (cash (C:=C) (d:=d)) := by
  have cont (i : Fin n) (k : choices C d) :
      Continuous (fun v : MaxwellSlots C d => (b C (d i)).coord (k i) (v i)) :=
    ((b C (d i)).coord (k i)).continuous_of_finiteDimensional.comp (continuous_apply i)
  unfold cash weight
  fun_prop

private def bill (p : Viewers F) (r : ℝ) (x : Points n) :
    MultilinearMap ℂ (fun i => RG17.Free C (d i)) ℂ :=
  (S.classMoment (spectator F p) d (r • x)).compLinearMap (fun i => (J r (d i)).toLinearMap)

private theorem zero {A B : Points n → ℂ} (x : Points n) :
    ‖iteratedFDeriv ℝ 0 A x - iteratedFDeriv ℝ 0 B x‖ = ‖A x-B x‖ := by
  rw [show iteratedFDeriv ℝ 0 A x-iteratedFDeriv ℝ 0 B x=iteratedFDeriv ℝ 0 (A-B) x from by ext z;simp,
    norm_iteratedFDeriv_zero]
  rfl

variable (reader : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
  (lead : Leading F J) (hG : G.Simple) (X : Scaling S) (foundation : Foundation F reader)

include reader lead hG X foundation in
theorem moving (v : ℝ → MaxwellSlots C d) (v₀ : MaxwellSlots C d)
    (arrives : ∀ i, Tendsto (fun r => v r i) trail (𝓝 (v₀ i)))
    {K : Set (Points n)} (compactK : IsCompact K) (sep : K ⊆ conf n)
    (g : ℝ → ℝ) (hg : Coupling G g) {ε : ℝ} (he : 0 < ε) (N : ℕ) :
    ∀ᶠ r in trail, ∀ x ∈ K, ∀ p q : Viewers F,
      ‖measured F p (J r) (v r) r x - measured F q (J r) (v r) r x‖ ≤ ε * g r ^ N := by
  let A := cash v₀ + 1
  have ap : 0 < A := add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun _ _ => norm_nonneg _) one_pos
  have hv : Tendsto v trail (𝓝 v₀) := tendsto_pi_nhds.mpr arrives
  have bounded := ((cash_cont (C:=C) (d:=d)).tendsto v₀).comp hv
  have paid (k : choices C d) :=
    PhysMS.Frame.negligible F reader J lead hG X foundation 0 (word k) K compactK sep g hg (ε/A) (div_pos he ap) N
  filter_upwards [eventually_all.mpr paid,
    bounded.eventually (ge_mem_nhds (show cash v₀ < A by dsimp only [A];linarith)),hg.positive]
    with r bank limited gp x hx p q
  let L := bill (d:=d) F J p r x - bill (d:=d) F J q r x
  change ‖L (v r)‖ ≤ _
  rw [expansion L (v r)]
  have cost (k : choices C d) : ‖L (word k)‖ ≤ (ε/A) * g r ^ N := by
    change ‖measured F p (J r) (word k) r x - measured F q (J r) (word k) r x‖ ≤ _
    simpa only [zero] using bank k x hx p q
  calc
    _ ≤ ∑ k : choices C d, ‖weight (v r) k * L (word k)‖ := norm_sum_le ..
    _ ≤ ∑ k : choices C d, ‖weight (v r) k‖ * (ε/A * g r ^ N) := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (cost k) (norm_nonneg _)
    _ = cash (v r) * (ε/A * g r ^ N) := by rw [cash, Finset.sum_mul]
    _ ≤ A * (ε/A * g r ^ N) := mul_le_mul_of_nonneg_right limited (mul_nonneg (div_pos he ap).le (pow_nonneg gp.le _))
    _ = _ := by field_simp [ap.ne']

end YM.Integration.WilsonPositionPhaseProfile

