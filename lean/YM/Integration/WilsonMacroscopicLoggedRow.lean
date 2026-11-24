import YM.Integration.WilsonMacroscopicProjectedRow

/-! An integer engineering power for the actual orbit-averaged grade, using only
the finitely many unaveraged modes of that grade on the enrolled reader. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicLoggedRow
open Function Set Filter MeasureTheory Table Extraction OPE OPE.Orbits OPE.Orbits.Reader OPE.Log
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
    (F : Spec.Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    {I : Type} [Fintype I] {d : I → ℕ} (v : Labels S d)

def top (m : ℕ) := (bands F.sector.derivatives m).filter (fun j => j.fst = m)

/-- The only raw OPE terms whose costs are needed at this grade. -/
def Priced (m : ℕ) (M η : ℝ) : Prop :=
    ∀ j : ↥(top F m), ∃ k : ℕ, ∀ᶠ r : ℝ in 𝓝[>]0, ∀ (x:I→E4) (o:E4),
      WithinRoom r M η x o →
        ‖Q.port.ope j.val x (names v) o‖ ≤ badge r ^ k * r ^ ((m:ℝ) - weight d)

theorem issued (log : SingleLog F Q.port) {M η : ℝ} (hM : 0 ≤ M) (hη : 0 < η)
    (m : ℕ) : Priced F Q v m M η := by
  intro j
  have grade : j.val.fst = m := (Finset.mem_filter.mp j.property).2
  obtain ⟨k,h⟩ := log.terms I (names v) η M hη hM j.val
  refine ⟨k,?_⟩
  filter_upwards [h,(show ∀ᶠ r:ℝ in 𝓝[>]0,0<r from self_mem_nhdsWithin)] with r h hr x o fit
  have hh := (h x o fit).2
  rw [grade] at hh
  rw [weighting v,Real.rpow_sub hr,Real.rpow_natCast,Real.rpow_natCast]
  exact hh

theorem original (paid : Services C f S) {M η : ℝ} (hM : 0 ≤ M) (hη : 0 < η)
    (m : ℕ) (price : Priced F Q v m M η) :
    ∃ (k : ℕ) (D : ℝ), 0 < D ∧ ∀ᶠ r : ℝ in 𝓝[>]0,
      ∀ (x : I → E4) (o : E4), WithinRoom r M η x o →
        ‖Q.fresh m x o v‖ ≤ D * badge r ^ k * r ^ ((m:ℝ)-weight d) := by
  choose n hn using price
  let k := ∑ j : ↥(top F m), n j
  have hk (j : ↥(top F m)) : n j ≤ k :=
    Finset.single_le_sum (f:=n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  let B := ∑ j ∈ top F m, ‖Q.cutTest m m (Q.port.loaded j m)‖
  have bpos : 0 ≤ B := Finset.sum_nonneg (fun j _ => norm_nonneg _)
  refine ⟨k, 1+B, by linarith, ?_⟩
  have joint := Filter.eventually_all.mpr hn
  filter_upwards [joint,WilsonMacroscopicProjectedRow.bridge F Q v paid hM hη m,
    (show ∀ᶠ r:ℝ in 𝓝[>]0,0<r from self_mem_nhdsWithin),
    ((ge_mem_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds)] with r h bridge hr h1 x o fit
  have money : 1 ≤ badge r := by
    unfold badge run
    linarith [Real.log_nonpos hr.le h1]
  let a := badge r ^ k * r ^ ((m:ℝ)-weight d)
  have rough : ‖WilsonMacroscopicProjectedRow.raw F Q v m x o‖ ≤ a * B := by
    rw [WilsonMacroscopicProjectedRow.exact_grade]
    refine (norm_sum_le _ _).trans ?_
    change (∑ j ∈ top F m, _) ≤ a * (∑ j ∈ top F m, _)
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j mem
    rw [norm_smul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (h ⟨j,mem⟩ x o fit).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ money (hk ⟨j,mem⟩)) (Real.rpow_nonneg hr.le _))
  have margin : r ^ ((m:ℝ)-weight d+1/2) ≤ a := calc
    _ ≤ r ^ ((m:ℝ)-weight d) := Real.rpow_le_rpow_of_exponent_ge hr h1 (by linarith)
    _ ≤ _ := le_mul_of_one_le_left (Real.rpow_nonneg hr.le _) (one_le_pow₀ money)
  have close := norm_add_le (Q.fresh m x o v - WilsonMacroscopicProjectedRow.raw F Q v m x o)
    (WilsonMacroscopicProjectedRow.raw F Q v m x o)
  rw [sub_add_cancel] at close
  calc
    _ ≤ _ := close
    _ ≤ a + a * B := add_le_add ((bridge x o fit).trans margin) rough
    _ = (1+B) * badge r ^ k * r ^ ((m:ℝ)-weight d) := by dsimp [a];ring

end YM.Integration.WilsonMacroscopicLoggedRow
