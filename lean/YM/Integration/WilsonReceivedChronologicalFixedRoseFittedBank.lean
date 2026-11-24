import YM.Integration.WilsonOriginalObservedRoseFittedPurse

/-! The finite fitted income at independent physical positions, with its exact power on each face. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalFixedRoseFittedBank
open Function Filter Finset Lattice Wilson RG Source Labels PhysicalNext.Repeat.Legato
open WilsonMeasuredPublicEntrancePanel (Panel)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonReceivedCanonicalVersePortfolio (Selection weight wallet)
open WilsonOriginalObservedRoseCorrectedWords (votes)
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) {n : ℕ} (d : Fin n → ℕ)
  {N per f K requested power t : ℕ} {B : ℝ} {fk : f ≤ K} {cut : K ≤ N}
  (A : Panel R d N per f K fk cut requested power t B) (file : Filed R d K)
  (station : A.slot = file.station) (axes : A.axis = file.A N per)

theorem factor (s : Finset (Fin n)) (b h : ℝ) (p : ℕ) :
    wallet R d (fun _ => b * h ^ p) s = wallet R d (fun _ => b) s * h ^ (p * s.card) := by
  unfold WilsonReceivedCanonicalVersePortfolio.wallet
  simp only [← mul_assoc, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_coe, ← pow_mul]

include station axes in
theorem original (s : (Stock.census (Fin n)).Mode) :
    (∑ q : Selection R d s.val,
      ‖weight R d N per K (votes R d (N := N) (per := per) file A.names A.turn) s.val q‖) ≤
      wallet R d (fun _ => B) s.val * R.family.path.levels.clock.hatBeta K ^ (power * s.val.card) := by
  rw [← factor R d s.val B (R.family.path.levels.clock.hatBeta K) power]
  exact WilsonOriginalObservedRoseFittedPurse.original R d A file station axes s

theorem uniform (b : ℝ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ {N per f K requested power t : ℕ} {fk : f ≤ K} {cut : K ≤ N},
      ∀ (A : Panel R d N per f K fk cut requested power t b) (file : Filed R d K),
        A.slot = file.station → A.axis = file.A N per → ∀ s : (Stock.census (Fin n)).Mode,
          (∑ q : Selection R d s.val,
            ‖weight R d N per K (votes R d (N := N) (per := per) file A.names A.turn) s.val q‖) ≤
              M * R.family.path.levels.clock.hatBeta K ^ (power * n) := by
  let bill (S : Finset (Fin n)) := |wallet R d (fun _ => b) S|
  let M := max 1 (∑ S, bill S)
  have one : 1 ≤ M := le_max_left _ _
  refine ⟨M, one, ?_⟩
  intro N per f K requested power t fk cut A file station axes s
  have room : wallet R d (fun _ => b) s.val ≤ M :=
    (le_abs_self _).trans <| (Finset.single_le_sum (f := bill) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ s.val)).trans (le_max_right _ _)
  have size : s.val.card ≤ n := by simpa only [Fintype.card_fin] using Finset.card_le_univ s.val
  have warm := (R.family.path.levels.fits.delayed K).le
  exact (original R d A file station axes s).trans <|
    mul_le_mul room (pow_le_pow_right₀ warm (Nat.mul_le_mul_left power size))
      (pow_nonneg (zero_le_one.trans warm) _) (zero_le_one.trans one)

end YM.Integration.WilsonReceivedChronologicalFixedRoseFittedBank
end
