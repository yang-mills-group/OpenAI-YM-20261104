import YM.MergeProof.Hens

/-!
Canonical singleton/higher-mode reclosure of an actual regular/forced
polynomial.  The forced singleton is retained at its full Box address.
No Nat-address realization, dormant-slot assumption, change of Rep, or
full-exponent singleton price is needed for this exact Served statement.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.NativeCanonicalReclosure
open Function Finset Lattice Wilson RG Marker
open MergeProof MergeProof.Accent
open scoped Classical BigOperators

variable {V : Type} [DecidableEq V] [Fintype V] {B : Census V}
    {G : Gauge} {n : Side}

def regularSingleton (F : Support n → Config G n → Poly B) : V → Config G n → ℂ :=
  fun v U => (∑ s, F s U).part (B.fire v)

def forcedSingleton (K : Box n → Config G n → Poly B) : V → Box n → Config G n → ℂ :=
  fun v s U => (K s U).part (B.fire v)

omit [Fintype V] in
private theorem octave_sum {I : Type} [Fintype I] (f : I → Poly B) :
    octave (∑ i, f i) = ∑ i, octave (f i) := by
  apply Marker.Poly.ext
  intro q
  by_cases h : 2 ≤ q.val.card
  · rw [crest _ _ h, Poly.part_sum, Poly.part_sum]
    exact Finset.sum_congr rfl (fun i _ => (crest (f i) q h).symm)
  · rw [starlet _ _ (Nat.lt_of_not_ge h), Poly.part_sum]
    symm
    exact Finset.sum_eq_zero (fun i _ => starlet (f i) q (Nat.lt_of_not_ge h))

/-- Exact reclosure leaves the original vacuum profile in `bar` and moves
only degrees at least two into the Carton. -/
theorem restore_eq (P : Rep G n)
    (F : Support n → Config G n → Poly B) (K : Box n → Config G n → Poly B)
    (hF : ∀ s U, (F s U).part B.quiet = 0)
    (hK : ∀ s U, (K s U).part B.quiet =
      profile P.activities (fun i => Complex.ofReal ∘ P.activities.K i) s U) :
    play P B K (fun U => ∑ s, F s U) =
      restore P (regularSingleton F) (forcedSingleton K)
        (fun s U => octave (F s U)) (fun s U => octave (K s U)) := by
  funext U
  have hz : (∑ s, F s U).part B.quiet = 0 := by
    simp only [Poly.part_sum, hF, Finset.sum_const_zero]
  have he : (∑ s, F s U) =
      Mach B (fun v => regularSingleton F v U) + ∑ s, octave (F s U) := by
    calc
      _ = Poly.bead B ((∑ s, F s U).part B.quiet) +
          Mach B (fun v => (∑ s, F s U).part (B.fire v)) +
          octave (∑ s, F s U) := ballots _
      _ = _ := by rw [hz, map_zero, zero_add, octave_sum]; rfl
  have hk (s : Box n) : K s U = bar P.activities B U s +
      Mach B (fun v => forcedSingleton K v s U) + octave (K s U) := by
    calc
      _ = Poly.bead B ((K s U).part B.quiet) +
          Mach B (fun v => (K s U).part (B.fire v)) + octave (K s U) := ballots _
      _ = _ := by rw [hK s U]; rfl
  unfold play restore
  dsimp only
  rw [he, show (fun s => K s U) = _ from funext hk]

/-- The original bounds at the requested exponent are preserved exactly.
There is no auxiliary full-exponent or finite-volume price in this result. -/
theorem served (P : Rep G n) (o : V → Site n) (w : V → ℝ)
    (F : Support n → Config G n → Poly B) (K : Box n → Config G n → Poly B)
    (hF : ∀ s, Burns o s (F s) P.p.threshold)
    (hK : ∀ s, Flow o s (K s) P.p.threshold)
    (hQuiet : ∀ s U, (K s U).part B.quiet =
      profile P.activities (fun i => Complex.ofReal ∘ P.activities.K i) s U)
    {e c : ℝ} (hReg : Towed w id F P.p.B e c)
    (hGas : Towed w Prod.fst K P.p.B e c) :
    Served P (regularSingleton F) (forcedSingleton K)
      (play P B K (fun U => ∑ s, F s U)) o w e c := by
  refine ⟨_, _, ?_, Towed.sift hReg, Towed.sift hGas,
    restore_eq P F K (fun s U => (hF s).sil U) hQuiet⟩
  exact ⟨fun s => ⟨(hF s).sift, fun U => octaves _⟩,
    fun s => ⟨(hK s).sift, fun U => octaves _⟩⟩

end YM.Integration.NativeCanonicalReclosure
