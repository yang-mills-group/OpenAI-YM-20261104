import YM.Integration.NativeCanonicalReclosure

/-!
Canonical reclosure paid only by the marked forced discrepancy. The full
original K remains in the exact source and its quiet profile remains in
`bar`; removing the quiet coefficient does not change any Carton term.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.NativeCanonicalReclosure
open Function Finset Lattice Wilson RG Marker
open MergeProof MergeProof.Accent
open scoped Classical BigOperators

variable {V : Type} [DecidableEq V] {B : Census V}
    {G : Gauge} {n : Side}

theorem octave_nonquiet (p : Poly B) :
    octave (Poly.inject (fun q => if q = B.quiet then 0 else p.part q)) = octave p := by
  apply Poly.ext
  intro q
  by_cases hq : 2 ≤ q.val.card
  · rw [crest _ _ hq, crest _ _ hq]
    have hn : q ≠ B.quiet := by
      intro he
      rw [he] at hq
      simp [Census.quiet] at hq
    exact if_neg hn
  · rw [starlet _ _ (Nat.lt_of_not_ge hq), starlet _ _ (Nat.lt_of_not_ge hq)]

theorem towed_octave_nonquiet {I Y : Type*} {s : I → Support n}
    {K : I → Y → Poly B} {w : V → ℝ} {m : ℕ} {e c : ℝ}
    (h : Towed w s (fun i y => Poly.inject
      (fun q => if q = B.quiet then 0 else (K i y).part q)) m e c) :
    Towed w s (fun i y => octave (K i y)) m e c := by
  have ht := Towed.sift h
  have he :
      (fun i y => octave (Poly.inject (fun q => if q = B.quiet then 0 else (K i y).part q))) =
      (fun i y => octave (K i y)) := by
    funext i y
    exact octave_nonquiet _
  rwa [he] at ht

variable [Fintype V]

/-- The same exact physical source is Served at the marked error price.
No quiet background allowance enters either Carton payment. -/
theorem served_nonquiet (P : Rep G n) (o : V → Site n) (w : V → ℝ)
    (F : Support n → Config G n → Poly B) (K : Box n → Config G n → Poly B)
    (hF : ∀ s, Burns o s (F s) P.p.threshold)
    (hK : ∀ s, Flow o s (K s) P.p.threshold)
    (hQuiet : ∀ s U, (K s U).part B.quiet =
      profile P.activities (fun i => Complex.ofReal ∘ P.activities.K i) s U)
    {e c : ℝ} (hReg : Towed w id F P.p.B e c)
    (hGas : Towed w Prod.fst
      (fun s U => Poly.inject (fun q => if q = B.quiet then 0 else (K s U).part q)) P.p.B e c) :
    Served P (regularSingleton F) (forcedSingleton K)
      (play P B K (fun U => ∑ s, F s U)) o w e c := by
  refine ⟨_, _, ?_, Towed.sift hReg, towed_octave_nonquiet hGas,
    restore_eq P F K (fun s U => (hF s).sil U) hQuiet⟩
  exact ⟨fun s => ⟨(hF s).sift, fun U => octaves _⟩,
    fun s => ⟨(hK s).sift, fun U => octaves _⟩⟩

/-- Separate regular and marked-forced prices combine by their maximum,
while the quiet K and both canonical singleton profiles stay literal. -/
theorem served_nonquiet_separate (P : Rep G n) (o : V → Site n) (w : V → ℝ)
    (hw : ∀ v, 0 < w v)
    (F : Support n → Config G n → Poly B) (K : Box n → Config G n → Poly B)
    (hF : ∀ s, Burns o s (F s) P.p.threshold)
    (hK : ∀ s, Flow o s (K s) P.p.threshold)
    (hQuiet : ∀ s U, (K s U).part B.quiet =
      profile P.activities (fun i => Complex.ofReal ∘ P.activities.K i) s U)
    {e a b : ℝ} (hReg : Towed w id F P.p.B e a)
    (hGas : Towed w Prod.fst
      (fun s U => Poly.inject (fun q => if q = B.quiet then 0 else (K s U).part q)) P.p.B e b) :
    Served P (regularSingleton F) (forcedSingleton K)
      (play P B K (fun U => ∑ s, F s U)) o w e (max a b) :=
  served_nonquiet P o w F K hF hK hQuiet
    (hReg.shrink le_rfl (le_max_left a b) hw)
    (hGas.shrink le_rfl (le_max_right a b) hw)

end YM.Integration.NativeCanonicalReclosure
