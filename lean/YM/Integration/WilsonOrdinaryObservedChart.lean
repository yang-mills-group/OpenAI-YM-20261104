import YM.Pier.Lair.Bank
import YM.Integration.WilsonOrdinaryGradeMargins

/-! The original mantle and the prescribed frame price the actual observing chart at
every lattice level, using its own radius. No surjectivity assumption on stopping levels. -/

noncomputable section
namespace YM.Integration.WilsonOrdinaryObservedChart
open Filter Set Spec OPE RG12 RG17 SharpGram
open scoped Topology

variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable (F : Final C f S) (J : ℝ → PhysMS.tower S) (P : Pier.Lair.Present F J)
variable {u : Filter (ℕ × ℕ)} (Q : Lenses.Mantle F u) (L : Layout F) (hL : Pegs Q L)
variable (E : Services C f S)
include P hL E

/-- The simultaneous projected-label lift and evaluation bound on the original
`L.charts`, valid at the common original mantle radius for *all* large `k`. -/
theorem original (d : ℕ) : ∃ K : ℝ, 0 < K ∧ ∀ᶠ k : ℕ in atTop,
    (∀ x : S.Field d, ∃ v : C.label d, S.project d (L.charts d k v) = x ∧
      mass C d v ≤ K * C.path.levels.clock.hatBeta k ^ Lenses.price d *
        C.S.a k ^ d * ‖(J (Q.radius k) d).symm x‖) ∧
    ∀ v : C.label d, ‖(J (Q.radius k) d).symm (S.project d (L.charts d k v))‖ ≤
      K / C.S.a k ^ d * mass C d v := by
  letI := L.notbot
  obtain ⟨D, hD, comp⟩ := Pier.Lair.travails F P d Q E
  let K := max (2*D) (D*(2*Lenses.bonus C d))
  refine ⟨K, lt_of_lt_of_le (by positivity : 0 < 2*D) (le_max_left ..), ?_⟩
  filter_upwards [Load.investors Q E d, comp, eventually_ge_atTop (C.ref d),
      (Next.Rank.Station.hat_rate C.path.levels E.simpleGate).eventually_ge_atTop 0] with k paid hcomp hk hβ
  have ha : 0 < C.S.a k ^ d := pow_pos (C.S.a_pos _) _
  have hb : 0 ≤ C.path.levels.clock.hatBeta k ^ Lenses.price d := pow_nonneg hβ _
  constructor
  · intro x
    obtain ⟨y, q, hy, hq, hm⟩ := paid.1 x
    obtain ⟨v, hv, hz⟩ := L.observes.value d k hk le_rfl q y _ (hm.filter_mono hL.along) (hq.mono_left hL.along)
    refine ⟨v, by rw [← hv]; exact hy, hz.trans ?_⟩
    calc
      _ ≤ 2 * C.path.levels.clock.hatBeta k ^ Lenses.price d * C.S.a k ^ d *
          (D * ‖(J (Q.radius k) d).symm x‖) :=
        mul_le_mul_of_nonneg_left (hcomp.left x) (by positivity)
      _ = (2*D) * C.path.levels.clock.hatBeta k ^ Lenses.price d * C.S.a k ^ d *
          ‖(J (Q.radius k) d).symm x‖ := by ring
      _ ≤ _ := by gcongr; exact le_max_left ..
  · intro v
    obtain ⟨q,hq,hc⟩ := L.observes.purchase d k hk le_rfl v
    have hh := paid.2 _ L.notbot hL.along _ _ _ hc hq
    calc
      _ ≤ D * ‖(Load.tent Q k d).symm (S.project d (L.charts d k v))‖ := hcomp.right _
      _ ≤ D * (2 * Lenses.bonus C d / C.S.a k ^ d * mass C d v) := mul_le_mul_of_nonneg_left hh hD.le
      _ = (D * (2*Lenses.bonus C d)) / C.S.a k ^ d * mass C d v := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (le_max_right ..) ha.le) (mass_nonneg ..)

end YM.Integration.WilsonOrdinaryObservedChart
