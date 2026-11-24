import YM.OPE.Therm.Rite
import YM.OPE.Therm.Bath

/-! Event probabilities for flags touching a finite set of sites under the
actual coarse Wilson law. The combinatorial constant is independent of period. -/

namespace YM.Integration.FVA1Physical

open Filter MeasureTheory Lattice RG Wilson OPE.Therm

/-- A flag on an anchor site arises from an incident plaquette. The base of
that plaquette is at distance at most two from the site. -/
theorem anchoredFlag_probability {G : Gauge} {H : History G} (hH : H.Selected)
    (hP : Poetry H.levels) (hG : G.Simple) :
    ∀ᶠ i : ℕ in atTop, ∀ (N n : ℕ) (_ : i ≤ N) (A : Support (H.S.side i n)),
      let t := (H.rep N n i).p.threshold
      (scene H N n i).real {U | ¬ Healthy t A U} ≤
        ((A.card * 5 ^ 4 * Fintype.card PlaqAxes : ℕ) : ℝ) * vanishP H.levels i := by
  filter_upwards [rare hP hG hH, narrow (H := H) hG] with i hprob ht
  intro N n hi A t
  letI := probability (p := n) hH hi
  let J : Finset (Face (Per (H.S.side i n))) := (halo 2 A) ×ˢ Finset.univ
  have ht' : cool H.levels i ≤ t := by
    change _ ≤ (H.rep N n i).p.threshold
    rw [(hH.represents N n i hi).vac]
    change _ ≤ H.levels.clock.threshold i
    linarith only [ht.1, ht.2]
  have hin : {U : Config G (H.S.side i n) | ¬ Healthy t A U} ⊆
      (House.chilly J (cool H.levels i))ᶜ := by
    intro U hu hj
    obtain ⟨x, hA, hx⟩ := Finset.not_disjoint_iff.mp hu
    obtain ⟨z, hz, hU⟩ := (flags_spec t U x).mp hx
    have hy : z.1 ∈ halo 2 A := halo_spec.mpr ⟨x, hA,
      (separation_comm x z.1).le.trans (Work.E01.sep_touched z x hz)⟩
    exact (not_lt_of_ge (hj z (Finset.mem_product.mpr ⟨hy, Finset.mem_univ _⟩))) (ht'.trans_lt hU)
  have hc : J.card ≤ A.card * 5 ^ 4 * Fintype.card PlaqAxes := by
    simpa [J] using Nat.mul_le_mul_right (Fintype.card PlaqAxes) (Corona.halo_size A 2)
  exact ((measureReal_mono (μ := scene H N n i) hin).trans
    (House.cool_miss (vanishP H.levels i) (hprob N hi n) J)).trans
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc) (Real.exp_pos _).le)

end YM.Integration.FVA1Physical
