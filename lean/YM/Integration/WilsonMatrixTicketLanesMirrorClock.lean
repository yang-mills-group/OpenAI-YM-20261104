import YM.FVA2.RankHistory
import YM.FormalOPE.RG10.BlockGauge.Fabric
import YM.MatchingR2.Top.Weather

/-! Paired finite Wilson regulators on the original physical sizes, block choices, and temperatures. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesMirrorClock
open Filter Lattice RG FormalOPE.RG10.BlockGauge FVA2.CityHistory FVA2.CityHistory.Delay
open scoped Topology Classical
variable {G : Gauge} (H : History G)

private theorem even (j p : ℕ) : Even (H.S.side j p).val := by
  obtain ⟨r,hr⟩ := H.S.side_four j p
  exact ⟨2*r,by omega⟩

/-- One actual tag at every physical block. A caller may select any such sequence. -/
abbrev Picks (p : ℕ) := ∀ j : ℕ, (H.levels.clock.op j p).Choices

def central (p : ℕ) : Picks H p := fun j =>
  ⟨fun _ => ((H.levels.clock.op j p).patch.center,1),fun _ => (H.levels.clock.op j p).patch.center⟩

/-- Assemble the original cutoff segment, in UV-to-IR order, into the inversion regulator. -/
def segment (p b : ℕ) (σ : Picks H p) : (k : ℕ) → Fabric G (H.S.side (b+k) p)
  | 0 => .endcap _ (even H b p)
  | k+1 => .layer (H.levels.clock.op (b+k) p) (H.levels.blocks (b+k) p).branches
      (σ (b+k)) (even H (b+k+1) p) (segment p b σ k)

/-- The large-block condition holds throughout every late segment, at every period. -/
theorem purchased : ∀ᶠ b : ℕ in atTop, ∀ (p k : ℕ), ∀ j < k,
    Bid.Larger (G:=G) (H.levels.clock.op (b+j) p) := by
  obtain ⟨B,hB⟩ := eventually_atTop.1 (MatchingR2.Top.step_shape H)
  filter_upwards [eventually_ge_atTop B] with b hb p k j _
  exact hB (b+j) (by omega) p

/-- The authentic beta shift is constant beyond the last occupied date. -/
def offset (p b k j : ℕ) : ℝ := H.β (b+k) p (b+min j k) - H.β (b+k) p (b+k)

def quotes (p b k : ℕ) (i : ℕ) : PowerSeries ℝ :=
  Delay.stones (offset H p b k) (k-i)

theorem sound (p b k : ℕ) : Legacy.SoundZ (quotes H p b k) := by
  intro i
  simp [quotes,Delay.stones]

theorem first (p b k : ℕ) : quotes H p b k 0 = 1 := by
  simp [quotes,Delay.stones,offset]

/-- Reading the top-to-bottom account in physical descent order gives the same clock. -/
theorem read_back (p b k j : ℕ) : quotes H p b k (k-j) = Delay.stones (offset H p b k) j := by
  simp only [quotes,Delay.stones]
  congr 3
  simp only [offset]
  congr 3
  omega

theorem physical (p b k j : ℕ) (hj : j ≤ k) : offset H p b k j =
    H.β (b+k) p (b+j) - H.β (b+k) p (b+k) := by simp [offset,min_eq_left hj]

end YM.Integration.WilsonMatrixTicketLanesMirrorClock
