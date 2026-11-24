import YM.Integration.WilsonOriginalThermometerFineHarvest
import YM.Integration.WilsonOriginalThermometerFiledPositions
import YM.Integration.WilsonOriginalReceivedFirstMarkers

/-! Separation of the three actual registered children at each payable first join. -/
noncomputable section
namespace YM.Integration.WilsonOriginalThermometerFiledCells
open Filter Set Wilson Lattice RG Source Pressure Extraction Marker Ac
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato QuadraticLocal
open WilsonSeparatedOriginalThermometerCells WilsonOriginalThermometerFineHarvest
open WilsonOriginalThermometerFineCover
open scoped Topology ContDiff BigOperators Classical

variable {G : Gauge} (R : Run G)

/-- One location per mixed face. The quiet and singleton parts pass through unchanged. -/
def first (v : Fin 3) (s : (Stock.census (Fin 3)).Mode) : Prop :=
  v ∈ s.val ∧ (∀ w ∈ s.val, v ≤ w) ∧ 1 < s.val.card

theorem one (s : (Stock.census (Fin 3)).Mode) (mixed : 1 < s.val.card) :
    ∃! v, first v s := by
  have present:s.val.Nonempty := Finset.card_pos.mp (by omega)
  refine ⟨s.val.min' present,⟨Finset.min'_mem _ _,fun x hx => Finset.min'_le _ _ hx,mixed⟩,?_⟩
  intro x hx
  exact le_antisymm (hx.2.1 _ (Finset.min'_mem _ _)) (Finset.min'_le _ _ hx.1)

private theorem other {s : (Stock.census (Fin 3)).Mode} {v : Fin 3} (belongs : first v s) :
    ∃ w ∈ s.val, v ≠ w := by
  by_contra! single
  have one : s.val ⊆ {v} := by
    intro w hw
    simpa only [Finset.mem_singleton] using (single w hw).symm
  have price := Finset.card_le_card one
  simp only [Finset.card_singleton] at price
  exact (not_lt_of_ge price) belongs.2.2

private theorem aperture {N j p : ℕ} {U : RG.Rep G (R.family.side (j+1) p)}
    (H : Opera.Guide R.alloy.B R.kit.shape N j p U) :
    U.p.B = radiusB (R.family.path.levels.clock.hatBeta (j+1)) := by
  rw [H.laws.intake.sizes,H.laws.data.funds.length_eq]
  change _ = radiusB (R.alloy.B.a.clock.hatBeta (j+1))
  rw [Extra.Iteration.block_beta (a:=R.alloy.B.a) (G:=G) j,
    Extra.Iteration.block_eq R.alloy.B.valid j]

/-- On a nonzero original cell the spatial test for every elected withdrawal is satisfied.
The period threshold precedes all dates, placements, genuine cash guides and earlier passports. -/
theorem original (simple : G.Simple) (φ : Test 3) (legal : tsupport φ ⊆ conf 3) (K h q : ℕ) :
    ∃ p₀ : ℕ, ∀ᶠ m : ℕ in atTop, ∀ p ≥ p₀, ∀ (N j : ℕ) (_ : m ≤ j+1) (top : j+1 ≤ N)
    (r : ℝ), 0 < r → r ≤ 1 → R.family.S.a m*(RG16.Lambda R.family.path.levels m)^4 ≤ r →
    ∀ z : Fin 3 → Site (R.family.side N p), weight φ (positions (R:=R) r (N,p)) z ≠ 0 →
    ∀ (U : RG.Rep G (R.family.side (j+1) p)), Opera.Guide R.alloy.B R.kit.shape N j p U →
    ∀ (P : Earn.Passport (R.family.side (j+1) p) (Fin 3)),
    (∀ v,P.origin v=(R.family.S.toDepth top p).parent (z v)) →
    ∀ v t, first v t → ∃ a ∈ t.val, ∃ b ∈ t.val,
      depth R (bill K h q m (j+1)) m (j+1)*(4*U.p.B+2)+2*U.p.B ≤ separation (P.origin a) (P.origin b) := by
  obtain ⟨p₀,paid⟩ := cells R simple φ legal K h q
  refine ⟨p₀,?_⟩
  filter_upwards [paid] with m score
  intro p room N j floor top r rp cap span z live U H P reaches v t active
  obtain ⟨b,mem,away⟩ := other active
  refine ⟨v,active.1,b,mem,?_⟩
  rw [reaches,reaches]
  exact score p room N (j+1) floor top r rp cap span z live v b away U.p.B
    (by rw [aperture R H]; omega)

end YM.Integration.WilsonOriginalThermometerFiledCells
