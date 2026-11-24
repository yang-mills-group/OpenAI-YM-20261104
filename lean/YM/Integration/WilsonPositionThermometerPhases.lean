import YM.Integration.WilsonPositionThermometerOscillation
import YM.PhysMS.Frame.Phases

/-! The actual continuum position thermometer is independent, to every
coupling order, of the chosen original vacuum viewer. No coefficient
of its interacting value is inferred from this phase comparison. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionThermometerPhases
open Function Filter Set Finset Metric MeasureTheory Lattice Wilson RG Source Extraction Table Spec
open OPE OPE.Orbits Climb Trace.Pilot Next.UVStress RG12 RG17 PhysMS PhysicalNext.Repeat.Legato
open XSpace XSpace.Normalize XSpace.Rose WilsonPositionThermometerReading
open scoped Topology ContDiff Classical BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book} (F : Final R.family f S)
variable (J : ℝ → PhysMS.tower S)
variable (reader : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (H : Leading F J)
    (hG : G.Simple) (X : Scaling S) (foundation : Foundation F reader)

def part (p : Viewers F) (r : ℝ) (x : Points 3) (s : Badge) : ℂ :=
  PhysMS.measured F p (J r) (d:=fun _ : Fin 3=>6) (leg R.family s) r x

def raw (p : Viewers F) (r : ℝ) (x : Points 3) : ℂ :=
  WilsonPositionThermometerConnected.value (part F J p r x)

private theorem norm_zero (P Q : Points 3 → ℂ) (x : Points 3) :
    ‖iteratedFDeriv ℝ 0 P x - iteratedFDeriv ℝ 0 Q x‖ = ‖P x-Q x‖ := by
  rw [show iteratedFDeriv ℝ 0 P x-iteratedFDeriv ℝ 0 Q x = iteratedFDeriv ℝ 0 (P-Q) x from by ext z;simp,
      norm_iteratedFDeriv_zero]
  rfl

include reader H hG X foundation in
theorem small {K : Set (Points 3)} (hk : IsCompact K) (sep : K ⊆ conf 3) {δ : ℝ} (hd : 0<δ) :
    ∀ᶠ r in trail,∀ s : Badge,∀ x∈K,∀ p : Viewers F,s.Nonempty → ‖part F J p r x s‖ < δ := by
  apply Filter.eventually_all.mpr
  intro s
  have bank := PhysMS.Frame.all_leading F reader J H hG X foundation 0 (leg R.family s) K hk sep δ hd
  filter_upwards [bank] with r ready x hx p hs
  have cost := ready x hx p
  rw [norm_zero,free R.family hG (sep hx) s hs,sub_zero] at cost
  exact cost

include reader H hG X foundation in
theorem same {K : Set (Points 3)} (hk : IsCompact K) (sep : K ⊆ conf 3)
    (g : ℝ→ℝ) (hg : Coupling G g) {ε : ℝ} (he : 0<ε) (q : ℕ) :
    ∀ᶠ r in trail,∀ x∈K,∀ p v : Viewers F, ‖raw F J p r x-raw F J v r x‖ ≤ ε*(g r)^q := by
  have price : ∀ᶠ r in trail,∀ s : Badge,∀ x∈K,∀ p v : Viewers F,
      ‖part F J p r x s-part F J v r x s‖ ≤ (ε/13)*(g r)^q := by
    apply Filter.eventually_all.mpr
    intro s
    have bill := PhysMS.Frame.negligible F reader J H hG X foundation 0 (leg R.family s) K hk sep g hg (ε/13) (by positivity) q
    filter_upwards [bill] with r hr x hx p v
    simpa only [part,norm_zero] using hr x hx p v
  filter_upwards [small F J reader H hG X foundation hk sep one_pos,price] with r ready paid x hx p v
  have cv := WilsonPositionThermometerOscillation.difference
    (fun s hs => (ready s x hx p hs).le) (fun s hs => (ready s x hx v hs).le)
    (fun s _ => paid s x hx p v)
  exact cv.trans_eq (by ring)

end YM.Integration.WilsonPositionThermometerPhases
