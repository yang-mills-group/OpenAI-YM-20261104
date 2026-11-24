import YM.Integration.WilsonMovingLampCoordinates
import YM.Integration.FVA1Physical.Wilson.InletFVA2

/-! Identification of the actual finite joint bank with the all-field Taylor
series of the originally funded shifted Wilson lamps. The field belongs to
the same period before the forest coordinates and Gaussian kernel are used. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingIssuedInlet
open Function Lattice Exterior Wilson Stationary Precision RG Push.Uniform Bloch
open RGComparison.Core16 RGComparison.Core16.Spool RGComparison.Core16.Lumen
open FormalBulk08 Jets Reef Mesa Flat Pose Kemp Rial Lotus Planned.PrimaryIntegral295
open Shore Gorge City Cork Rift Lava Glide Bank Dawn Wine Roof Dove PhysicalNext.Repeat.Legato
open FVA1Physical.Wilson FVA1Physical.Round2.Curvature
open MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage MSbar.Mosaic
open scoped Classical ContDiff BigOperators Topology PowerSeries
variable {G : Gauge} {I : Type} [Fintype I] (J : I → Lamp G)

theorem full {n : Side} (o : I → Site n) (part : Bool) :
    stencilInlet J o part = Jets.paste (fun x : Positions (Primary n G) =>
      look part (tally J o (represent ((tint G (Body 1 n)) x)) )) := by
  let A : Finset (Slice J) := Finset.univ
  let q := lampShape J part A
  let s := inletSlot J o
  have smooth : ContDiffAt ℝ ∞ (fun x => q (Lumen.vector x)) 0 := by
    change ContDiffAt ℝ ∞ (q ∘ (tint G (↑A))) 0
    apply ContDiffAt.comp
    · have source : ContDiffAt ℝ ∞ q 0 := (lampShape_hot J part A).of_le le_top
      simpa using source
    · fun_prop
  have fields : (fun x : Positions (Primary n G) => q (Lumen.vector (x ∘ s))) =
      fun x => look part (tally J o (represent ((tint G (Body 1 n)) x))) := by
    funext x
    rw [← exhibition J o]
    apply congrArg (fun z => look part (exhibit J z))
    funext i
    simp only [selectLinks, A, Finset.mem_univ, dif_pos, Function.comp_apply]
    exact (Work.F03.represent_link ((tint G (Body 1 n)) x) (legs J o i)).symm
  apply PowerSeries.ext
  intro i
  rw [stencilInlet, PowerSeries.coeff_mk]
  unfold lampRow
  rw [WilsonMovingLampCoordinates.tensor]
  change MvPolynomial.rename s (PowerSeries.coeff i (Jets.paste (fun x => q (Lumen.vector x)))) = _
  rw [← WilsonMovingTaylorConvention.coefficient, WilsonMovingTaylorConvention.occupied s _ smooth, fields]

/-- The exact source of the conditional finite field at the real dated step;
no hypothesis equating the two banks or their emitted coefficients. -/
theorem joint (A : Issue G) (o : I → Site A.f) (part : Bool) :
    jointFieldBank J A o part =
      enterRows A (Jets.paste (fun x : Positions (Primary A.f G) =>
        look part (tally J o (represent ((tint G (Body 1 A.f)) x))))) := by
  rw [← inlet_FVA2, full]

/-- A single independent formal column, at any registered true offset,
expressed as a purchased nonlinear incoming bank with its actual units. -/
theorem booked {G : Gauge} (R : Run G) {d D : ℕ}
    (L : ∀ i, Lodge ((R.alloy.B.a.clock.op i 0).patch)) (a : hue G) (depth : d < D)
    (N per : ℕ) (b : Letter (R.family.labels.level d)) (f : Dawn.Studio D)
    (k : ℕ) (bound : ((R.family.labels.level d).grades (mint _ b)).2 ≤ k)
    (o : Site (R.family.side N per)) :
    let F := R.family.labels.level d
    let n := R.family.side N per
    let w := Dawn.notch (pet F b) ((Dawn.paper_fits (pet F b)).trans (Nat.le_trans d.le_succ depth)) f
    let lamp := investment (R.makes.sections d) (CoefficientBridge.run_valuation R d) (mint F b)
    PowerSeries.map (MvPolynomial.rename (WilsonMovingSectionLamp.place G o)).toRingHom
      (PowerSeries.X ^ (F.grades (mint F b)).2 *
        Kemp.banner k (WilsonRunFormalMarkedStep.graph R L a depth N N b f) n) =
      PowerSeries.C (MvPolynomial.C w) *
        stencilInlet (fun _ : Fin 1 => lamp) (fun _ => o) false := by
  intro F n w lamp
  rw [WilsonMovingSectionLamp.ultraviolet R L a depth N per b f k bound o, full]
  congr 2
  funext x
  simp [Spool.tally, Spool.look,lamp]

end YM.Integration.WilsonMovingIssuedInlet
end
