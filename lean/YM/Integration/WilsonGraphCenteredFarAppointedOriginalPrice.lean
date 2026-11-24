import YM.Integration.WilsonGraphCenteredFarOriginalMixedOperand
import YM.Integration.WilsonGraphCenteredPhysicalPairReturn
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace YM.FVA2.GradedFar.AppointedOriginalOperand

open Filter Real Growth Continuation
open Register MS MS.Native MS.Land MS.Book MS.Book.Program
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Enh O.Score O.Canon Scale Dframe Reg.Point
open YangMills YM.Answer.ContinuumLimit YM.Integration
open scoped Topology BigOperators Classical

universe u
variable (g : GaugeGroup) (hg : g.IsSimple) (periods : ℕ → ℕ) (strict : StrictMono periods)
private abbrev V := WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order periods strict)
private abbrev Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
private abbrev Q := WilsonGraphPaperPublication.perspective.{u} g hg
private abbrev H := Elected.Hframe (Z g hg) (V.{u} g hg periods strict).pupil.last
  (V.{u} g hg periods strict).pupil.J
private abbrev publicTable := YangMills.hierarchy (g := g) (V.{u} g hg periods strict).pupil.last
  (V.{u} g hg periods strict).pupil.P
private abbrev heat := ElectedMeasurement.clock (V.{u} g hg periods strict) (Z g hg)

/-- Price of the two original continuum fields against the original #309 row and Dx. -/
def OriginalPrice (h p : ℕ) (K : Set (YangMills.Points 2)) (C B : ℝ) : Prop :=
  ∃ D : ℝ, 0 ≤ D ∧ ∃ e : ℕ, ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ s ≥ 0, exp s ≤ C*(gYM g.core r)^(-B) →
    ∀ (u v : Sec g.core h) (phase : Option (publicTable.{u} g hg periods strict).Character)
      (o : Spacetime) (y : YM.Points 1) (_hy : (WithLp.toLp 2 ![0,y 0] : YangMills.Points 2) ∈ K),
      let w : Window := (r,s)
      let f := r * exp s
      let cost := D*(‖chair g.core h u‖*‖chair g.core h v‖)*(gYM g.core r)^(p+1)*(1+s)^e
      ‖Physical.Y0 (V.{u} g hg periods strict).pupil.last (H.{u} g hg periods strict)
          (fun _ : Fin 1 => h) (fun _ : Fin 1 => h) w (phase,o) (0 : YM.Points 1) y
          (fun _ => u) (fun _ => v) -
        crop p (heat.{u} g hg periods strict r) (Continuation.row (Z g hg) (d := fun _ : Fin 1 => h) (e := fun _ : Fin 1 => h) (0 : YM.Points 1) (fun _ => u) y (fun _ => v) s)‖ ≤ cost ∧
      ‖Physical.Dactual (V.{u} g hg periods strict).pupil.last (H.{u} g hg periods strict)
          r f (phase,o) y (e := fun _ : Fin 1 => h) (fun _ => v) u -
        crop p (heat.{u} g hg periods strict r) (Dx (Z g hg) (Q.{u} g hg).MS (e := fun _ : Fin 1 => h) y (fun _ => v) s u)‖ ≤ cost


private theorem centerCoordinates (y : YM.Points 1) :
    outgoing y = WithLp.toLp 2 ![0,y 0] := by
  apply congrArg (WithLp.toLp 2)
  funext i
  fin_cases i <;> rfl

/-- On the same elected window, heater, sites and fields, the physical all-near and
mixed observables satisfy the original #309 centered two-slot estimates. -/
theorem onWindow (h p : ℕ) (K : Set (YangMills.Points 2)) (compact : IsCompact K)
    (safe : K ⊆ YM.conf 2) {C B : ℝ} (hC : 0 < C) (hB : 0 < B) :
    OriginalPrice.{u} g hg periods strict h p K C B := by
  obtain ⟨D,hD,e,paid⟩ := AppointedCenteredPhysicalReturn.pairedAtNearClock.{u}
    g hg periods strict h p K compact safe hC hB
  refine ⟨D,hD,e,?_⟩
  filter_upwards [paid] with r hr
  intro s hs window u v phase o y hy
  have loc := centerCoordinates y
  have hv : outgoing y ∈ YM.conf 2 := loc.symm ▸ safe hy
  have site : center y hv = ⟨WithLp.toLp 2 ![0,y 0],safe hy⟩ := Subtype.ext loc
  have forecasts := atHeat (Z g hg) (Q.{u} g hg).MS (Q.{u} g hg).matching h p y hv s
    (heat.{u} g hg periods strict r) u v
  rw [site] at forecasts
  rw [← forecasts.1, ← forecasts.2]
  exact hr s hs window u v phase o y hy

end YM.FVA2.GradedFar.AppointedOriginalOperand
