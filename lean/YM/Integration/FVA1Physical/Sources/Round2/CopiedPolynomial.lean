import YM.Integration.FVA1Physical.Sources.Round2.CopiedDrawing
import YM.Integration.FVA1Physical.Sources.Round2.PosteriorReclock

/-! An independently transported polynomial insertion has zero source Taylor
error on every normalized live Schur draw, including its full exterior. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Finset Matrix Lattice RG YM.Wilson Tree Precision Exterior Push.Uniform
open MSbar MSbar.Rolling MSbar.Midpoint MSbar.Heath MSbar.Heath.Cottage MSbar.Heath.Stock MSbar.Jade
open MSbar.Lis MSbar.Mosaic MSbar.Bakery MSbar.Bakery.Film MSbar.Kelvin MSbar.Wave MSbar.Bakery.Portal MSbar.Cacao
open Next.SectorChange YM.Integration.FVA1Physical.Wilson
open scoped Classical Topology BigOperators
variable {G:Gauge}

theorem clockReading_enter (A:Issue G) (src:Nesting G A.f) (z:View (Joint A.F G)) (p:ℕ) (g:ℝ) :
    clockReading p g (enterRows A src) z=clockReading p g src (taps A.F G *ᵥ z) := by
  unfold clockReading taste picture
  simp only [PowerSeries.coeff_map]
  exact sum_congr rfl fun i _=>congrArg (fun u:ℝ=>g^i*u) (enter_read A src z i)

theorem clipped_inherited_draw (A:Issue G) (V:Voice G) (cle:Clear G V) (χ:ChartRatio G) (hχ:LocalRatio χ)
    (X Y:Support A.f) (xy:X⊆Y) (U:Config G A.f) {g:ℝ} (hg:0<g) (Z:Positions (Primary A.c G))
    (lo hi K r δ:ℝ) (small:3*shade G*K<(LocalH.geom_patch G).choose) (pd:(mold A.pre A.F A.v).PosDef)
    (src:Nesting G A.f) (series:PowerSeries ℝ) (m p:ℕ) :
    let O:=postcard G A.c g Z
    let ν:=vest (priced A.F A.v A.pre.clip A.pre.path) (g•Z)
    let loc:=sampleY A.F A.pre A.v V X Y U (g•Z) ∘ includeX A.F X
    Couch V A.F ν Y χ (linCash A.F (g•Z)) O lo hi K r δ →
    ∀ w∈clipM A.F X Y (hotel A.F X Y V O ν lo hi) χ g loc U,
      clockReading p g (sourceClock m series src) (chartLog g (chambers A.F Y V O ν (draw A.F X U loc g w)))=
        clockReading p g (inheritedBank A m series src) (meetVar Z (berth A.F A.pre A.v V X Y U Z g w)) := by
  intro O ν loc paid w hit
  rw [copied_drawing_log A V cle χ hχ X Y xy U hg Z lo hi K r δ small pd paid w hit]
  exact (clockReading_enter ..).symm

end YM.Integration.FVA1Physical.Round2.Curvature
