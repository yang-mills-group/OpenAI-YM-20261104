import YM.Integration.FVA1Physical.Sources.Round2.CopiedLog
import YM.Integration.FVA1Physical.Wilson.EnterRows

/-! The copied physical field at an integration point in the measured Schur
cut has *exactly* the absolute field coordinates used by the next Wilson bank. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Finset Matrix Lattice RG YM.Wilson Tree Precision Exterior Push.Uniform
open MSbar MSbar.Rolling MSbar.Midpoint MSbar.Heath MSbar.Heath.Cottage MSbar.Heath.Stock MSbar.Jade
open MSbar.Lis MSbar.Mosaic MSbar.Bakery MSbar.Bakery.Film MSbar.Kelvin MSbar.Wave
open Next.SectorChange YM.Integration.FVA1Physical.Wilson
open scoped Classical Topology BigOperators
variable {G:Gauge}

theorem copied_drawing_log (A:Issue G) (V:Voice G) (cle:Clear G V) (χ:ChartRatio G) (hχ:LocalRatio χ)
    (X Y:Support A.f) (xy:X⊆Y) (U:Config G A.f) {g:ℝ} (hg:0<g) (Z:Positions (Primary A.c G))
    (lo hi K r δ:ℝ) (small:3*shade G*K<(LocalH.geom_patch G).choose) (pd:(mold A.pre A.F A.v).PosDef) :
    let O:=postcard G A.c g Z
    let ν:=vest (priced A.F A.v A.pre.clip A.pre.path) (g•Z)
    let m:=sampleY A.F A.pre A.v V X Y U (g•Z) ∘ includeX A.F X
    Couch V A.F ν Y χ (linCash A.F (g•Z)) O lo hi K r δ →
    ∀ w∈clipM A.F X Y (hotel A.F X Y V O ν lo hi) χ g m U,
      chartLog g (chambers A.F Y V O ν (draw A.F X U m g w))=
        taps A.F G *ᵥ meetVar Z (berth A.F A.pre A.v V X Y U Z g w) := by
  intro O ν m couch w hit
  let W:=draw A.F X U m g w
  let C:=chambers A.F Y V O ν W
  let t:=sampleY A.F A.pre A.v V X Y U (g•Z)
  have exactLog:chartLog g C=g⁻¹ • Rolling.stamp A.F G (imageNear V A.F C) :=
    copied_hotel_log A.F V cle χ X Y O ν _ couch xy small W hit.1 g
  have exactDraw:imageNear V A.F C=t+(imbed (includeX A.F X))*ᵥ(g•w) :=
    sumsY V A.F X Y O U ν χ hχ cle _ couch xy _ pd w hit
  have project (k:Positions (Key A.F G)):pushG A.F (meetVar Z k)=k := by
    change ((partSpace _ _) ((partSpace _ _).symm (Z,k))).2=k
    rw [ContinuousLinearEquiv.apply_symm_apply]
  rw [exactLog,exactDraw,taps,LinearMap.toMatrix'_mulVec]
  change g⁻¹ • Rolling.stamp A.F G (t+(imbed (includeX A.F X))*ᵥ(g•w))=
    Rolling.stamp A.F G (pushG A.F (meetVar Z (berth A.F A.pre A.v V X Y U Z g w)))
  rw [project,←map_smul,Matrix.mulVec_smul,smul_add,inv_smul_smul₀ hg.ne']
  rfl

end YM.Integration.FVA1Physical.Round2.Curvature
