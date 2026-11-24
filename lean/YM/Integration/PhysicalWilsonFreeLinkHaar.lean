import YM.RGComparison.Core16.Germ
import YM.WilsonCoeffUV.Step.NoiseUnit

/-! Relative and absolute free-link charts describe the same Haar integral
at any coarse gauge field, including the original varying aperture. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.PhysicalWilsonFreeLinkHaar
open Function Lattice Wilson RG Tree Precision Exterior FreeResolvent WilsonCoeffUV MeasureTheory
open RGComparison.Core16.Descent
open scoped Classical BigOperators Matrix.Norms.Frobenius

variable {G:Gauge} {c f:Side} (S:StepData c f) (F:Forest S.ratio)

def haar : Measure (F.Slice G):=Measure.pi fun _=>G.probHaar

def move (V:Config G c):F.Slice G≃ᵐF.Slice G :=
  MeasurableEquiv.piCongrRight fun i=>MeasurableEquiv.mulRight (replica S.ratio V i)

theorem preserving (V:Config G c):MeasurePreserving (move S F V) (haar S F) (haar S F):=
  measurePreserving_pi _ _ (fun i:F.Free =>measurePreserving_mul_right G.probHaar (replica S.ratio V i))

theorem actual (V:Config G c) (a:AxisChart G F):
    lifting F V a=F.drape (move S F V (fun i=>G.lieExp (a i))):=rfl

theorem all {Z:Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] (V:Config G c) (value:Config G f→Z):
    (∫ z,value (F.drape (move S F V z)) ∂haar S F)=∫ z,value (F.drape z) ∂haar S F:=
  (preserving S F V).integral_comp' (fun z=>value (F.drape z))

theorem aperture {Z:Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] (V:Config G c)
    (A:Set (F.Slice G)) (value:Config G f→Z):
    (∫ z,(move S F V ⁻¹' A).indicator (fun y=>value (F.drape (move S F V y))) z ∂haar S F)=
      ∫ z,A.indicator (fun y=>value (F.drape y)) z ∂haar S F:=by
  rw [←(preserving S F V).integral_comp' (A.indicator (fun y=>value (F.drape y)))]
  apply integral_congr_ae
  filter_upwards with z
  by_cases h:move S F V z∈A <;> simp [h]

theorem conditioned (V:Config G c) (A:Set (F.Slice G)) (physical:Config G f→ℝ)
    (mark:Config G f→ℂ) (β:ℝ) (tag:S.Choices):
    let w:=fun u:Config G f=>physical u*Real.exp (-β*noiseTaylor S V u tag)
    let full:=fun u:Config G f=>(w u:ℂ)*mark u
    let raw:=fun z:F.Slice G=>F.drape (move S F V z)
    ((∫ z,(move S F V ⁻¹' A).indicator (fun y=>full (raw y)) z ∂haar S F)/
      (∫ z,(move S F V ⁻¹' A).indicator (fun y=>(w (raw y):ℂ)) z ∂haar S F))=
      (∫ z,A.indicator (fun y=>full (F.drape y)) z ∂haar S F)/
        (∫ z,A.indicator (fun y=>(w (F.drape y):ℂ)) z ∂haar S F):=by
  intro w full raw
  exact congrArg₂ (·/·) (aperture S F V A full) (aperture S F V A (fun u=>(w u:ℂ)))

theorem coordinates (B:fieldDir G c 1) (x:AxisChart G F):
    noiseTaylor S (represent B) (F.drape (fun i=>G.lieExp (x i))) (tac S)=
      jointPen G S (Sum.elim (flatten (sliceCoord S F x)) (flatten B)):=by
  rw [drape_coord S F x]
  change noiseTaylor S (represent B) (represent (sliceCoord S F x)) (tac S)=
    noiseTaylor S (mantle (flatten B)) (mantle (flatten (sliceCoord S F x))) (tac S)
  rw [placed,placed]

end YM.Integration.PhysicalWilsonFreeLinkHaar
end
