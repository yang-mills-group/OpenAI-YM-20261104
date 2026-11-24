import YM.Integration.WilsonGeneralReducedPhysicalSelfGappedBoard
import YM.Integration.WilsonOriginalPublicNodalQuadraticShift

/-! A single finite positive quadrature of an uncentered self and its signed
adjoint, usable through the all-axis gap interpolation. Its true upper is
bought on the selected original field, before the planting depth or order. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonGeneralReducedPhysicalSelfGappedHome
open Function Filter Finset Set Lattice Wilson RG Source Labels Cells OPE Extraction Spec
open Table Table.Pairing Extraction.Banks RG17 PhysicalNext.Repeat.Legato Climb GapsContact Next.Rank
open XSpace XSpace.Normalize XSpace.Rose XSpace.Cirrus MS MS.Menus MS.Land MS.Theater Local.Physical
open FVA2 FVA2.Register Trace.Pilot PhysMS Frame XSpace.Structure1 Maxwell Maxwell.Wick
open WilsonOriginalBlissMixedGram (columns grades)
open WilsonMeasuredPublicEntranceOrderedPins (physical)
open WilsonPositionHomogeneousFrame (homogeneous)
open WilsonThermometerUnitFilingFourSquare (Arm)
open WilsonGeneralReducedPhysicalSelfGappedBoard (atPlace)
open WilsonGeneralReducedPhysicalSelfFullWord (finiteWord atNode)
open WilsonOriginalPublicPlantedGram (measured)
open WilsonPositionProgramPublicContrast (assay)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)
    (Z:WilsonPrescription G){g:G.Simple}{M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {T:Prescription (Press.portDeck G)}{dial:Bool}(H:Main.Match Z g M T dial){Y:(Bel R.family.book).Hierarchy}
    {l:Filter (ℕ×ℕ)}(B:Deck G)(h:ℕ)(a:Axis)
local notation "I" => Glyph B h
private theorem weighted (v:I→ℂ){ι:Type}[Fintype ι](w:ι→ℝ)(A:ι→(I→I→ℂ)):
    assay v v (∑i,w i • A i)=∑i,w i • assay v v (A i):=by
  let L:(I→I→ℂ)→ₗ[ℝ]ℂ:={
    toFun:=assay v v
    map_add':=by intro p q; simp [assay,mul_add,sum_add_distrib]
    map_smul':=by
      intro r p
      simp [assay,smul_sum]
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      ring}
  exact (map_sum L _ _).trans (sum_congr rfl fun i _=>map_smul L _ _)

include a in
private theorem clear {p:Points 2}{b:ContDiffBump p}{σ:ℝ}(sp:0<σ)
    (gap:∀y∈tsupport b,∀i:Axis,σ<y 1 i-y 0 i):tsupport b ⊆ conf 2:=by
  intro y hy i j equal
  have neq:y 0 a≠y 1 a:=by have h:=gap y hy a;linarith
  fin_cases i <;> fin_cases j
  · rfl
  · exact (neq (congrArg (fun v:E4=>v a) equal)).elim
  · exact (neq (congrArg (fun v:E4=>v a) equal.symm)).elim
  · rfl

include H in
theorem original (lead:Leading F J)(obedient:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d)(below:l≤f.fuse):
    ∃(p:Points 2)(b:ContDiffBump p)(σ k:ℝ),0<σ ∧ 0<k ∧ (∀y∈tsupport b,∀i:Axis,σ<y 1 i-y 0 i) ∧
    (∀x:RG17.Free R.family h,∃A:ℝ,0≤A ∧ ∀ᶠr in trail,∀(arm:Arm R.family S l h (homogeneous F J Z r h x)),
      ∀{ι:Type}[Fintype ι](s:ℕ)(o:ι→Fin 2 → Lattice.Cover)(y:ι→Points 2)(μ:ι→ℂ),
      (∀i,y i∈tsupport b) → (∀i,Order.grid R.family s (o i)=r • y i) → (∀i,Order.grid R.family s (o i)∈conf 2) →
      ∀ε:ℝ,0<ε → ∀ᶠ n:ℕ×ℕ in l,∀z:ι → Lattice.Cover,‖∑i,μ i*
        physical (grades h h) s (fun l=>o i l+z i) n.1 n.2 (columns R a h h (arm.source n) (arm.source n))‖≤
          (∑i,‖μ i‖)*A+ε) ∧
    ∀q:ℕ,∀(L:Filter ℝ){t:ℝ→ℝ},(∀ᶠr in L,0<t r) → Tendsto t L (𝓝 0) →
    ∀(D:ℕ)(C:ℝ),∃j₀:ℕ,∀ᶠ r in L,∀j≥j₀,(j:ℝ)≤C*(-Real.log (t r))^D →
    ∀{cap}(_:Handoff.Directory Z j cap),Handoff.Directory.budget G 2 h+q≤cap →
    ∀c∈(Z.run.step j).Box,∀u:ℝ,|u|≤8*t r →
    ∀{ι:Type}[Fintype ι](w:ι→ℝ)(y:ι→Points 2),(∀i,0≤w i) → (∑i,w i=1) → (∀i,y i∈tsupport b) →
    ∀v:I→ℂ,k*‖v‖^2≤‖∑i,w i • cash q u (finiteWord Z a j (atPlace (Z.run.step j) c (y i)) v)‖:=by
  obtain ⟨p,b,σ,k,sp,kp,gaps,margin⟩:=
    WilsonGeneralReducedPhysicalSelfGappedBoard.original Z H a (id:I→I) injective_id
  refine ⟨p,b,σ,k,sp,kp,gaps,?_,?_⟩
  · intro x
    exact WilsonOriginalPublicNodalQuadraticShift.original R F J Z h a x g lead obedient below b.hasCompactSupport
      (clear a sp gaps)
  · intro q L t pos small D C
    obtain ⟨j₀,paid⟩:=margin q L pos small D C
    refine ⟨j₀,?_⟩
    filter_upwards [paid] with r due j later short cap P room c box u heat ι ins w y positive unit support v
    have sale:=due j later short P room c box u heat w y positive unit support v
    rw [weighted] at sale
    have eq (i:ι):=atNode Z a j P (atPlace (Z.run.step j) c (y i)) v q u rfl room
    simpa only [eq] using sale

end YM.Integration.WilsonGeneralReducedPhysicalSelfGappedHome
