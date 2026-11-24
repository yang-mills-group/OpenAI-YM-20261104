import YM.Integration.WilsonPositionProgramPublicDirectoryBoard

/-! A finite oriented mass matrix from the same Wilson prescription as its
inversion. Every paid corner is the actual continued Handoff against the
original common reflected profile, with all grades and its signed unit. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramPublicDirectoryHearing
open Filter Function Extraction Table Spec PhysMS Lattice Source Labels Maxwell MS MS.Menus
open XSpace XSpace.Normalize XSpace.Rose XSpace.Cirrus Table.Pairing Local.Physical
open WilsonThermometerUnitFilingFourSquare WilsonPositionProgramPublicContrast
open WilsonPositionProgramPublicFourPrice WilsonPositionProgramPublicWide
open WilsonPositionProgramPublicWickGram WilsonPositionProgramPublicReflectedRead
open FVA2 FVA2.Register MS.Land
open scoped Topology BigOperators Classical

variable {G:Gauge} {B:Deck G} {h:ℕ} {K:Type} [Fintype K] (leg:K→Glyph B h)
    {I:Type} [Fintype I] {C:Family G} {S:Table C.book} {f:Extraction.Order}
    {l:Filter (ℕ×ℕ)} [l.NeBot] {d:ℕ} (F:Final C f S)
    {m:I→S.Field d} (arm:(i:I)→Bool→Arm C S l d (m i)) (axis:Axis)
    (Z:WilsonPrescription G) {g:G.Simple}
    {M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))} {T:Prescription (Press.portDeck G)}
    {dial:Bool} (H:Main.Match Z g M T dial)
include H in
theorem original (each:Injective leg) (order:l≤f.fuse) (q:ℕ) :
    ∃ (b:Bulb (center axis) axis) (k:ℝ),0<k ∧
      ∀ L:Filter ℝ,∀t:ℝ→ℝ,(∀ᶠ r in L,0<t r) → Tendsto t L (𝓝 0) →
      ∀(D:ℕ)(J:ℝ),∀ᶠ r in L,∀i≥WilsonPositionAuxiliaryMesh.floor Z.run q (t r),
      (i:ℝ)≤J*(-Real.log (t r))^D → ∀{fret}(P:Handoff.Directory Z i fret),
      Handoff.Directory.budget G 2 h+q≤fret → ∀c∈(Z.run.step i).Box,
      ∀(T R:ℝ)(ht:0<T),0<R → R≤T →
      ∀(w:ℕ×ℕ→I→ℂ)(u:ℕ×ℕ→Bool→K→ℂ)(bare:ℕ×ℕ→ℝ)(A e:ℝ),
        (∀ᶠ z in l,charge (w z)≤A) → (∀ᶠ z in l,|bare z|≤8*t r) →
        (∀ᶠ z in l,∀a v,‖assay (weighted leg (R/T) (u z a)) (weighted leg (R/T) (u z v))
          (WilsonPositionProgramPublicDirectoryBoard.table Z axis b q leg P (bare z) c)-
          WilsonPositionProgramPublicWideHearing.paid F arm axis b ht (w z) z a v‖≤e) →
        ∀η:ℝ,0<η → ∀ᶠ z in l,k*((R/T)^h*‖u z false-u z true‖)^2≤4*e+η:=by
  obtain ⟨b,k,δ,hk,hδ,basin⟩:=WilsonPositionProgramPublicWideHearing.original leg F arm
    Z.scheme Z.store axis each order
  obtain ⟨i₀,use⟩:=eventually_atTop.mp ((goesFront (Expense.Stretched.runs Z.run)).eventually basin)
  refine ⟨b,k,hk,?_⟩
  intro L t pos small D J
  filter_upwards [WilsonPositionProgramPublicDirectoryBoard.original Z H axis b q leg L pos small D J hδ,
    (WilsonPositionAuxiliaryMesh.grows Z.run q L pos small).eventually_ge_atTop i₀] with
    r fees late i ge le fret P cover c hc T R ht hr hrt w u bare A e hA hbare hearing η hη
  apply use i (late.trans ge) c hc T R ht hr hrt w u
    (fun z=>WilsonPositionProgramPublicDirectoryBoard.table Z axis b q leg P (bare z) c)
    A e hA _ hearing η hη
  filter_upwards [hbare] with z hz
  exact fees i ge le P cover c hc (bare z) hz
end YM.Integration.WilsonPositionProgramPublicDirectoryHearing
