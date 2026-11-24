import YM.Integration.WilsonPositionProgramPublicGram
import YM.Integration.WilsonThermometerUnitFilingFourSquareGram

/-! The compact public determining tests evaluated on the original torus at
every microscopic placement, with the actual translated spectator labels. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramPublicMicroscopic
open Function Set Filter Lattice Wilson RG Source Extraction Table Spec
open PhysicalNext.Repeat.Legato RG17 FullVolume Climb Next.UVStress Trace.Pilot PhysMS
open Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register WilsonPositionHomogeneousFrame
open WilsonMatrixTicketLanesSmearedRows WilsonMatrixTicketLanesSmearedPivot
open WilsonThermometerUnitFilingFourSquare
open private companion from YM.Integration.WilsonMatrixTicketLanesNormalizedPivot
open scoped Topology ContDiff Classical BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (J : ℝ → tower S) (Z : WilsonPrescription G)
    {d : ℕ} (B : Profiles R d) {r : ℝ} (hr : 0 < r)

def sheet (z : ℕ×ℕ) (u : R.family.label d) (i : B.probes.index) : ℂ :=
  let e := B.probes.shell i
  Order.smears R.family z.1 z.2 (Fin.cons ⟨d,u⟩ (companion F J Z r ∘ e.letter))
    (dilate hr (test B i))

theorem received {l : Filter (ℕ×ℕ)} [l.NeBot] (order : l ≤ f.fuse)
    {y : S.Field d} (arm : Arm R.family S l d y) :
    Tendsto (fun z => sheet F J Z B hr z (arm.source z)) l (𝓝 (row F J Z B r y)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  let e := B.probes.shell i
  let tail := companion F J Z r ∘ e.letter
  let dims : Caps (e.n+1) := Fin.cons d (fun j => (tail j).1)
  let marks (u : R.family.label d) : R.family.book.Vector dims :=
    fun j => Fin.cases (motive:=fun j => R.family.label (dims j)) u (fun k => (tail k).2) j
  have written (u : R.family.label d) : (fun j => (⟨dims j, marks u j⟩ : R.family.book.Token)) =
      Fin.cons ⟨d,u⟩ tail := by
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  have pass (j) : Tendsto (fun z => marks (arm.source z) j) l (𝓝 (marks arm.label j)) := by
    refine Fin.cases arm.approaches (fun _ => tendsto_const_nhds) j
  have physical := calibrated_smear (d:=dims) F.room.ordered l order (dilate hr (test B i))
    (v:=fun z => marks (arm.source z)) (x:=marks arm.label) pass
  change Tendsto (fun z : ℕ×ℕ => Order.smears R.family z.1 z.2 _ _ ) l
    (𝓝 ((dilate hr (test B i)).applyTo (fun x => S.read x (fun j => ⟨dims j,marks arm.label j⟩)))) at physical
  simp only [written] at physical
  have endpoint : (dilate hr (test B i)).applyTo (fun x => S.read x (Fin.cons ⟨d,arm.label⟩ tail)) =
      row F J Z B r y i := by
    rw [zoom_integral]
    change (test B i).applyTo (fun x => S.read (r • x) (Fin.cons ⟨d,arm.label⟩ tail)) =
      observation F J Z e (test B i) r d y
    rw [on_field F J Z e (test B i) hr]
    apply Test.apply_eq
    intro z hz
    let t : Exterior R.family.book := ⟨e.n,r • z,tail,Work.A05.smul_conf hr hz⟩
    change S.spectra d (S.project d arm.label) t =
      S.spectra d (S.project d (S.representative d y)) t
    rw [arm.represents,S.rep]
  rw [← endpoint,←written arm.label]
  exact physical

/-- Fixed extracted columns have the original ordered UV then period limit. -/
theorem fixed (y : S.Field d) :
    Tendsto (fun z => sheet F J Z B hr z (S.representative d y)) f.fuse
      (𝓝 (row F J Z B r y)) :=
  received F J Z B hr le_rfl
    (⟨fun _ => S.representative d y, S.representative d y, tendsto_const_nhds, S.rep d y⟩ :
      Arm R.family S f.fuse d y)

end YM.Integration.WilsonPositionProgramPublicMicroscopic
