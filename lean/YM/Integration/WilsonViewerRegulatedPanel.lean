import YM.Integration.WilsonViewerPhysicalRelease
import YM.Integration.WilsonPublicOutputRegulators

/-! The signed input to the common release on the literal finite original
pack and its full basis of held heads at matching physical addresses. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonViewerElectedHierarchy
open Function Filter Set MeasureTheory Spec Extraction Table PhysicalNext.Repeat.Legato
open OPE OPE.Orbits OPE.Orbits.Reader OPE.Log Climb RG17 PhysMS Trace.Pilot
open Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register FVA2.Scale FVA2.O FVA2.O.Score FVA2.O.Project
open MS MS.Land MS.Fleet MS.Theater Next.Rank RG12 SharpGram WilsonMSDictionaryVector
open WilsonPositionHomogeneousFrame WilsonMatrixTicketLanesSmearedPivot WilsonMacroscopicRichTwoDatePivot
open WilsonMacroscopicRichPositionRows WilsonPublicOutputSmooth
open scoped Topology Classical BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (Z : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {σ : Prescription (Press.portDeck G)}
    {branch : Bool} {simple : G.Simple} (ms : Main.Match Z simple M σ branch)
    (ν : ℝ) {n : ℕ} (d : Fin n → ℕ) (v : (i : Fin n) → Free R.family (d i))
    (h q P E A : ℕ) (panel : Profiles R h) (probe : panel.probes.index → Atom (R:=R) h)
    (site : ∀ j, panel.probes.shell j = WilsonMatrixTicketLanesTwoSites.shell R.family.book.grid h (probe j))
    (K : Set (Points n)) (C D : Test n → ℝ)
local notation "θ" => WilsonPositionHomogeneousFrame.reading F J Z
local notation "pub" => homogeneous F J Z

/-- At each physical radius one set of cutoff labels and reporting layout
serves every smooth test, exterior index and independent inverse parameter. -/
theorem regulated (purchase : ∀ᶠ r in trail,
    ∃ (L : Layout F) (ins : (i : Fin n) → R.family.label (d i)) (out : Dframe.Toon G h → R.family.label h),
      (∀ i, master L (d i) r (ins i) = pub r (d i) (v i)) ∧
      (∀ i, R.family.ref (d i) ≤ L.level r) ∧
      (∀ k, master L h r (out k) = pub r h (WilsonMSDictionaryVector.basis R.family h k)) ∧
      R.family.ref h ≤ L.level r ∧
      let t := r/((θ r)^A)^2
      ∀ tp : 0<t, ∀ ψ : Test n, tsupport ψ ⊆ K →
        let a := fun i => pub r (d i) (v i)
        let X := exterior F J Z panel probe site tp
        let read := fun j => RG17.appeared F a (X j) r ψ
        let value := fun s => experiment R.family d h Z M ν v ψ ((ms.separatedOPE ν).wilson.light h).choose q (θ r) s
        (∀ j, packs (X j) r ψ) ∧
        (∀ j, Integrable (fun z : Points ((X j).n+1) =>
          (X j).test z * RG17.query F a ((X j).offset z) (X j).labels none r ψ)) ∧
        ‖(fun j => (X j).charge F h (RG17.basket Q h a r ψ))-read‖ ≤ C ψ*(((θ r)^A)^2)^(h+1)/(θ r)^E ∧
        ∃ᶠ s : ℝ in atTop, f.late (fun N per =>
          ‖WilsonPublicOutputRegulators.contrast F L X d ins out r ψ (value s) (N,per)‖ ≤ D ψ*(θ r)^(P+A*(2*h+1)))) :
    purchasedRows (F:=F) (Q:=Q) (J:=J) Z M ms ν d v h q P E A panel probe site K C D := by
  filter_upwards [purchase,RG17.positiveLength] with r saved rp
  obtain ⟨L,ins,out,first,fit,last,href,measured⟩ := saved
  intro t tp ψ hs
  obtain ⟨cover,integrable,spatial,signed⟩ := measured tp ψ hs
  exact ⟨spatial, WilsonPublicOutputRegulators.original F J Z L (exterior F J Z panel probe site tp)
    d ins out r ψ (fun i => pub r (d i) (v i)) first fit last href rp cover integrable _ _ signed⟩

end YM.Integration.WilsonViewerElectedHierarchy
end
