import YM.Integration.WilsonReceivedChronologicalFixedRoseGridSeats

/-! Archive the material actually assigned to each supported cell before the two regulators. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalFixedRoseGridArchive
open Function Finset Filter Lattice Wilson RG Marker
open PhysicalNext.Repeat.Legato
open WilsonOriginalMixedBlockRows WilsonMovingForkPrintedFile
open WilsonMovingForkStencilProgramme (Basis)
open WilsonMovingForkStencilCatalogue (Catalogue)
open WilsonMovingForkDepositedPrint (Sheet)
open WilsonMovingForkStencilLine (Received)
open WilsonReceivedChronologicalMaterialCapture (placed)
open WilsonReceivedChronologicalFixedRoseVariation (cells)
open Analysis Table Spec Extraction Next.UVStress StressFlux.Matching Cells WilsonCenteredPhysicalPanel WilsonCenteredCompactBooking
open scoped Classical

variable {G:Gauge}{n K first f:ℕ}(R:Run G)(d:Fin n→ℕ)(φ:Test n)(r:ℝ)(fine:f≤K)


abbrev Ledger:=
  ∀(N per:ℕ)(z:cells R φ r (f,per))(_q:Basis R d)(i:ℕ)(hi:i<K),
    Option (Sheet R N i (parent R hi.le per (placed R fine z.val)))

private def move {N per i:ℕ}{ξ ψ:Fin n→Site (R.family.side K per)}(ik:i<K)(same:ξ=ψ)
    (record:Option (Sheet R N i (parent R ik.le per ξ))):
    Option (Sheet R N i (parent R ik.le per ψ)):=same ▸ record

def catalogue (ledger:Ledger R d φ r fine):Catalogue R d K:=fun N per ξ q i ik=>
  if h:∃z:cells R φ r (f,per),placed R fine z.val=ξ then
    move R ik h.choose_spec (ledger N per h.choose q i ik)
  else none

private theorem file {N per:ℕ}(ledger:Ledger R d φ r fine)(y z:cells R φ r (f,per))(q:Basis R d)
    (i:ℕ)(ik:i<K)(same:placed R fine y.val=placed R fine z.val):
    move R ik same (ledger N per y q i ik)=ledger N per z q i ik:=by
  have eq:y=z:=by
    apply Subtype.ext
    funext v
    exact (R.family.S.toDepth fine per).embed_injective (congrFun same v)
  subst z
  rfl

theorem seated (ledger:Ledger R d φ r fine)(N per:ℕ)(z:cells R φ r (f,per))(q:Basis R d)
    (i:ℕ)(ik:i<K):
    catalogue R d φ r fine ledger N per (placed R fine z.val) q i ik=ledger N per z q i ik:=by
  have trueAt:∃y:cells R φ r (f,per),placed R fine y.val=placed R fine z.val:=⟨z,rfl⟩
  unfold catalogue
  rw [dif_pos trueAt]
  exact file R d φ r fine ledger trueAt.choose z q i ik trueAt.choose_spec

end YM.Integration.WilsonReceivedChronologicalFixedRoseGridArchive
end
