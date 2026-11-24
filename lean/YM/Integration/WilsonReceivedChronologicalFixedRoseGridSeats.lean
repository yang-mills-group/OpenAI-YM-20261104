import YM.Integration.WilsonMovingForkStencilCatalogue
import YM.Integration.WilsonReceivedChronologicalFixedRoseVariation
import YM.Integration.WilsonReceivedChronologicalMaterialCapture

/-! A single catalogue retains the actual earlier sheet on each occupied physical cell and grade. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalFixedRoseGridSeats
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

abbrev Rows:=∀(_N per:ℕ),cells R φ r (f,per)→Basis R d→(i:ℕ)→
  Config G (R.family.side i per)→Marker.Poly (Stock.census (Fin n))

private theorem unique {per:ℕ}{u v:cells R φ r (f,per)}(same:placed R fine u.val=placed R fine v.val):u=v:=by
  apply Subtype.ext
  funext i
  exact (R.family.S.toDepth fine per).embed_injective (congrFun same i)

def Eligible (rows:Rows (f:=f) R d φ r)(per:ℕ):Prop:=
  ∀(N:ℕ),K≤N→∀(z:cells R φ r (f,per))(q:Basis R d)(a:↥(Ico first (K-1))),
  let atAge:=parent R (by have live:=mem_Ico.mp a.property;omega:a.val+1≤K) per (placed R fine z.val)
  ∃H:Sheet R N (a.val+1) atAge,Received H (rows N per z q (a.val+1))

def Occupied (rows:Rows (f:=f) R d φ r)(book:Catalogue R d K)(per:ℕ):Prop:=
  ∀(N:ℕ),K≤N→∀(z:cells R φ r (f,per))(q:Basis R d)(a:↥(Ico first (K-1))),
  let atAge:=parent R (by have live:=mem_Ico.mp a.property;omega:a.val+1≤K) per (placed R fine z.val)
  ∃H:Sheet R N (a.val+1) atAge,
    book N per (placed R fine z.val) q (a.val+1) (by have live:=mem_Ico.mp a.property;omega)=some H ∧
    Received H (rows N per z q (a.val+1))

theorem original (rows:Rows (f:=f) R d φ r)
    (paid:∀ᶠper:ℕ in atTop, Eligible (first:=first) R d φ r fine rows per):
    ∃book:Catalogue R d K,∀ᶠper:ℕ in atTop,Occupied (first:=first) R d φ r fine rows book per:=by
  let entry (N per:ℕ)(ξ:Fin n→Site (R.family.side K per))(q:Basis R d)(i:ℕ)(hi:i<K):Prop:=
    ∃H:Sheet R N i (parent R hi.le per ξ),
      K≤N ∧ Nat.lt first i ∧ ∃z:cells R φ r (f,per),placed R fine z.val=ξ ∧ Received H (rows N per z q i)
  let book:Catalogue R d K:=fun N per ξ q i hi=>
    if h:entry N per ξ q i hi then some h.choose else none
  refine ⟨book,?_⟩
  filter_upwards [paid] with per admitted
  intro N kn z q a atAge
  have range:=mem_Ico.mp a.property
  have ik:a.val+1<K:=by omega
  obtain ⟨H,received⟩:=admitted N kn z q a
  have event:entry N per (placed R fine z.val) q (a.val+1) ik:=
    ⟨H,kn,Nat.lt_succ_of_le range.1,z,rfl,received⟩
  obtain ⟨_,_,y,same,booked⟩:=event.choose_spec
  have yz:y=z:=unique R φ r fine same
  refine ⟨event.choose,dif_pos event,?_⟩
  simpa only [yz] using booked

end YM.Integration.WilsonReceivedChronologicalFixedRoseGridSeats
end
