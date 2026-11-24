import YM.Integration.WilsonPhysicalSignedBornFloor
import YM.Integration.WilsonOriginalPublicEarnedGramWilsonTable

/-! One positive original finite quadratic for the entire named public field space. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalPositiveHome
open Filter Set Function Lattice Wilson RG Source Extraction RG17 Table Spec Climb
open FVA2 FVA2.Register
open Trace.Pilot PhysMS Frame XSpace XSpace.Normalize XSpace.Structure1 Maxwell Maxwell.Wick
open MS MS.Menus MS.Land MS.Theater Local.Physical PhysicalNext.Repeat.Legato
open WilsonOriginalPublicRelativeGramFreePanel (named pointsAt incidence)
open WilsonOriginalPublicRelativeGramLeading (fields)
open WilsonPositionProgramPublicWickGram (reading nodes)
open WilsonPositionProgramPublicContrast (assay)
open WilsonPositionHomogeneousFrame (homogeneous)
open WilsonMacroscopicRichTwoDatePivot (active)
open WilsonOriginalBlissMixedGram (grades)
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}
    (F:Spec.Final R.family f S)(J:ℝ→tower S)(Z:WilsonPrescription G)
    {Y:(Bel R.family.book).Hierarchy} (B:Deck G)(h:ℕ)(a:Axis)

open WilsonOriginalPublicRelativeGramOuterPhysical (truePair)
open WilsonOriginalPublicRelativeGramAddresses (ports shape)
open WilsonOriginalPublicRelativeGramReflectedLimit (entered ordered)
open WilsonOriginalPublicRelativeGramPins (readings matrix)
variable (ℓ:Ultrafilter (ℕ×ℕ))(avoid:Finset E4)



open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonOriginalPublicRelativeGramPins (cutoff)
variable {arch:Trace.Terrace.Arch R.family}

open GapsContact.Seams Trace.Terrace
open WilsonOriginalPublicRelativeGramPins (cutoff matrix readings)

structure Meter {G:Gauge}{d:ℕ}{I:Type}[Fintype I]{B:Local.Physical.Deck G}
    (a:Axis)(legs:I→Glyph B d) where
  k:ℝ
  δ:ℝ
  positive:0<k
  aperture:0<δ
  paid:∀p:I→I→ℂ,‖p-reading a (nodes a) legs‖≤δ → ∀x:I→ℂ,k*‖x‖^2≤(assay x x p).re

def meter {G:Gauge}{d:ℕ}{I:Type}[Fintype I]{B:Local.Physical.Deck G}
    (a:Axis)(legs:I→Glyph B d)(independent:Injective legs):Meter a legs:=
  let s:=WilsonPhysicalSignedBornFloor.original a legs independent
  ⟨s.choose,s.choose_spec.choose,s.choose_spec.choose_spec.1,s.choose_spec.choose_spec.2.1,s.choose_spec.choose_spec.2.2⟩

def appointed {G:Gauge}(B:Local.Physical.Deck G)(d:ℕ)(a:Axis):Meter a (id:Glyph B d→Glyph B d):=
  meter a id injective_id
local notation "I" => Glyph B h
local notation "E" => named R B h

theorem original (simple:G.Simple)(bliss:Bliss F ℓ arch Y)(lead:Leading F J)
    (earned:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d):
    ∃Γ:WilsonViewerReportingGrid.Grid (ℓ:=ℓ) F h (wilson arch),∀ᶠr in trail,∀{height T:ℕ}(cap:h≤height)(book:Book F (l:=ℓ) Y arch height T r)(side:I→Bool),
    ∀ᶠb in (ℓ:Filter (ℕ×ℕ)),∀x:I→ℂ,(appointed B h a).k*‖x‖^2 ≤
      (assay x x (fun i j=>cutoff R a (fun _:I=>h) (Γ.date r)
      (fun _:Unit=>ports R avoid (pointsAt a) (Γ.date r) r) (fun _:Unit=>(1:ℂ))
      (fun _ w j=>((book.rows ⟨h,Nat.lt_succ_of_le cap⟩).arm (side j)
        (homogeneous F J Z r h (E j))).source w) false b i j)).re:=by
  obtain ⟨Γ,bill⟩:=WilsonOriginalPublicEarnedGramWilsonTable.original R F J Z B h a ℓ avoid simple bliss lead earned
  let fee:=appointed B h a
  refine ⟨Γ,?_⟩
  filter_upwards [bill fee.δ fee.aperture] with r price height T cap book side
  filter_upwards [price cap book side] with w near
  exact fee.paid _ near.le

end YM.Integration.WilsonPhysicalPositiveHome
