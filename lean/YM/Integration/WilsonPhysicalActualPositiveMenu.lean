import YM.Integration.WilsonPhysicalActualReflectedMenu

/-! Positive physical reflected report in the actual primitive weak/pooled menu, with its original aperture and extraction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalActualPositiveMenu
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
local notation "I" => Glyph B h
local notation "E" => named R B h

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

open WilsonPhysicalPositiveHome (appointed)
open WilsonPhysicalActualReflectedMenu (bill)
theorem original (simple:G.Simple)(bliss:Bliss F ℓ arch Y)(lead:Leading F J)
    (earned:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d):
    ∃ε:ℝ,0<ε ∧ ∀ᶠr in trail,∀m:ℕ,R.family.S.a m/r<ε → ∀{height T:ℕ}(cap:h≤height)
    (book:Book F (l:=ℓ) Y arch height T r)(side:I→Bool),
    ∀ᶠz in (ℓ:Filter (ℕ×ℕ)),∀x:I→ℂ,(appointed B h a).k*‖x‖^2 ≤
      (assay x x (fun i j=>bill F J Z (fun _:Fin 2=>book) ⟨h,Nat.lt_succ_of_le cap⟩ ![E i,E j] ![side i,side j] a z.1 z.2
        (fun t=>Cells.location R.family.S m z.1 z.2 (ports R avoid (pointsAt a) m r t)))).re:=by
  obtain ⟨ε,ep,allR⟩:=WilsonPhysicalPositiveSameDate.original R F J Z B h a ℓ avoid simple bliss lead earned
  refine ⟨ε,ep,?_⟩
  filter_upwards [allR] with r active m mesh height T cap book side
  filter_upwards [active m mesh cap book side] with z paid x
  let k:Fin (height+1):=⟨h,Nat.lt_succ_of_le cap⟩
  have settled (i j:I):
      cutoff R a (fun _:I=>h) m (fun _:Unit=>ports R avoid (pointsAt a) m r) (fun _:Unit=>(1:ℂ))
        (fun _ w j=>((book.rows k).arm (side j) (homogeneous F J Z r h (E j))).source w) false z i j=
      bill F J Z (fun _:Fin 2=>book) k ![E i,E j] ![side i,side j] a z.1 z.2
        (fun t=>Cells.location R.family.S m z.1 z.2 (ports R avoid (pointsAt a) m r t)):=by
    unfold cutoff
    rw [Fintype.sum_unique,one_mul]
    exact WilsonPhysicalActualReflectedMenu.original F J Z (fun _:Fin 2=>book) k ![E i,E j] ![side i,side j] a z.1 z.2 _
  exact (paid x).trans_eq (congrArg (fun A:I→I→ℂ=>(assay x x A).re) (funext fun i=>funext (settled i)))

end YM.Integration.WilsonPhysicalActualPositiveMenu
