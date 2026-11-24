import YM.Integration.WilsonPhysicalActualMixedMenus
import YM.Integration.WilsonPhysicalPositiveSameDate

/-! The actual adjoint and actual right field in the elected finite reflected Gram,
resolved on their own booked weak directions or on their unchanged pooled arms. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalActualReflectedMenu
open Function Filter Finset MeasureTheory Lattice RG Wilson Source Labels Extra.Histories
open Table Climb Spec PhysicalNext.Repeat.Legato Trace.Target Trace.Pilot
open OPE Next.Extract RG.Supply MS MS.Land FVA2 FVA2.Register PhysMS
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonReflectedPublicOrientedFaces (displayed)
open WilsonPhysicalActualMixedMenus (name source Choices multiplier)
open WilsonPhysicalActualWeakCylinders (product)
open WilsonOriginalBlissMixedGram (columns grades)
open scoped Classical BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}{l:Ultrafilter (ℕ×ℕ)}
variable (F:Final R.family f S)(J:ℝ→tower S)(Z:WilsonPrescription G)
  {H:(Bel R.family.book).Hierarchy}{arch:Trace.Terrace.Arch R.family}{D T:ℕ}
local notation "C" => R.family
variable {ρ:Fin 2→ℝ}(books:(i:Fin 2)→Book F (l:=l) H arch D T (ρ i))
  (d:Fin (D+1))(v:Fin 2→(Bel R.family.book).Field d)(weak:Fin 2→Bool)(a:Axis)

def turns:Fin 2→Motion:=![(Signed.mirror a,true),(1,false)]

def bill (N p:ℕ)(sites:Fin 2→Site ((C).side N p)):ℂ:=
  ∑e:Choices (R:=R) (fun _:Fin 2=>d) weak,
    multiplier F J Z books (fun _:Fin 2=>d) v weak (turns a) e *
      (C).omega N p (product (fun _:Fin 2=>d) (turns a) N p sites
        (fun i=>source F J Z d (books i) (v i) (weak i) (e i) N p))

private theorem right (h:ℕ)(x:(C).label h):displayed R h x (1,false)=x:=by
  simp [displayed,show (1:Signed).ortho=1 from map_one Signed.inclusionO]

theorem original (N p:ℕ)(sites:Fin 2→Site ((C).side N p)):
    (C).ensemble (grades d d) sites (columns R a d d (name F J Z d (books 0) (v 0) (weak 0) N p)
        (name F J Z d (books 1) (v 1) (weak 1) N p))=bill F J Z books d v weak a N p sites:=by
  calc
    _ = (C).omega N p (product (fun _:Fin 2=>d) (turns a) N p sites
        (fun i=>name F J Z d (books i) (v i) (weak i) N p)):=by
      apply congrArg ((C).omega N p)
      funext U
      change (∏i:Fin 2,(C).O N p (d:=grades d d i)
        (columns R a d d (name F J Z d (books 0) (v 0) (weak 0) N p)
        (name F J Z d (books 1) (v 1) (weak 1) N p) i) (sites i) U)=_
      simp only [product,Fin.prod_univ_two]
      change _=_*(C).O N p (displayed R d _ (1,false)) (sites 1) U
      rw [right]
      rfl
    _ = bill F J Z books d v weak a N p sites:=by
      unfold bill
      convert! WilsonPhysicalActualMixedMenus.original F J Z books (fun _:Fin 2=>d) v weak (turns a) N p sites using 6

end YM.Integration.WilsonPhysicalActualReflectedMenu
