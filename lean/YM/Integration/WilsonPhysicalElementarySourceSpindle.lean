import YM.Integration.WilsonPhysicalActualMixedMenus
import YM.Integration.WilsonPositionProgramTrialPublicRawFare

/-! Actual Spindle income of every primitive in the detected public roster. All
directions are registered before the radii; repeating a home leaves its real reporter intact. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Integration.WilsonPhysicalElementarySourceSpindle
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow RG16 RG16.Literal
open Climb OPE Overlay Bid Push.GridApprox RG17 PhysMS EveryPhase OPE.Orbits OPE.Log MS MS.Land FVA2 FVA2.Register
open Next.Rank
open WilsonOriginalTwoFlatPublicFare (charge)
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonMovingForkOpticalBook (reporter)
open WilsonThermometerUnitFilingFourPoolClock (outer)
open WilsonPhysicalActualMixedMenus (Port source)
open WilsonPhysicalVaneBasis (field)
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}
  (F:Final R.family order S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}
variable (J:ℝ→tower S)(Z:WilsonPrescription G){I:Type}[Fintype I][Nonempty I]{D T:ℕ}
  (d:I→Fin (D+1))(x:∀i,RG17.Free R.family (d i).val){δ:ℝ}
  (books:(s:{s:ℝ//0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
local notation "C" => R.family
local notation "β" => R.family.path.levels.clock.hatBeta

abbrev Roster:Type:=(i:I)×((C).labels.level (d i)).Index

def primitive (i:I):(w:Bool)→Port R (d i) w→((C).labels.level (d i)).Index
  | false,_=>0
  | true,e=>e

def address (i:I)(w:Bool)(e:Port R (d i) w):Roster (R:=R) d:=⟨i,primitive d i w e⟩

def vector (s:{s:ℝ//0<s ∧ s<δ})(i:I):(w:Bool)→Port R (d i) w→S.Field (d i)
  | false,_=>WilsonPositionHomogeneousFrame.homogeneous F J Z s.val (d i) (x i)
  | true,e=>(books s).V (d i) (field (C) (d i) e)

theorem issued (s:{s:ℝ//0<s ∧ s<δ})(i:I)(w:Bool)(e:Port R (d i) w)(N p:ℕ):
    source F J Z (d i) (books s) (x i) w e N p=
      (((books s).rows (d i)).arm w (vector F J Z d x books s i w e)).source (N,p):=by
  cases w <;> rfl

theorem reporter_eq (ρ:I→{s:ℝ//0<s ∧ s<δ}):
    reporter F books (fun p:Roster (R:=R) d=>ρ p.1)=reporter F books ρ:=by
  unfold reporter
  congr 1
  apply le_antisymm
  · apply Finset.sup_le
    intro p _
    exact Finset.le_sup (f:=fun i=>max (books (ρ i)).stock.j (books (ρ i)).W.k) (Finset.mem_univ p.1)
  · apply Finset.sup_le
    intro i _
    let p:Roster (R:=R) d:=⟨i,0⟩
    exact Finset.le_sup (f:=fun p:Roster (R:=R) d=>max (books (ρ p.1)).stock.j (books (ρ p.1)).W.k) (Finset.mem_univ p)

private theorem installed (s:{s:ℝ//0<s ∧ s<δ})(i:I)(w:Bool)(e:Port R (d i) w):
    WilsonReflectedMixedMasterSchool.field F J Z D T (fun p:Roster (R:=R) d=>d p.1)
        (fun p=>field (C) (d p.1) p.2) (fun p=>x p.1) books (address d i w e) s false w=
      vector F J Z d x books s i w e:=by
  cases w <;> rfl

theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (lead:Leading F J)(obeys:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (J r) d)(h:ℕ)
    (paid:∀s,WilsonMovingForkWindowBooks.Priced F (books s)):
    ∃A:Roster (R:=R) d→ℝ,∃E:Roster (R:=R) d→ℕ,(∀p,1≤A p) ∧ ∀ᶠr in trail,
      ∀ρ:I→{s:ℝ//0<s ∧ s<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r)→(∃i,(ρ i).val=r)→
      let f:=reporter F books ρ
      ∀(i:I)(w:Bool)(e:Port R (d i) w),∀N p,f<N→
        Motion.orbitCost ((C).labels.level (d i))*
          Spindle.paid (C) (d i) f N p (source F J Z (d i) (books (ρ i)) (x i) w e N p)≤
            A (address d i w e)*(β f)^(E (address d i w e)):=by
  letI : Nonempty (Roster (R:=R) d):=⟨⟨Classical.arbitrary I,0⟩⟩
  let grads:=fun p:Roster (R:=R) d=>d p.1
  let y:=fun p:Roster (R:=R) d=>field (C) (d p.1) p.2
  let xs:=fun p:Roster (R:=R) d=>x p.1
  obtain ⟨A,E,start,all⟩:=WilsonPositionProgramTrialPublicRawFare.original F J Z simple bliss slow lead obeys D T h grads y xs books paid
  refine ⟨A,E,start,?_⟩
  filter_upwards [all] with r compact ρ span born f i w e N p ahead
  let home:=fun p:Roster (R:=R) d=>ρ p.1
  obtain ⟨prior,same⟩:=born
  have obtained:=compact home (fun g=>span g.1) (show ∃g:Roster (R:=R) d,(home g).val=r from ⟨⟨prior,0⟩,same⟩)
    (address d i w e) false w
  have receipt:=WilsonOriginalTwoFlatPublicFare.issued F ((books (ρ i)).rows (d i)) (books (ρ i)).checked w
    (vector F J Z d x books (ρ i) i w e) (p:=p) (WilsonMovingForkOpticalBook.station_le F books ρ i (d i) w) ahead
  rw [issued]
  refine (mul_le_mul_of_nonneg_left receipt (zero_le_one.trans (Motion.orbitCost_one_le _))).trans ?_
  have key:(address (R:=R) d i w e).1=i:=by cases w <;> rfl
  change Motion.orbitCost ((C).labels.level (grads (address d i w e)))*_≤_ at obtained
  dsimp [home,grads,y,xs] at obtained
  simp only [reporter_eq F d books ρ,key,installed] at obtained
  cases w <;> simpa only [f,address] using obtained

end YM.Integration.WilsonPhysicalElementarySourceSpindle
