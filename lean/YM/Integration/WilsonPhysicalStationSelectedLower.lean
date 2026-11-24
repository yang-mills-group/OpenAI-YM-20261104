import YM.Integration.WilsonPhysicalStationUniformLower
import YM.Integration.WilsonPhysicalStationReferenceSalary
import YM.Integration.WilsonPhysicalStationDetectorCurrency
import YM.Integration.WilsonPhysicalStationLowerImage

/-! The unique lower subtraction for an already appointed source is chosen
before the full detector table and persists in the true physical filtration. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationSelectedLower
open Function Filter Finset Lattice RG Wilson Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus MergeProof Matric Gram
open PhysicalNext.Repeat.Legato Bandage Campaign
open Next.Foundations OPE Work.G08
open Next.Rank Next.Rank.East Next.Rank.Price MergeProof.East
open Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress
open Trace.Physical.GermGraph
open WilsonPhysicalStationFactoryGerm (incoming)
open WilsonPhysicalStationRawReading (err eng)
open WilsonPhysicalStationFineCorrection (measured)
open WilsonPhysicalStationRegisteredDiagonal (ratio ceiling)
open WilsonPhysicalStationRegisteredFiling (rate)
open WilsonPhysicalStationThermalStart (entered)
open WilsonPhysicalStationThermalCoordinates (filed)
open WilsonPhysicalStationEndCurrency (row charge)
open WilsonPhysicalStationRestoredEntry (signal)
open WilsonPhysicalStationWeightedAxis (purse)
open WilsonPhysicalStationDatedSalary (span datedMass)
open scoped BigOperators Classical Topology

variable {G:Gauge} (R:Run G) {T:Campaign R} (L:Pillars R T) {f:Extraction.Order} {S:Table R.family.book}
  (fac:Facilities R.family f S) {H:(Bel R.family.book).Hierarchy}
  {D D':ℕ} (A:Vane R.family D) (B:Vane R.family D') {N p:ℕ}
  (h e:ℕ) (da:h   <   D+1) (db:h   <   D'+1)
local notation "a₀" => (⟨h,da⟩:Fin (D+1))
local notation "b₀" => (⟨h,db⟩:Fin (D'+1))
local notation "L₀" => R.family.path.levels
local notation "F₀" => R.family.labels.level h
local notation "μ" => (F₀).coeffSize
local notation "P₀" => Columns.low (F₀) e
local notation "K₀" => R.family.factory h N p
local notation "C₀" => ((L₀).params A.k).columns
local notation "C₁" => ((L₀).params B.k).columns
local notation "δ₀" => barunit (R.family.S.block A.k)
local notation "D₀" => (F₀).scaled (ratio R A.k)

local notation "M₀" => Station.mag (L₀) A.b A.k
local notation "M₁" => Station.mag (L₀) B.b B.k


local notation "t₀" => (shrink R.family A.k N p)⁻¹
local notation "t₁" => (shrink R.family B.k N p)⁻¹



include fac in
theorem unique (ca:A.checked f H D) (top:A.k < N) (earlier:e < h)
    (gate:(C₀)*err R A.k ≤ 1/2)(y u v:R.family.label h)
    (hu:(P₀) u=u)(hv:(P₀) v=v)
    (uc:(P₀) (A.R N p (a₀) (y-(K₀).terminal u))=0)
    (vc:(P₀) (A.R N p (a₀) (y-(K₀).terminal v))=0):u=v:=by
  let diff:=u-v
  have fixed:(P₀) diff=diff:=by dsimp [diff];rw [map_sub,hu,hv]
  have adjust:(P₀) ((A.R N p (a₀)) ((K₀).terminal diff))=0:=by
    have eq:((K₀).terminal diff)=(y-(K₀).terminal v)-(y-(K₀).terminal u):=by
      dsimp [diff];rw [map_sub];abel
    rw [eq,map_sub,map_sub,uc,vc,sub_self]
  have blank:(P₀) (WilsonPhysicalStationFiledSlope.testing R A (a₀) N p diff)=0:=by
    change (P₀) (eng R h A.k • (A.R N p (a₀)) ((K₀).terminal diff))=0
    rw [map_smul,adjust,smul_zero]
  have stock:=WilsonPhysicalStationFiledSlope.original R fac A (a₀) e (p:=p) ca top earlier gate diff fixed
  rw [blank] at stock
  have no:Columns.trace R.family h N p A.k diff=0:=by
    apply size_separates (F₀)
    simpa [Frame.coeffSize] using stock
  have dated:datedMass R h N p ((K₀).terminal diff) A.k=0:=by
    change μ (((K₀).entries A.k ((K₀).terminal.symm ((K₀).terminal diff))).x)=0
    rw [LinearEquiv.symm_apply_apply]
    change μ (Columns.trace R.family h N p A.k diff)=0
    rw [no];simp [Frame.coeffSize]
  have bare:=WilsonPhysicalStationReferenceSalary.original R h A.k N p ((K₀).terminal diff)
    (ca.early (a₀)) top.le
  rw [dated,mul_zero,norm_le_zero_iff] at bare
  have equal:(K₀).terminal u=(K₀).terminal v:=sub_eq_zero.mp (by simpa [diff] using bare)
  exact (K₀).terminal.injective equal

structure Receipt (ca:A.checked f H D) (cb:B.checked f H D')
    (top:B.k < N) (a:(F₀).Index)(W:R.family.label h):Prop where
  lower:(P₀) W=W
  clear:(P₀) (A.R N p (a₀)
    (entered R B (b₀) (p:=p) cb top (Pi.single a 1)-(K₀).terminal W))=0
  coefficients :
    let q:=((F₀).grades a).2
    let s:R.family.label h:=Pi.single a 1
    let y:=entered R B (b₀) (p:=p) cb top s
    ∀ i,(1-err R B.k)*‖filed R A (a₀) N p (y-(K₀).terminal W) i-
      (signal R N p A.k B.k h q (M₀) (M₁):ℂ)*s i‖*(t₀)^((F₀).grades i).2 ≤ 
      rate R A.k B.k h*purse R N p A.k B.k h q (M₀) (M₁)
  reference: ‖(K₀).terminal W‖ ≤ WilsonPhysicalStationUniformLower.allowance R A.k B.k h ((F₀).grades a).2 (M₀) (M₁)

include L fac in
theorem original (hg:G.Simple) (ca:A.checked f H D) (cb:B.checked f H D')
    (dates:B.k=A.k+1) (top:B.k < N) (horizon:h=e+1)
    (gate:(C₀)*err R A.k ≤ 1/2)(next:(C₁)*err R B.k ≤ 1/2)
    (a:(F₀).Index)(weight:((F₀).grades a).1=h):
    ∃! W:R.family.label h, Receipt R A B h e da db (p:=p) ca cb top a W:=by
  obtain ⟨W,lower,clear,prices⟩:=WilsonPhysicalStationWeightedAxis.original R L fac A B h e da db
    (p:=p) hg ca cb dates top horizon gate a weight
  have bound:=WilsonPhysicalStationUniformLower.original R A B h e da db (p:=p) ca cb dates top horizon
    gate next a weight W clear prices
  refine ⟨W,⟨lower,clear,prices,bound⟩,?_⟩
  intro z hz
  exact unique R fac A h e da (p:=p) ca (by omega) (by omega) gate _ z W hz.lower lower hz.clear clear

end YM.Integration.WilsonPhysicalStationSelectedLower
end
