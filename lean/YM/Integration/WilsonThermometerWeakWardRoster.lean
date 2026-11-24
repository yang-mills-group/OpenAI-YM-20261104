import YM.Integration.WilsonThermometerWeakLinearReport
import YM.Integration.WilsonThermometerWeakWardPair

/-! The cutoff Ward remainder at each original displaced site on its own funded
program. Every proper face and its measurable exterior use the same physical law. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakWardRoster
open Function Filter Set Lattice RG Wilson Spec Extraction Cells
open YM.Integration.WilsonLimitConstruction
open PhysicalNext.Repeat.Legato Next.Rank Next.Rank.Tapes.West Next.Rank.East
open PhysicalNext.RankCovariance MergeProof.East Trace.Over
open scoped Topology Classical

open PhysicalNext PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft
open Lattice Wilson Pressure RG Next.Rank Next.Rank.Perch Tapes Peak Flux Marker Ac Corona Value Precision RankCovariance Org Input
     Display Display.Docking Filter RG.Supply Next.Rank.Ship Next.Rank.Station Next.Rank.Spindle
open Function Filter Set Metric Source RG12 Extra.Histories RG05Readout Native Address Many Records Harvest Push.GridApprox Cells Extraction
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open Trace.Physical Push.Local GermGraph Next.Rank.Tapes.West Configuration Normal Rise
open Paint Thirst Relation Perch Glimmer LiftMark Beamer Station Atlas Tariffs Ribbon
open Edition Peak Value Marker Corona Alarm Next.Rank.Glyph
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetField
open WilsonAddressedWeakCalibration WilsonAddressedWeakReflectedHearing WilsonThermometerReflectedTrajectory
open FVA2 FVA2.ColorCode Pert.Position MS MS.Land MS.Menus MS.Rake MS.Tone PhysMS
open Trace Trace.Pilot WilsonAddressedWeakCorrectedCylinder WilsonAddressedWeakPointCells WilsonAddressedWeakMaxwellPositions
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
variable {G:Gauge} (R:Run G) {d H:ℕ}
local notation "Rf" => R.family
local notation "Lev" => R.family.path.levels
local notation "cash" => WilsonThermometerOffsetLedger.cash R

variable {C:Local.Physical.Deck G} {O₀:Booked C} (M:MS_Data G O₀)

open WilsonThermometerWeakPanelBorn WilsonThermometerSmallPanelRead
open WilsonThermometerWeakJointWidth WilsonPositionThermometerStationNorm
open WilsonAddressedWeakFixedChild WilsonAddressedWeakCalibration

open WilsonThermometerWeakWardRows (inverseBill)
open WilsonThermometerOwnOffsetField Push Trace.Pilot Next.Extract MergeProof
variable (V:∀d,Source.SectionData (R.family.labels.level d)) (W:Mark.Weave G)
    {P:∀d,(ℕ×ℕ)→(R.family.label d≃ₗ[ℂ]R.family.label d)} (b:Presentation R.family)
    (portfolio:∀d,Mark.Portfolio R.family.params (V d) (W d))
    (house:Hearthside R.family V W P b (PhysicalNext.Repeat.Legato.Bandage.fly R.alloy.B.a))

open WilsonCapturedPrimaryWardRetimed (reading)

open WilsonOffsetReportingProducts WilsonThermometerWeakEquationCost
open MeasureTheory XSpace XSpace.Rose Labels OPE OPE.Orbits WilsonOffsetEquationLaw
def rate (N:ℕ):ℝ:=Real.exp (-(3/128:ℝ)*(Rf).S.scale N)
def leaf {ℓ d:ℕ} (x:(Rf).label d) (y:Palette Rf d):ℝ:=
  2*((Fintype.card ((Rf).labels.level d).Index:ℝ)*‖x‖+‖((Rf).S.a ℓ:ℂ)^d‖*size y)

def returned (P:∀d,(ℕ×ℕ)→((Rf).label d≃ₗ[ℂ](Rf).label d)) (d:ℕ) {ℓ N:ℕ} (h:ℓ≤N) :Prop:=
  ∀(p:ℕ)(z:Site ((Rf).side N p))(X:Sight Rf d p)(r:Emblems Rf d),
  Enrolled R.makes R.doors cash ℓ N p d (digits R N p z) X r →
  ∀(x:(Rf).label d)(y:Palette Rf d)(m:ℕ)(early:m≤ℓ)(v:Site ((Rf).side m p)),
    let T:=center (Rf).S p (early.trans h) 0
    z∈T.margin v (3*span (Rf).S h p) → ∃ D:Config G ((Rf).side N p)→ℂ,
      Interior (T.chamber 0) D ∧ T.rootTest ((Rf).beta N p) D ≤ leaf R (ℓ:=ℓ) x y * rate R N ∧
      T.copy v D=residual Rf (V d) N p (P d (N,p)) (x-reading (p:=p) r h y) z

include W b portfolio house in
theorem single (d:ℕ) (simple:G.Simple):
    ∀ᶠ ℓ:ℕ in atTop,∀ᶠ N:ℕ in atTop,∃h:ℓ≤N,returned R V P d h:=by
  filter_upwards [WilsonThermometerRelativeWard.paid R V W P b portfolio house simple d,
    WilsonThermometerWeakEquationCost.original R P house d (1/128) (by norm_num)] with ℓ cells charges
  filter_upwards [cells,charges] with N native priced
  obtain ⟨h,inspected⟩:=native
  refine ⟨h,?_⟩
  intro p z X r admitted x y m early v T inside
  let a:ℂ:=((Rf).S.a ℓ:ℂ)^d
  let q:=reading (p:=p) r h y
  have col:column R (p:=p) r h (a • y)=q:=by
    simp only [WilsonThermometerWeakEquationCost.column,q,WilsonCapturedPrimaryWardRetimed.reading,a,map_smul,Pi.smul_apply]
    exact ((Rf).factory d N p).terminal.map_smul _ _
  have amt:=priced p h (digits R N p z) cash X r admitted x (a • y)
  rw [col,size_smul] at amt
  obtain ⟨D,valid,fare,placed⟩:=inspected p x q early v z inside
  refine ⟨D,valid,fare.trans ?_,placed⟩
  calc
    _ ≤ (leaf R (ℓ:=ℓ) x y * Real.exp ((1/128:ℝ)*(Rf).S.scale N)) *
        Real.exp (-(1/32:ℝ)*(Rf).S.scale N):=mul_le_mul_of_nonneg_right amt (Real.exp_pos _).le
    _ = _ :=by rw [mul_assoc,←Real.exp_add];dsimp only [rate];congr 2;ring

def sound {I:Type} [Fintype I] (P:∀d,(ℕ×ℕ)→((Rf).label d≃ₗ[ℂ](Rf).label d))
    (b:Presentation Rf) (rad:ℕ→ℕ) (d:I→ℕ) {ℓ N:ℕ} (h:ℓ≤N):Prop:=
  ∀(p:ℕ)(z:I→Site ((Rf).side N p))(r:(i:I)→Emblems Rf (d i))(x:(i:I)→(Rf).label (d i))
    (y:(i:I)→Palette Rf (d i)),let q i:=reading (p:=p) (r i) h (y i)
    (∀i,b.step (d i) (N,p) (x i)=b.step (d i) (N,p) (q i)) →
    Avoids (C:=Rf) V rad d z → ∀Z:Config G ((Rf).side N p)→ℂ,
       (∀i,LocalOn (Mark.Outer (rad (d i)) (z i)) Z) → Envelope Z →
      moment ((Rf).beta N p) (fun U=>(∏ i,(Rf).O N p (q i) (z i) U)*Z U)=
      moment ((Rf).beta N p) (fun U=>(∏ i,((Rf).O N p (x i) (z i) U-
        residual Rf (V (d i)) N p (P (d i) (N,p)) (x i-q i) (z i) U))*Z U)

include W portfolio house
theorem original (simple:G.Simple):∃ rad:ℕ→ℕ,
    ∀(I:Type)[Fintype I](d:I→ℕ),∀ᶠ ℓ:ℕ in atTop,∀ᶠ N:ℕ in atTop,∃h:ℓ≤N,
      (∀i,returned R V P (d i) h) ∧ ∀s:Finset I,sound R V P b rad (fun i:s=>d i) h:=by
  classical
  obtain ⟨rad,erase⟩:=WilsonThermometerRelativeWard.original R V W P b portfolio house
  refine ⟨rad,fun I _ d=>?_⟩
  filter_upwards [eventually_all.mpr (fun i:I=>single R V W b portfolio house (d i) simple)] with ℓ priced
  filter_upwards [eventually_all.mpr priced,eventually_ge_atTop ℓ,
    eventually_all.mpr (fun s:Finset I=>erase s (fun i=>d i.val))] with N ready h heard
  refine ⟨h,fun i=>(ready i).choose_spec,?_⟩
  intro s p z r x y q same away Z dist bounded
  exact heard s p x q z Z same away dist bounded

end YM.Integration.WilsonThermometerWeakWardRoster
end
