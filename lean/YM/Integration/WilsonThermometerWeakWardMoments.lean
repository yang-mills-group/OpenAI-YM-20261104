import YM.Integration.WilsonThermometerWeakWardRoster
import YM.Integration.WilsonThermometerWeakWardSubwords
import YM.Integration.WilsonThermometerExtractedColumns
import YM.Integration.WilsonThermometerMarchTerminalWatch

/-! Every finite original occupied moment and cleared exterior are measured on the
same regulated Wilson density. The signed substitution uses the complete
projection-null Ward error at every occupied site before the physical limit. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakWardMoments
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
open WilsonThermometerWeakWardRoster (rate leaf returned sound)
open WilsonThermometerWeakLinearReport (linearFiled)
open WilsonThermometerReflectedWatch (exterior)
open Next.Extract
open WilsonThermometerMarchTerminalWatch (upper)

def amount (d ℓ:ℕ) (A:ℝ) (x:(Rf).label d) (y:Palette Rf d):ℝ:=
  (A*(Rf).S.a ℓ^(-(d:ℝ)-1)+1)*(1+‖x‖)+leaf R (ℓ:=ℓ) x y

def funded {I:Type} [Fintype I] (d:I→ℕ) (rad:ℕ→ℕ)
    (A:I→ℝ) {ℓ N:ℕ} (p:ℕ) (live:ℓ≤N):Prop:=
  ∀(z:I→Site ((Rf).side N p))(X:(i:I)→Sight Rf (d i) p)(r:(i:I)→Emblems Rf (d i))
    (x:(i:I)→(Rf).label (d i))(y:(i:I)→Palette Rf (d i)),let Y i:=reading (p:=p) (r i) live (y i)
    (∀i,Enrolled R.makes R.doors cash ℓ N p (d i) (digits R N p (z i)) (X i) (r i)) →
    (∀i,b.step (d i) (N,p) (x i)=b.step (d i) (N,p) (Y i)) →
    Avoids (C:=Rf) V rad d z →
    ∀(m:ℕ)(early:m≤ℓ)(v:I→Site ((Rf).side m p)),let T:=center (Rf).S p (early.trans live) 0
    (∀i,z i∈T.margin (v i) (3*span (Rf).S live p)) →
    ∀(J:Type)[Fintype J](loc:J→T.Cell)(watch:J → Config G ((Rf).side N p)→ℂ),
    Injective (Sum.elim v loc) → (∀j,Interior (T.chamber 0) (watch j)) →
    let Z:=exterior T loc watch
    (∀ i,LocalOn (Mark.Outer (rad (d i)) (z i)) Z) → Envelope Z →
    ‖moment ((Rf).beta N p) (fun U=>(∏ i,(Rf).O N p (Y i) (z i) U)*Z U)-
      moment ((Rf).beta N p) (fun U=>(∏ i,(Rf).O N p (x i) (z i) U)*Z U)‖ ≤
      (((2:ℕ)^Fintype.card I-1:ℕ):ℝ)*(rate R N*∏ i,amount R (d i) ℓ (A i) (x i) (y i))*
      ∏ j,T.rootTest ((Rf).beta N p) (watch j)

theorem examine {I:Type}[Fintype I](d:I→ℕ)(rad:ℕ→ℕ)(A:I→ℝ)(nn:∀i,0≤A i)
    {ℓ N p:ℕ}(live:ℓ≤N) (clock:0≤(Rf).S.scale N) (arms:∀i,returned R V P (d i) live) (erased:sound R V P b rad d live)
    (stock:∀(i:I)(m:ℕ)(early:m≤ℓ)(v:Site ((Rf).side m p))(o:Site ((Rf).side N p))(x:(Rf).label (d i)),
      let T:=center (Rf).S p (early.trans live) 0
      o∈T.margin v (3*span (Rf).S live p) → ∃ F,Interior (T.chamber 0) F ∧
        T.rootTest ((Rf).beta N p) F ≤ (A i*(Rf).S.a ℓ^(-(d i:ℝ)-1)+1)*(1+‖x‖) ∧ T.copy v F=(Rf).O N p x o):
    funded R V b d rad A p live:=by
  classical
  intro z X r x y Y offered same sep m early v T margin J _ loc watch distinct housed Z away bounded
  choose F regular gross present using fun i=>stock i m early (v i) (z i) (x i) (margin i)
  choose D edited small read using fun i=>arms i p (z i) (X i) (r i) (offered i) (x i) (y i) m early (v i) (margin i)
  let M i:=amount R (d i) ℓ (A i) (x i) (y i)
  have std (i:I):T.rootTest ((Rf).beta N p) (F i)≤M i := (gross i).trans (le_add_of_nonneg_right (by
    dsimp only [WilsonThermometerWeakWardRoster.leaf];positivity [size_ge (y i)]))
  have positive (i:I):0≤M i:=(T.root_nonneg ((Rf).beta N p) _).trans (std i)
  have priced (i:I):T.rootTest ((Rf).beta N p) (D i)≤rate R N*M i:=by
    have a:0≤(A i*(Rf).S.a ℓ^(-(d i:ℝ)-1)+1)*(1+‖x i‖):=by positivity [nn i,(Rf).S.a_pos ℓ]
    calc
      _ ≤ leaf R (ℓ:=ℓ) (x i) (y i)*rate R N := small i
      _ ≤ M i*rate R N:=mul_le_mul_of_nonneg_right (le_add_of_nonneg_left a) (Real.exp_pos _).le
      _ = _:=mul_comm ..
  have loss:rate R N≤1:=Real.exp_le_one_iff.mpr (by nlinarith : -(3/128:ℝ)*(Rf).S.scale N≤0)
  have estimate:=WilsonThermometerWeakWardSubwords.original T v loc F D watch ((Rf).beta N p)
    (seamless R.makes N p) distinct regular edited housed positive loss std priced
  have fcopy (i:I):T.copy (v i) (F i)=(Rf).O N p (x i) (z i):=present i
  have dcopy (i:I):T.copy (v i) (D i)=residual Rf (V (d i)) N p (P (d i) (N,p)) (x i-Y i) (z i):=read i
  rw [erased p z r x y same sep Z away bounded]
  simpa only [fcopy,dcopy,Y,M,Z] using! estimate

include M W portfolio house
theorem original (H:ℕ) (simple:G.Simple) (paid:R2I.RG05Joint.AcrossPanels R.kit)
    (shop:RG05Preconstruction.ReadoutPurchase R.b) (S:Rules G) (W₀:Warehouse G)
    (μ ε:ℝ) (pos:0<ε) (f:Extraction.Order) (hier:(Cells.standard Rf).Hierarchy) (room:CellHyp Rf f):
    ∃ rad:ℕ→ℕ,∃ E:Fin (H+1)→ℝ,(∀a,0≤E a) ∧
    ∀(I:Type)[Fintype I](d:I→Fin (H+1)),∃A:I→ℝ,(∀i,0≤A i) ∧
    ∀ᶠ ℓ:ℕ in atTop,∀ᶠ n:ℕ×ℕ in f.fuse,∃live:ℓ<n.1,
      (∀a:Fin (H+1),linearFiled R b a f hier ε (E a) live) ∧
      ∀t:Finset I, funded R V b (fun i:t=>(d i).val) rad (fun i=>A i) n.2 live.le:=by
  classical
  obtain ⟨rad,ward⟩:=WilsonThermometerWeakWardRoster.original R V W b portfolio house simple
  obtain ⟨E,nnE,report⟩:=WilsonThermometerWeakLinearReport.original R M V W b portfolio house H simple paid shop S W₀ μ ε pos f hier
  refine ⟨rad,E,nnE,fun I _ d=>?_⟩
  choose start A nn stock using fun i:I=>WilsonThermometerExtractedColumns.original R.makes room (d i).val
  refine ⟨A,nn,?_⟩
  filter_upwards [report,ward I (fun i=>(d i).val),eventually_all.mpr (fun i:I=>eventually_ge_atTop (start i))] with ℓ legal paid earlier
  filter_upwards [(upper f).eventually legal,(upper f).eventually paid,eventually_all.mpr (fun i:I=>stock i ℓ (earlier i)),(upper f).eventually ((Rf).S.divergent.eventually_ge_atTop 0)] with n returned income raw clock
  obtain ⟨live,linear⟩:=returned
  obtain ⟨_,arms,erased⟩:=income
  refine ⟨live,linear,fun t=>examine R V b (fun i:t=>(d i).val) rad (fun i=>A i) (fun i=>nn i) live.le clock
      (fun i=>arms i) (erased t) ?_⟩
  intro i
  exact (raw i.val).choose_spec

end YM.Integration.WilsonThermometerWeakWardMoments
end
