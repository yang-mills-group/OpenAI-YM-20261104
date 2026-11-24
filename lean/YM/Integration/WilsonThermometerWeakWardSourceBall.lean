import YM.Integration.WilsonThermometerWeakWardLimit

/-! The retimed source may be inked on its own original reporting clock. Only
the actual occupied norm bounds, posted before the regulators, enter its UV
tolerance. The signed comparison is still at finite cutoff on the whole law. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakWardSourceBall
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

open WilsonThermometerWeakWardMoments (funded amount)
open WilsonThermometerWeakWardLimit (ceiling price)
def covered {I:Type} [Fintype I] (d:I→ℕ) (rad:ℕ→ℕ)
    (Xcap Ycap:I→ℝ) (δ:ℝ) {ℓ N:ℕ} (p:ℕ) (live:ℓ≤N):Prop:=
  ∀(z:I→Site ((Rf).side N p))(X:(i:I)→Sight Rf (d i) p)(r:(i:I)→Emblems Rf (d i))
    (x:(i:I)→(Rf).label (d i))(y:(i:I)→Palette Rf (d i)),let Y i:=reading (p:=p) (r i) live (y i)
    (∀i,Enrolled R.makes R.doors cash ℓ N p (d i) (digits R N p (z i)) (X i) (r i)) →
    (∀i,b.step (d i) (N,p) (x i)=b.step (d i) (N,p) (Y i)) →
    (∀i,‖x i‖≤Xcap i) → (∀i,size (y i)≤Ycap i) →
    Avoids (C:=Rf) V rad d z →
    ∀(m:ℕ)(early:m≤ℓ)(v:I→Site ((Rf).side m p)),let T:=center (Rf).S p (early.trans live) 0
    (∀i,z i∈T.margin (v i) (3*span (Rf).S live p)) →
    ∀(J:Type)[Fintype J](loc:J→T.Cell)(watch:J → Config G ((Rf).side N p)→ℂ),
    Injective (Sum.elim v loc) → (∀j,Interior (T.chamber 0) (watch j)) →
    let Z:=exterior T loc watch
    (∀ i,LocalOn (Mark.Outer (rad (d i)) (z i)) Z) → Envelope Z →
    ‖moment ((Rf).beta N p) (fun U=>(∏ i,(Rf).O N p (Y i) (z i) U)*Z U)-
      moment ((Rf).beta N p) (fun U=>(∏ i,(Rf).O N p (x i) (z i) U)*Z U)‖ ≤
      δ*
      ∏ j,T.rootTest ((Rf).beta N p) (watch j)

theorem use {I:Type}[Fintype I](d:I→ℕ)(rad:ℕ→ℕ)(A:I→ℝ)(nn:∀i,0≤A i)
    (Xcap Ycap:I→ℝ)(δ:ℝ){ℓ N p:ℕ}(live:ℓ≤N) (bank:funded R V b d rad A p live)
    (late:(((2:ℕ)^Fintype.card I-1:ℕ):ℝ)*(rate R N*∏i,ceiling R (d i) ℓ (A i) (Xcap i) (Ycap i))≤δ):
    covered R V b d rad Xcap Ycap δ p live:=by
  classical
  intro z X r x y Y enrolled same xBound yBound avoid m early v T placed J _ loc watch apart inside Z away bounded
  have estimate:=bank z X r x y enrolled same avoid m early v placed J loc watch apart inside away bounded
  refine estimate.trans (mul_le_mul_of_nonneg_right (le_trans ?_ late) (Finset.prod_nonneg fun i _=>T.root_nonneg _ _))
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  refine Finset.prod_le_prod (fun i _=>?_) (fun i _=>price R (nn i) (x i) (y i) (xBound i) (yBound i))
  dsimp only [WilsonThermometerWeakWardMoments.amount,WilsonThermometerWeakWardRoster.leaf]
  positivity [nn i,(Rf).S.a_pos ℓ,size_ge (y i)]

include M W portfolio house
theorem original (H:ℕ)(simple:G.Simple)(paid:R2I.RG05Joint.AcrossPanels R.kit)
    (shop:RG05Preconstruction.ReadoutPurchase R.b)(S:Rules G)(W₀:Warehouse G)(μ ε:ℝ)(ep:0<ε)
    (f:Extraction.Order)(hier:(Cells.standard Rf).Hierarchy)(room:CellHyp Rf f):
    ∃rad:ℕ→ℕ,∃E:Fin (H+1)→ℝ,(∀i,0≤E i) ∧
    ∀(I:Type)[Fintype I](d:I→Fin (H+1)),∀ᶠ ℓ:ℕ in atTop,∀(Xcap Ycap:I→ℝ)(δ:ℝ),0<δ →
    ∀ᶠ n:ℕ×ℕ in f.fuse,∃h:ℓ<n.1,(∀a:Fin (H+1),linearFiled R b a f hier ε (E a) h) ∧
      ∀s:Finset I,covered R V b (fun i:s=>(d i).val) rad (fun i=>Xcap i) (fun i=>Ycap i) δ n.2 h.le:=by
  classical
  obtain ⟨rad,E,nn,bank⟩:=WilsonThermometerWeakWardMoments.original R M V W b portfolio house H simple paid shop S W₀ μ ε ep f hier room
  refine ⟨rad,E,nn,fun I _ d=>?_⟩
  obtain ⟨A,nnA,vouchers⟩:=bank I d
  filter_upwards [vouchers] with ℓ issued
  intro Xcap Ycap δ pos
  let C (i:I):=ceiling R (d i) ℓ (A i) (Xcap i) (Ycap i)
  have faded:Tendsto (fun n:ℕ×ℕ=>rate R n.1) f.fuse (𝓝 0):=Real.tendsto_exp_atBot.comp
    (Tendsto.const_mul_atTop_of_neg (by norm_num : -(3/128:ℝ)<0) ((Rf).S.divergent.comp (upper f)))
  have small (s:Finset I):∀ᶠ n:ℕ×ℕ in f.fuse,
      (((2:ℕ)^Fintype.card s-1:ℕ):ℝ)*(rate R n.1*∏i:s,C i)≤δ:=by
    have gone:Tendsto (fun n:ℕ×ℕ=>(((2:ℕ)^Fintype.card s-1:ℕ):ℝ)*(rate R n.1*∏i:s,C i)) f.fuse (𝓝 0):=by
      simpa only [zero_mul,mul_zero] using (faded.mul_const (∏i:s,C i)).const_mul (((2:ℕ)^Fintype.card s-1:ℕ):ℝ)
    exact (gone.eventually_lt_const pos).mono (fun _ h=>h.le)
  filter_upwards [issued,eventually_all.mpr small] with n elected priced
  obtain ⟨h,linear,faces⟩:=elected
  exact ⟨h,linear,fun s=>WilsonThermometerWeakWardSourceBall.use R V b _ rad (fun i:s=>A i) (fun i=>nnA i)
    (fun i=>Xcap i) (fun i=>Ycap i) δ h.le (faces s) (priced s)⟩

end YM.Integration.WilsonThermometerWeakWardSourceBall
end
