import YM.Integration.WilsonThermometerWeakWardMoments
import YM.Integration.WilsonThermometerReferenceStation

/-! Uniform loss on every bounded ball of true reporting fields and all
occupied subwords, with the complete reflected exterior retained. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakWardLimit
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

open WilsonThermometerWeakWardMoments (amount)
private theorem normPaid {a:ℕ} (x:(Rf).label a) : ‖x‖≤((Rf).labels.level a).coeffSize x:=by
  exact (pi_norm_le_iff_of_nonneg (Work.G08.size_nonneg _ _)).mpr
    fun j=>Finset.single_le_sum (fun _ _=>norm_nonneg _) (Finset.mem_univ j)

def ceiling (d ℓ:ℕ) (A X Y:ℝ):ℝ:=(A*(Rf).S.a ℓ^(-(d:ℝ)-1)+1)*(1+X)+
  2*((Fintype.card ((Rf).labels.level d).Index:ℝ)*X+‖((Rf).S.a ℓ:ℂ)^d‖*Y)

theorem price {a ℓ:ℕ}{A X Y:ℝ} (pos:0≤A) (x:(Rf).label a) (y:Palette Rf a)
    (hx:‖x‖≤X)(hy:size y≤Y):
    amount R a ℓ A x y≤ceiling R a ℓ A X Y:=by
  dsimp only [WilsonThermometerWeakWardMoments.amount,ceiling,WilsonThermometerWeakWardRoster.leaf]
  have base:0≤A*(Rf).S.a ℓ^(-(a:ℝ)-1)+1:=by positivity [(Rf).S.a_pos ℓ]
  apply add_le_add (mul_le_mul_of_nonneg_left (add_le_add (le_refl (1:ℝ)) hx) base)
  exact mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg _))
    (mul_le_mul_of_nonneg_left hy (norm_nonneg _))) (by norm_num)

def measured {I:Type}[Fintype I] (H:ℕ) (d:I→Fin (H+1))(ε:ℝ)(E:Fin (H+1)→ℝ)
    (f:Extraction.Order)(hier:(Cells.standard Rf).Hierarchy)(rad:ℕ→ℕ){ℓ N p:ℕ}(h:ℓ<N)(B δ:ℝ):Prop:=
  ∀(z:I→Site ((Rf).side N p))(X:(i:I)→Sight Rf (d i) p)(r:(i:I)→Emblems Rf (d i)),
    (∀i,Enrolled R.makes R.doors cash ℓ N p (d i) (digits R N p (z i)) (X i) (r i)) →
    ∀T:I→Vane Rf H,(∀i,(T i).k=ℓ) → (∀i,(T i).checked f hier H) →
    ∃L:(i:I)→(Cells.standard Rf).Field (d i) →ₗ[ℂ] Palette Rf (d i),
      (∀i v,b.step (d i) (N,p) (reading (p:=p) (r i) h.le (L i v))=
        b.step (d i) (N,p) ((T i).wheel.atCut (N,p) (d i) v) ∧
        size (L i v)≤E (d i)*((Lev).clock.hatBeta ℓ)^ε*(cost Rf (d i)*‖v‖)) ∧
      ∀(s:Finset I)(w:(i:s)→(Cells.standard Rf).Field (d i)),(∀i,‖w i‖≤B) →
      Avoids (C:=Rf) V rad (fun i:s=>(d i).val) (fun i=>z i) →
      ∀(m:ℕ)(early:m≤ℓ)(v:s→Site ((Rf).side m p)),let U:=center (Rf).S p (early.trans h.le) 0
      (∀i:s,z i∈U.margin (v i) (3*span (Rf).S h.le p)) →
      ∀(J:Type)[Fintype J](loc:J→U.Cell)(watch:J → Config G ((Rf).side N p)→ℂ),
      Injective (Sum.elim v loc) → (∀j,Interior (U.chamber 0) (watch j)) →
      let Z:=exterior U loc watch
      (∀i:s,LocalOn (Mark.Outer (rad (d i)) (z i)) Z) → Envelope Z →
      ‖moment ((Rf).beta N p) (fun g=>(∏i:s,(Rf).O N p (reading (p:=p) (r i) h.le (L i (w i))) (z i) g)*Z g)-
       moment ((Rf).beta N p) (fun g=>(∏i:s,(Rf).O N p ((T i).wheel.atCut (N,p) (d i) (w i)) (z i) g)*Z g)‖ ≤
      δ*∏j,U.rootTest ((Rf).beta N p) (watch j)

include M W portfolio house
theorem original (H:ℕ)(simple:G.Simple)(paid:R2I.RG05Joint.AcrossPanels R.kit)
    (shop:RG05Preconstruction.ReadoutPurchase R.b)(S:Rules G)(W₀:Warehouse G)(μ ε:ℝ)(ep:0<ε)
    (f:Extraction.Order)(hier:(Cells.standard Rf).Hierarchy)(room:CellHyp Rf f):
    ∃rad:ℕ→ℕ,∃E:Fin (H+1)→ℝ,(∀i,0≤E i) ∧
    ∀(I:Type)[Fintype I](d:I→Fin (H+1)),∀ᶠ ℓ:ℕ in atTop,∀B:ℝ,0≤B → ∀δ:ℝ,0<δ →
    ∀ᶠ n:ℕ×ℕ in f.fuse,∃h:ℓ<n.1,measured R V b H d ε E f hier rad (p:=n.2) h B δ:=by
  classical
  obtain ⟨rad,E,nn,bank⟩:=WilsonThermometerWeakWardMoments.original R M V W b portfolio house H simple paid shop S W₀ μ ε ep f hier room
  refine ⟨rad,E,nn,fun I _ d=>?_⟩
  obtain ⟨A,nnA,vouchers⟩:=bank I d
  filter_upwards [vouchers,eventually_all.mpr (fun i:I=>WilsonThermometerReferenceStation.cutoff
    (C:=Rf) (f:=f) (H:=hier) simple R.makes (d i).val ε ep)] with ℓ issued fits
  intro B bp δ dp
  let g:=((Lev).clock.hatBeta ℓ)^ε
  let boundX (i:I):=Real.exp (Work.D01.columnLogs (Lev) ℓ)*(g*(cost Rf (d i)*B))
  let boundY (i:I):=E (d i)*g*(cost Rf (d i)*B)
  let C (i:I):=ceiling R (d i) ℓ (A i) (boundX i) (boundY i)
  have hc (i:I):0≤cost Rf (d i):=by dsimp only [cost];positivity
  have gb:0≤g:=Real.rpow_nonneg (zero_le_one.trans ((Lev).fits.delayed ℓ).le) _
  have faded:Tendsto (fun n:ℕ×ℕ=>rate R n.1) f.fuse (𝓝 0):=Real.tendsto_exp_atBot.comp
    (Tendsto.const_mul_atTop_of_neg (by norm_num : -(3/128:ℝ)<0) ((Rf).S.divergent.comp (upper f)))
  have small (s:Finset I):∀ᶠ n:ℕ×ℕ in f.fuse,
      (((2:ℕ)^Fintype.card s-1:ℕ):ℝ)*(rate R n.1*∏i:s,C i)≤δ:=by
    have gone:Tendsto (fun n:ℕ×ℕ=>(((2:ℕ)^Fintype.card s-1:ℕ):ℝ)*(rate R n.1*∏i:s,C i)) f.fuse (𝓝 0):=by
      simpa only [zero_mul,mul_zero] using (faded.mul_const (∏i:s,C i)).const_mul (((2:ℕ)^Fintype.card s-1:ℕ):ℝ)
    exact (gone.eventually_lt_const dp).mono (fun _ h=>h.le)
  filter_upwards [issued,eventually_all.mpr small] with n ready toll
  obtain ⟨h,linear,prices⟩:=ready
  refine ⟨h,?_⟩
  intro z X r rows T dates checked
  choose L good using fun i:I=>linear (d i) n.2 (z i) (X i) (r i) (rows i)
    (T i) (by have:= (d i).isLt;omega) (dates i) (checked i)
  refine ⟨L,good,?_⟩
  intro s w cheap avoids m early v U placed J _ loc watch distinct housed Z away bounded
  let x (i:s):=(T i).wheel.atCut n (d i) (w i)
  let y (i:s):=L i (w i)
  have budget (i:s):amount R (d i) ℓ (A i) (x i) (y i)≤C i:=by
    apply price R (nnA i)
    · refine (normPaid R (x i)).trans ((fits i.val (T i) (d i) rfl (dates i) (checked i) (w i) n.1 n.2 h).trans ?_)
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (cheap i) (hc i)) gb) (Real.exp_pos _).le
    · refine (good i (w i)).2.trans ?_
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (cheap i) (hc i))
        (mul_nonneg (nn (d i)) gb)
  have positive (i:s):0≤amount R (d i) ℓ (A i) (x i) (y i):=by
    dsimp only [WilsonThermometerWeakWardMoments.amount,WilsonThermometerWeakWardRoster.leaf]
    positivity [nnA i,(Rf).S.a_pos ℓ,size_ge (y i)]
  have total:=prices s (fun i=>z i) (fun i=>X i) (fun i=>r i) x y (fun i=>rows i)
    (fun i=>(good i (w i)).1.symm) avoids m early v placed J loc watch distinct housed away bounded
  apply total.trans
  apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg fun i _=>U.root_nonneg _ _)
  refine le_trans ?_ (toll s)
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  exact Finset.prod_le_prod (fun i _=>positive i) (fun i _=>budget i)

end YM.Integration.WilsonThermometerWeakWardLimit
end
