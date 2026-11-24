import YM.Integration.WilsonOriginalPositionReportedCell
import YM.Integration.WilsonPositionFineCouplingBill

/-! The signed microscopic profile and position thermometer can be compared at the
very same original fine coupling. Its cutoff variation and finite scalar composition
are paid on the common preselected mesh. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPositionFineScheme
open Filter Set Function Finset Lattice Wilson RG Source Extraction Table Spec
open PhysicalNext.Repeat.Legato RG17 Trace.Pilot PhysMS Climb OPE OPE.Orbits
open Maxwell XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open Next.UVStress Pert.Asymptotics FVA2 FVA2.Register FVA2.Scale MS MS.Land MS.Fleet
open WilsonPositionSeparatedProfileMatching WilsonPositionThermometerRunning WilsonPositionRawMesh
open scoped Topology BigOperators Classical
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (J : ℝ → PhysMS.tower S) (Z : WilsonPrescription G)
    {hG : G.Simple} {T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {σ : Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match Z hG T σ dial)
    {l : Ultrafilter (ℕ × ℕ)} {Y : (Bel R.family.book).Hierarchy}
    (A : ℝ → WilsonPositionThermometerCapStation.Group R.family 6)
local notation "θ" => WilsonPositionHomogeneousFrame.reading F J Z

variable {B:ℕ} (hB : 0<B) (pace : WilsonWindowReportingPace.Slow R.kit) (fine index : ℝ→ℕ)
local notation "m" => WilsonMeasuredWindow.stop R.family.path.levels hG B
local notation "Λ" => WilsonPositionAuxiliaryReporterCalendar.scale R hG (B:=B)
local notation "thermal" => WilsonPositionRawCutoff.thermometer Z F J A

def enrolled : Prop := ∀ᶠ r in trail, m r ≤ fine r ∧
  (Λ r)^((3:ℝ)/2) ≤ (index r:ℝ)*Real.log Z.run.ratio ∧
  (index r:ℝ)*Real.log Z.run.ratio ≤ (Λ r)^((3:ℝ)/2)+2*(Λ r) ∧
  R.family.S.a (fine r)/R.family.S.a (m r)=(Z.run.step (index r)).spacing

include hB pace in
/-- Choose one actual cutoff-independent pair of dates for every later finite calculation. -/
theorem calendar {a : Axis} {ε : ℝ} (purchase : WilsonPositionProgramElection.course hG a ε R.kit)
    {d:ℕ} (hd : 0<d) (ratio : Z.run.ratio=3^d) :
    ∃ fine index : ℝ→ℕ, enrolled (R:=R) (hG:=hG) (B:=B) Z fine index := by
  let paid (r:ℝ) (j:ℕ×ℕ) : Prop := m r ≤ j.1 ∧
    (Λ r)^((3:ℝ)/2) ≤ (j.2:ℝ)*Real.log Z.run.ratio ∧
    (j.2:ℝ)*Real.log Z.run.ratio ≤ (Λ r)^((3:ℝ)/2)+2*(Λ r) ∧
    R.family.S.a j.1 / R.family.S.a (m r)=(Z.run.step j.2).spacing
  let date (r:ℝ) : ℕ×ℕ := if h:∃ j,paid r j then h.choose else (0,0)
  have dates := (WilsonMeasuredWindow.stop_tendsto R.family.path.levels hG B hB).eventually
    (WilsonPositionProgramInversion.chosen R hG Z.run purchase hd ratio pace.2)
  refine ⟨fun r=>(date r).1,fun r=>(date r).2,?_⟩
  filter_upwards [dates] with r pick
  obtain ⟨w,j,_,_,spacing,lo,hi⟩ := pick
  have witness : ∃ k,paid r k := ⟨(m r+j,WilsonPositionProgramCommonWindow.elapsed w j),Nat.le_add_right _ _,lo,hi,spacing⟩
  change paid r (date r)
  simpa only [date, dif_pos witness] using witness.choose_spec

def paired (d : ℕ) {n : ℕ} (φ : Test n) (v : Tags G d n) (q : ℕ) : Prop :=
  ∃ (w : ℝ → (ℕ × ℕ) → Fin n → R.family.label d) (c : ℝ → Fin n → R.family.label d),
  (∀ᶠ r in trail, ∀ i, Tendsto (fun z=>w r z i) (l : Filter _) (𝓝 (c r i)) ∧
    S.project d (c r i)=WilsonPositionHomogeneousPanel.field F J Z d v r i) ∧
  ∀ δ>0, ∀ᶠ r in trail,
    ∃ D : Handoff.Directory Z (index r) (Handoff.Directory.budget G n d+q),
    ∀ᶠ z:(ℕ × ℕ) in (l:Filter _), let u:=Pert.Asymptotics.regulatorRun R.family z.1 z.2 (fine r)
      ‖(∑ site : WilsonPositionPhysicalCellTest.Sites R z n,WilsonPositionPhysicalCellTest.mass φ r z site *
            R.family.ensemble (N:=z.1) (p:=z.2) (fun _=>d) site (w r z)) -
        WilsonPositionOriginalCellAverage.average (Z.run.step (index r)) φ
          (WilsonPositionEpochCellTariff.data D d q v (u:ℂ))‖ ≤ δ*|θ r|^q ∧
      |thermal r z-forward Z (Z.run.step (index r)) q u| ≤ δ*|θ r|^q

include H hB pace in
theorem observed (schedule : enrolled (R:=R) (hG:=hG) (B:=B) Z fine index)
    (lead : Leading F J) (book : WilsonPositionCapTransport.Book (f:=f) (l:=l) (H:=Y) A J)
    (prior : (l : Filter _) ≤ f.fuse) (coordinate : Coupling G θ)
    (d : ℕ) {n : ℕ} (φ : Test n) (v : Tags G d n) (q : ℕ) (hq : 0<q)
    (test : paired (l:=l) F J Z A fine index d φ v q) :
    WilsonPositionAuxiliaryMatch.booked Z F J d φ v q := by
  obtain ⟨w,c,labels,deposit⟩ := test
  apply WilsonPositionRawCutoff.on_axis Z H d φ v q F J
    (fun _ r z=>Pert.Asymptotics.regulatorRun R.family z.1 z.2 (fine r)) lead A book prior coordinate
    (fun r=>WilsonPositionHomogeneousPanel.panel d φ r (w r))
  · filter_upwards [labels,RG17.positiveLength] with r marked hr
    exact WilsonPositionHomogeneousPanel.signed F J Z d φ v hG prior hr (w r) (c r)
      (fun i=>(marked i).1) (fun i=>(marked i).2)
  intro δ hd
  have zero := coordinate.conforms hG
  have small := zero.eventually_lt_const (zero_lt_one : (0:ℝ)<1)
  have legal := (goesFront (Expense.Stretched.runs Z.run)).eventually (Rose.usable Z.scheme Z.criterion hG)
  obtain ⟨k,hk⟩ := eventually_atTop.mp legal
  have late := (WilsonPositionAuxiliaryMesh.grows Z.run q trail coordinate.positive zero).eventually_ge_atTop k
  have fee := WilsonPositionFineCouplingBill.interval R hG hB pace θ coordinate Z H q hq hd
  have floors := WilsonPositionProgramInversionBill.interval R hG hB pace θ coordinate Z H q (show 0<(1:ℝ) by norm_num)
  have lr := Real.log_pos (show 1<(Z.run.ratio:ℝ) by
    exact_mod_cast (show 1<Z.run.ratio from (by decide : 1<3).trans_le Z.run.large))
  have clock := (WilsonPositionAuxiliaryReporterCalendar.measured R hG hB pace θ coordinate).eventually_lt_const
    (show (2:ℝ)<3 by norm_num)
  have grows : Tendsto Λ trail atTop := tendsto_atTop_add_const_left _ _
    ((WilsonAdmissionScale.logarithm_tendsto R.family.path.levels hG).comp
      (WilsonMeasuredWindow.stop_tendsto R.family.path.levels hG B hB))
  have bill := WilsonPositionOriginalCellAverage.paid φ Z H q v trail coordinate.positive zero
    (48/Real.log Z.run.ratio) 2 (show 0<δ/3 by linarith)
  filter_upwards [schedule,clock,grows.eventually_ge_atTop 9,small,late,coordinate.positive,
    deposit (δ/3) (by linarith),fee,floors,bill] with r geom measure big tiny many hot issue pay found quad
  obtain ⟨mf,lo,hi,_⟩ := geom
  obtain ⟨D,pairs⟩ := issue
  have iFloor := (found (index r) lo hi).1
  have upper : (index r:ℝ) ≤ 48/Real.log Z.run.ratio*(-Real.log (θ r))^2 := by
    have power : (Λ r)^((3:ℝ)/2) ≤ (Λ r)^2 := by
      rw [←Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    have head : Λ r≤4*(-Real.log (θ r)) := by linarith
    have rect : (Λ r)^2 ≤ (4*(-Real.log (θ r)))^2 := by gcongr
    have size : (index r:ℝ)≤48*(-Real.log (θ r))^2 /Real.log Z.run.ratio :=
      (le_div_iff₀ lr).mpr (by nlinarith only [hi,power,rect,mul_nonneg (by linarith : 0≤Λ r-1) (by linarith : 0≤Λ r)])
    exact size.trans_eq (by ring)
  refine ⟨index r,iFloor,?_⟩
  filter_upwards [pairs,(large_mesh f (fine r)).filter_mono prior] with z heard live
  let u := Pert.Asymptotics.regulatorRun R.family z.1 z.2 (fine r)
  obtain ⟨unit,img,debt⟩ := pay (index r) lo hi (fine r) z.1 z.2 mf live
  refine ⟨unit,img,?_,?_,debt⟩
  · rw [WilsonPositionPhysicalCellTest.panel,WilsonPositionRawEpoch.through Z H D d φ v q
      (hk _ (many.trans iFloor)) le_rfl]
    have cache := quad (index r) iFloor upper D le_rfl u unit
    have smallPower : (θ r)^(q+1)≤|θ r|^q := by
      rw [abs_of_pos hot,pow_succ]; exact mul_le_of_le_one_right (pow_nonneg hot.le _) tiny.le
    apply (norm_sub_le_norm_sub_add_norm_sub _ (WilsonPositionOriginalCellAverage.average
      (Z.run.step (index r)) φ (WilsonPositionEpochCellTariff.data D d q v (u:ℂ))) _).trans
    rw [norm_sub_rev] at cache
    exact (add_le_add heard.1 (cache.trans (mul_le_mul_of_nonneg_left smallPower
      (by linarith)))).trans (by nlinarith only [mul_pos hd (pow_pos (abs_pos.mpr hot.ne') q)])
  · exact heard.2.trans (mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg (abs_nonneg _) _))

include H hB pace in
theorem original (ν : ℝ) {arch : Trace.Terrace.Arch R.family} (bliss : Bliss F l arch Y)
    (book : WilsonPositionCapTransport.Book (f:=f) (l:=l) (H:=Y) A J)
    (schedule : enrolled (R:=R) (hG:=hG) (B:=B) Z fine index)
    {C η : ℝ} (slack : η<1)
    (thermometer : WilsonMaxwellThermometerFirstInvoice.invoice F J A Z.criterion Z.scheme hG B l C η)
    (reader : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (lead : Leading F J)
    (obedient : ∀ d, ∀ᶠ r in trail, Frame.obedient F Y (J r) d) (X : Scaling S) (foundation : Foundation F reader)
    (charged : ∀ d n (φ:Test n) (v:Tags G d n) q,0<q → paired (l:=l) F J Z A fine index d φ v q) :
    WilsonOriginalPositionScheme.Matched F J Z (T:=T) ν := by
  have coordinate := WilsonMaxwellThermometerFirstInvoice.original F J A Z.criterion Z.scheme hG B
    pace hB bliss book lead slack thermometer
  apply WilsonOriginalPositionScheme.matched F J Z H ν reader lead obedient X foundation coordinate
  intro d n φ v q
  cases q with
  | zero => exact WilsonOriginalPositionRawScheme.ground F J Z H ν lead obedient d φ v
  | succ k =>
    exact observed F J Z H A hB pace fine index schedule lead book bliss.lies coordinate d φ v _
      (by omega) (charged d n φ v _ (by omega))

end YM.Integration.WilsonOriginalPositionFineScheme
