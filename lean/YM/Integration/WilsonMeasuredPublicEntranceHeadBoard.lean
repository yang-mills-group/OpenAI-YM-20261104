import YM.Integration.WilsonMeasuredPublicEntrancePhysicalHeads

/-! The full public Wilson roster supplies the actual separately charged physical
head of every slot, retaining the sold whole face and every mixed hard row. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceHeadBoard
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Trace.Physical Trace.Physical.GermGraph Push Marker Motion PhysicalNext PhysicalNext.Repeat
open PhysicalNext.Repeat.Legato MergeProof MergeProof.Accent RG05Readout RG05Readout.Address RG05Readout.Many
open RG05Readout.Copper RG05Readout.Pantry RG05Readout.Native RG05Readout.Records RG05Readout.Harvest
open Push.Local RG12 Push.GridApprox Bandage Extra.Multi MergeProof.Menu Next.Rank Edition Baler Value Glyph Thirst Alarm
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetField
open WilsonThermometerOwnOffsetTale WilsonThermometerOwnOffsetNectar WilsonThermometerOwnOffsetRadii
open WilsonThermometerReflectedTrajectory
open scoped Classical BigOperators
section Income
variable {G:Gauge} (R:Run G) {N p k:ℕ} {I:Type} [Fintype I] [DecidableEq I]
variable (d:I → ℕ) (z:I → Site (R.family.side N p)) (c:I → Site (R.family.side k p))
  (y:(i:I) → Palette R.family (d i)) (V:(i:I) → Sight R.family (d i) p)
  (r:(i:I) → Emblems R.family (d i)) (J:Census I)
local notation "P" => R.family.path.rep N p k
local notation "B" => WilsonThermometerOffsetLedger.cash R
local notation "atRoot" => fun i:I=>point R (z i) (1,false) (c i) k
local notation "s0" => fun _:I=>(1,false)
local notation "home" => WilsonThermometerOwnOffsetJoint.origins R (fun i=>WilsonThermometerReflectedRoster.endpoint R (z i) (1,false) (c i)) k
local notation "soft" => fun i:I=> (marked R (z i) (1,false) (c i) (V i) (r i) (y i) k).2.1
local notation "forced" => fun i:I=>profile (P).activities (marked R (z i) (1,false) (c i) (V i) (r i) (y i) k).2.2

def Income (deep:k<N) (t:ℕ) (W:I → Config G (R.family.side N p) → ℂ):Prop :=
    let F:=WilsonThermometerReflectedRoster.density R d z s0 c y r J deep.le deep.le
    let w:=fun _:I=>radius R t k k
    ∃ q:(i:I) → Coefficient (R.family.labels.level (d i)) (R.family.side k p),
      (∀i,(q i).Format (atRoot i) R.family.params (P)) ∧
      (∀i,(q i).remBound (atRoot i) (P) (kappa R.family.path k) (B (d i) k*size (y i))) ∧
      (∀i,Germ.projection (R.family.labels.level (d i)) R.family.params (P).p.threshold
          (atRoot i) (q i)=y i (primaryLetter (d i))) ∧
      (∀i,soft i=(q i).exponentialEntry (atRoot i) (R.family.localSection (d i)) (P)) ∧
      (∀i,forced i=profile (P).activities (q i).forced) ∧
      (∀v U,(q v).density (atRoot v) (R.family.localSection (d v)) (P) U=
        (P).eval U • actualTransport R.family (N:=N) (W v) deep.le U) ∧
      ∃H K, Carton atRoot H K (P).p.threshold ∧ F=restore (P) soft forced H K ∧
        ∀u:ℂ, ‖u‖ ≤ Real.exp (((P).p.B/8:ℕ):ℝ) →
        Served (P) soft forced (restore (P) soft forced (fun Z U=>u • H Z U) (fun b U=>u • K b U))
          atRoot w ((P).p.supportExponent-1) 1

end Income
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08 Next.Rank Marker MergeProof Accent Extra.Multi
open RG05Readout RG05Readout.Address RG05Readout.Records Menu Extra.Trajectories Push.GridApprox.Nil
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open WilsonThermometerOwnOffsetField WilsonThermometerMarchSource WilsonAddressedAlignedColumn
open WilsonAddressedPublicPool WilsonAddressedPublicCrown WilsonThermometerReflectedTrajectory
open scoped Classical Topology BigOperators
variable {G : Gauge} (R : Run G) {f : Extraction.Order} {S : Table R.family.book} (F : Final R.family f S)
    {D : ℕ} (l:Ultrafilter (ℕ×ℕ))
open WilsonMeasuredPublicClearance WilsonThermometerUnitFilingFourPoolClock WilsonThermometerUnitFilingFourPoolShell
open GapsContact GapsContact.Seams GapsContact.Stamps OPE Trace.Pilot PhysMS FVA2 FVA2.Register
variable {z:Trace.Terrace.Arch R.family}
local notation "C₀" => R.family

theorem original (simple : G.Simple) (shop : RG05Preconstruction.ReadoutPurchase R.b)
    :
    ∃ t ≥ D+3, ∀ (T count:ℕ) (δ:ℝ), 0<δ → ∀ᶠ r:ℝ in trail,
    ∀ board:Book F l (z:=z) D T count δ r, let j:=board.bank.j
    ∀ p N (deep : j < N),
    ∃ (V : (a : Fin (D+1)) → Sight C₀ a.val p) (u : (a : Fin (D+1)) → Emblems C₀ a.val)
      (est : ∀ a : Fin (D+1), Opened C₀ a.val (j) p),
    (∀ a, Enrolled R.makes R.doors (WilsonThermometerOffsetLedger.cash R) (j) N p a.val
      (digits R N p 0) (V a) (u a)) ∧
    ∀ (I : Type) [Fintype I] [DecidableEq I] (d : I → Fin (D+1)) (v : (i : I) → S.Field (d i).val)
      (c : I → Site ((C₀).side (j) p)) (names : Census I),
    let radius:=WilsonThermometerUnitFilingFourPoolShell.radius z (WilsonMeasuredPublicClearance.deep T) r
    let wallet:=dock radius^T
    let L:=fun i=>(board.bank.department (d i).val (Nat.le_of_lt_succ (d i).isLt)).print (v i)
    (∀ i j' : I, i≠j' → ((C₀).path.levels.budget (j)).B^2 <
      separation (point R (N:=N) 0 (1,false) (c i) (j)) (point R (N:=N) 0 (1,false) (c j') (j))) →
    let x:=fun i=>(L i).arm.source (N,p)
    let y := fun i => offer R (x i) (est (d i)) deep.le
    let b := fun i => anchorAt R (c i) N
    let data := fun i => reduce (y i)
    (∀ i, charge (y i) ≤ max 1 (2*(wallet*GapsContact.Ascent.cost F (d i).val (radius) (v i)))) ∧
    WilsonThermometerReflectedRoster.filed R (fun i => (d i).val) (fun _ => 0) (fun _ => (1,false)) c
      data (fun i => V (d i)) (fun i => u (d i)) names deep.le t ∧
    (∀ j (hj : j ≤ N) (s : names.Mode) T,
      (WilsonThermometerReflectedRoster.density R (fun i => (d i).val) (fun _ => 0) (fun _ => (1,false)) c
        data (fun i => u (d i)) names deep.le hj T).part s =
      ((C₀).path.rep N p j).eval T • actualTransport C₀ (N:=N)
        (fun W => ∏ i∈s.val, ((charge (y i):ℝ):ℂ)⁻¹ * (C₀).O N p (x i) (b i) W) hj T) ∧
    Income R (fun i=>(d i).val) (fun _=>0) c data (fun i=>V (d i)) (fun i=>u (d i))
      names deep t (fun i W=>((charge (y i):ℝ):ℂ)⁻¹ * (C₀).O N p (x i) (b i) W) := by
  obtain ⟨t,tp,relative⟩:=WilsonMeasuredPublicEntranceBoard.original (D:=D) R F l (z:=z) simple shop
  have growing:=Real.tendsto_log_atTop.comp (Next.Rank.Station.hat_rate (C₀).path.levels simple)
  obtain ⟨J,wake⟩:=eventually_atTop.mp (growing.eventually_ge_atTop (3:ℝ))
  refine ⟨t,tp,?_⟩
  intro T count δ pos
  have small:∀ᶠ r:ℝ in trail,δ*r<(C₀).S.a J:=by
    have lim:Tendsto (fun r:ℝ=>δ*r) trail (𝓝 0):=by
      have h:Tendsto (fun r:ℝ=>r) trail (𝓝 0):=nhdsWithin_le_nhds
      simpa using h.const_mul δ
    exact lim.eventually_lt_const ((C₀).S.a_pos J)
  filter_upwards [relative T count δ pos,small] with r placed cost board j per N deep
  let dep:=board.bank.department 0 (Nat.zero_le _)
  let seed:=dep.print 0
  obtain ⟨eqj,eqm⟩:=dep.dated 0
  have mj:board.bank.m≤j:=by simpa only [seed,j,eqj,eqm] using seed.fore
  have mature:J≤j:=by
    apply le_of_not_gt
    intro no
    have overlap:=(C₀).S.strictAnti.antitone ((board.before.trans mj).trans no.le)
    linarith [board.small]
  have growth:3≤Real.log ((C₀).path.levels.clock.hatBeta j):=wake j mature
  have wide:5≤((C₀).path.levels.budget j).B:=by
    have land:(Real.log ((C₀).path.levels.clock.hatBeta j))^2 ≤ ((((C₀).path.levels.budget j).B:ℕ):ℝ):=Nat.le_ceil _
    exact_mod_cast (show (5:ℝ)≤((((C₀).path.levels.budget j).B:ℕ):ℝ) by
      nlinarith only [land,growth,sq_nonneg (Real.log ((C₀).path.levels.clock.hatBeta j)-3)])
  have vac:(R.family.path.rep N per j).p=(C₀).path.levels.budget j:= (R.makes.wilson.represents N per j deep.le).vac
  obtain ⟨V,u,est,enrolled,seated⟩ := placed board per N deep
  refine ⟨V,u,est,enrolled,?_⟩
  intro I fi di d v c names r₀ wallet L far x y b data
  obtain ⟨amount,full,fields⟩:=seated I d v c names far
  refine ⟨amount,full,fields,?_⟩
  apply WilsonMeasuredPublicEntrancePhysicalHeads.original R (fun i=>(d i).val) (fun _=>0) c data (fun i=>V (d i)) (fun i=>u (d i))
    names deep t (fun i=>enrolled (d i)) full _ (fields j deep.le) (vac.symm ▸ wide)
  simpa only [vac] using far

end YM.Integration.WilsonMeasuredPublicEntranceHeadBoard
end
