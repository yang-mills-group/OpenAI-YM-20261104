import YM.Integration.WilsonOriginalPublicFigureSettlement
import YM.Integration.WilsonOriginalPublicTrialRegulators
import YM.Integration.WilsonOriginalPublicRegulatorHearing
import YM.Integration.WilsonOriginalPublicOrderedRegulators
import YM.Integration.WilsonPositionProgramPublicMaster

/-! The original fixed-date measurement compared with the publicly submitted
Mer source, on the same funded normalized finite inversion. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalPublicFigureRoster
open WilsonOriginalThermometerPalette (levels salary)
open Function Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress Next.Rank Next.Rank.East
open WilsonPositionThermometerCapStation
open WilsonPositionProgramNominatedRoster (selected selected_fee)
open WilsonPositionProgramThermometerCoordinates (price)
open WilsonOriginalPublicFiniteInversion (observed terminal)
open WilsonOriginalPublicFigureSettlement (measured nominal evaluate)
open WilsonOriginalPublicFigureCatalogue (filed)
open WilsonPositionProgramInversionMaterial WilsonPositionProgramSeriesRead
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Embroider WilsonCoeffUV.Soil WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Shard WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Bank.Mosaic
open WilsonMarkedIndependentNormalizedElection (deck)
open Filter Finset Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open RegulatorIR RegulatorIR.Ledger RegulatorIR.Calibration RegulatorIR.FVAAlt2
open WilsonThermometerPositionInversionWords WilsonPositionProgramSignedFace
open WilsonPositionProgramReporterBand
open XSpace XSpace.Cirrus FVA2 FVA2.Register MS MS.Land
open scoped Classical ENNReal BigOperators
variable {G : Gauge} (C : Run G) {AUX : Type}
    {simple : G.Simple} {a : Axis} {ε : ℝ}
    (first : WilsonPositionProgramArithmetic.course simple a ε C.kit)
    (paid : WilsonPositionProgramStageInvoice.Requested C.kit) (slow : WilsonWindowReportingPace.Slow C.kit)
    (branch : ∀ P : RG.Patch, P.Branches C.family.path.levels.clock.kernel G) (p : ℕ) (color : G.ColorIndex)
    (Z : WilsonPrescription G) {M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {T : Prescription (Press.portDeck G)} {dial : Bool} (matchMS : Main.Match Z simple M T dial)
local notation "Ω₀" => ℕ × AUX
local notation "Y" => Oracle.books C.family.path.levels.clock.kernel
local notation "Λ" => RG16.Lambda C.family.path.levels

include first paid slow matchMS in
theorem original (Q : Prescription (Press.portDeck G))
    (calibration : TaylorOKPl M (YM.FVAAlt2.Lobby.Table (Lodge.basisR C) (Press.portDeck G)) Q)
    (floor : ℕ) {d₀ : ℕ} (hd : 0<d₀) (ratio : Z.run.ratio=(3:ℕ)^d₀)
    (pace : ∀ m, ((C.family.S.block m).val:ℝ) ≤ Real.log (Λ m))
    (grades reporters:Fin 3→ℕ)(fixedStop target:ℕ)(η:ℝ)(M₀:Fin 3→ℝ)
    (ports:∀a:Fin 3,ℕ×ℕ→C.family.label (grades a))(before:∀a,reporters a≤fixedStop)
    (bought:WilsonOriginalMicroscopicGuardedPageSchool.Indexed C grades reporters target η M₀ ports)
    {n:ℕ}(nonempty:0<n)(room:Set (Points n))(compact:IsCompact room)(apart:room⊆conf n):
    ∃stage,∃B:Band C Z.run stage,(∀t,floor≤B.index t) ∧
      let m:=fun u:Ω₀=>B.lower u.1
      let j:=fun u:Ω₀=>B.span u.1
      let w:=fun u:Ω₀=>B.powers u.1
      let S:=WilsonPositionProgramInfraredCircuit.circuit C Z.run m j w (fun u=>B.blocks u.1)
      ∀(z:Ω₀→Fin n → Cover)(c:Ω₀ → Four ℝ),(∀u,c u∈(Z.run.step (B.index u.1)).Box) →
        (∀u,(Z.run.step (B.index u.1)).rel (z u) (c u)∈room) →
      ∃F:Tent j,Notebook S Y G branch color (Rocket.native j) F p ∧
      (∀ {l : ℕ} (child : Fin l → Fin n), Function.Injective child →
        ∀ (d : ℕ) (v : Fin l→Dframe.Toon G d) (μ : ℝ) (k : ℕ), k≤p →
        ∃ E : ℝ, 0<E ∧ ∀ᶠ t in atTop, ∀ y : AUX, ∀ cap (P : Handoff.Directory Z (B.index t) cap),
          Handoff.Directory.budget G l d + k ≤ cap →
          let e := fun x : Ω₀ => (Z.run.step (B.index x.1)).spacing
          let θ := fun x => μ+Real.log (e x)
          ‖PowerSeries.coeff k (Rocket.adjust S Y branch F (Lodge.basisR C)
            (WilsonPositionProgramSubmittedCoefficient.final j) (Dframe.flash ∘ v) (fun x => (z x) ∘ child) Q θ e (t,y)) -
            WilsonPositionProgramPoint.entry Z (T:=T) P d μ ((z (t,y)) ∘ child) (Dframe.fill v) k‖ ≤
            E*(e (t,y))^Tide.mildG) ∧
      ∀(J:Type)[Fintype J](arity:J→ℕ)(names:(s:J)→Fin (arity s+1)→Fin 3)
        (child:(s:J)→Fin (arity s+1)→Fin n)(dd:(s:J)→Fin (arity s+1)→ℕ)
        (fit:∀s i,grades (names s i)<dd s i),
        let l:=fun s=>grades ∘ names s
        let fields:=fun s=>deck (G:=G) (l s) (dd s) (fit s)
        let L:=C.family.path.levels
        ∀{h D₀ k u e:ℕ}(fund:ℕ→Gear G→ℝ),FundedMarkedCoverRows.prices fund C.kit → h<D₀ →
        Rails h k u e → (∀s,capP (fields s) ≤ k) → e ≤ p →
        ∃loss:J→ℕ,∃A:J→ℝ,(∀s,0≤A s) ∧
        ∀(f:Extraction.Order)(trees:∀t,(Z.run.step (B.index t)).p.Tree)(strength:ℕ),
        ∀ᶠ t in atTop,∀menu:Finset AUX,
        let m₀:=B.reporter+t
        let top:=m₀+B.upper t
        ∀ᶠ inversion in atTop,∀ᶠ ξ in f.fuse,fixedStop<ξ.1 ∧ m₀<ξ.1 ∧
        ∀(s:J)(q:Fin (e+1)),∀y∈menu,∀(phase:Fin 3→ℂ →L[ℝ] ℝ)(probe:(i:Fin (arity s+1))→Volume (dd s i)),
          let v:=(fun i=>WilsonOriginalPublicTrialInput.vector C grades reporters fixedStop target η M₀ ports before bought ξ.1 ξ.2 (names s i))
          let X:=WilsonOriginalPublicTrialRegulators.dose C grades reporters fixedStop target η M₀ ports before bought
            (names s) (dd s) (fit s) phase ξ.1 ξ.2
          let x:=fun i=>PermuteLens L C.metals.O (fields s i) top m₀ (X i)
          let field:=fun i=>steep L C.metals.O (fields s i).ans (fields s i).path top m₀ (top-m₀) (x i)
          let ζ:=dose C (l s) field (dd s) (fit s) probe
          let ε:=(Z.run.step (B.index t)).spacing
          let Δ:=fun b=>filed C (l s) v b-ζ b
          let survey:=observed C Z.run m j w (fun a=>B.blocks a.1) branch F (fun a=>z a ∘ child s) (l s) (t,y) q.val inversion
          let P:=(Z.run.step (B.index t)).p
          let pos:=z (t,y) ∘ child s
          (∀i,WilsonPositionProgramNormalizedMaster.fee X e i ≤
            WilsonOriginalPublicTrialInput.bill C grades reporters fixedStop η M₀ e phase (names s i)) ∧
          ‖measured C (l s) q.val P pos (trees t) v-nominal C (l s) q.val P pos (trees t) ζ-evaluate C (l s) q.val survey Δ‖ₑ ≤
            2*(ENNReal.ofReal (ε^(strength+loss s))*WilsonOriginalPublicFigureCharges.bill C grades reporters fixedStop η M₀ (names s) q.val+
            ENNReal.ofReal (A s*ε^strength*∑b:Terms C (l s) q.val,∏i,
              WilsonPositionProgramNormalizedMaster.fee X e i*‖jewelBloom (fit s i) (b.1 i) (probe i)‖)):=by
  obtain ⟨stage,B,late,commission⟩:=WilsonOriginalPublicFigureSettlement.original (AUX:=AUX)
    C first paid slow branch p color Z matchMS grades reporters fixedStop target η M₀ ports before bought
    Q calibration floor hd ratio pace nonempty room compact apart
  refine ⟨stage,B,late,?_⟩
  intro m j w S z c hc hz
  obtain ⟨F,file,scheme,transfer⟩:=commission z c hc hz
  refine ⟨F,file,scheme,?_⟩
  intro J _ arity names child dd fit l fields L h D₀ k u e fund earn big rails cap order
  choose loss sold using fun s:J=>WilsonPositionProgramMasterTestCost.original C simple fund earn big rails (l s) (dd s) (fit s) (cap s)
  choose A a_pos funds using fun s:J=>sold s Z.run B
  refine ⟨loss,A,a_pos,?_⟩
  intro f trees strength
  have payouts:=Filter.eventually_all.2 (fun s:J=>Filter.eventually_all.2 (fun q:Fin (e+1)=>
    transfer (Fin (arity s+1)) (names s) (child s) trees q.val ((Nat.le_of_lt_succ q.isLt).trans order) (strength+loss s)))
  filter_upwards [payouts,Filter.eventually_all.2 funds] with t bills credits
  intro menu m₀ top
  filter_upwards [Filter.eventually_all.2 (fun s:J=>Filter.eventually_all.2 (fun q:Fin (e+1)=>(bills s q) menu))] with inversion passed
  apply (Extraction.Order.fused f _).2
  rw [Extraction.Order.late]
  apply Filter.Eventually.of_forall
  intro per
  filter_upwards [f.mesh.cofinal.eventually_ge_atTop (max fixedStop m₀+1)] with N high
  have live:fixedStop<f.mesh.choose N:=by omega
  refine ⟨live,by omega,?_⟩
  intro s q y used phase probe v X x field ζ ε Δ survey P pos
  have hear:=(passed s q y used (f.mesh.choose N) (f.per.choose per) live).2 ζ
  have adjust:=credits s X probe q.val (Nat.le_of_lt_succ q.isLt) strength
  constructor
  · exact fun i=>((WilsonOriginalPublicTrialInput.original C grades reporters fixedStop target η M₀ ports before bought
      (f.mesh.choose N) (f.per.choose per) live).2.2.2 (names s) (dd s) (fit s) phase e i).2
  · apply hear.trans
    change 2*ENNReal.ofReal (ε^(strength+loss s))*(_+WilsonOriginalPublicFigureCharges.charge C (l s) q.val ζ)≤_
    rw [mul_assoc,mul_add]
    exact mul_le_mul_right (add_le_add le_rfl adjust) 2

abbrev Face:Type:={s:Finset (Fin 3)//s.Nonempty}
def arity(s:Face):ℕ:=s.val.card-1
theorem seats(s:Face):s.val.card=arity s+1:=by
  have h:=Finset.card_pos.mpr s.property
  unfold arity
  omega
def names(s:Face):Fin (arity s+1) → Fin 3:=s.val.orderEmbOfFin (seats s)
theorem actual(s:Face):Set.range (names s)=s.val:=by
  ext a
  simp only [Set.mem_range,Finset.mem_coe,names]
  constructor
  · rintro ⟨i,rfl⟩
    exact Finset.orderEmbOfFin_mem ..
  · intro ha
    let b:s.val:=⟨a,ha⟩
    exact ⟨(s.val.orderIsoOfFin (seats s)).symm b,congrArg Subtype.val ((s.val.orderIsoOfFin (seats s)).apply_symm_apply b)⟩

end YM.Integration.WilsonOriginalPublicFigureRoster
end
