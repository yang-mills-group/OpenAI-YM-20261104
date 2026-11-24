import YM.Integration.WilsonOlderSignedOneMarkPlant
import YM.Integration.WilsonCenteredDetectorUnit
import YM.Integration.WilsonFirstReceivedGalleryRegular

/-! The rank-zero primary of the complete signed residual on the physical
post. Its value is exactly the signed regular debt in the same deposited
singleton at the flat field. -/

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOlderSignedOneMarkScalar
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open Planned.GuardedAtom Push.Local Source Labels Extra.Histories Next.Foundations
open scoped Classical BigOperators Topology

open Push.AbsoluteSums

variable {G : Gauge} (R : Run G) {m i N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ) (hi : m ≤ i) (cut : i < N)
  (ahead : Mentor.Forecast D R.rolls Q φ books) {V : Type} [Fintype V] [DecidableEq V]
  {X : V → Type} [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats : ℕ)
  (physical : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V))
  (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades
    order shelf seats i hi physical)

local notation "sheet" => R.family.path.levels.clock.op i per
local notation "student" => Oak.student (n:=per) R hk D Q π Γ books hi P.op P.lesson ahead actors
  P.model order P.voter
local notation "Ω" => Oak.expenseReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf
local notation "fig" => Oak.figureReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf
local notation "oldG" => Coat.gStep (Ψ (i+1)).beta
local notation "lamps" => (rendered student (Ψ i).p oldG)
local notation "gauge" => (Tint.Patrol.report student P.output oldG)
local notation "κ" => LocalComparison.forcedDivisor R.family i
local notation "width" => ((Ψ i).p.supportExponent+1+1)

local notation "weights" => Stoop.radius P.w (Ω^6)
local notation "homes" => (P.passport.coarser (sheet).ratio).origin
local notation "debt" => (⟨P.output.old,P.output.hard⟩ :
  Gallery (Wallet actors) P.outputIndex homes (Ψ i) (Stock.census V))
local notation "βhat" => R.alloy.B.a.clock.hatBeta (i+1)
local notation "gf" => Coat.gStep (R.family.path.rep N per (i+1)).beta


local notation "stages" => AllOrder.Floe.Step.tape (Burn.horizon k+2)
local notation "raw" x:max U:max => Integral.markedLog gf U
  (Air.craft student (fun b=>(student b).paint x) grades (π i) stages)

include course cut in
theorem flat (simple : G.Simple) (p : ℕ) (deep : 2*(p+1)+8 ≤ order) (aged : p+4 ≤ 3*k+2)
    {ε : ℝ} (ep : 0<ε)
    (opened : WilsonFirstReceivedEarnedFee.opening R simple P.op.count p order k deep aged ep ≤ i)
    (x : Wallet actors) (v : V) :
    let s:=(Stock.census V).fire v
    let U:Config G (R.family.side i per):=1
    let t:ℂ:=(Ψ i).eval U
    let z:=(LocalComparison.actualPush R.family N per i (physical x) U).part s-t*(raw x U).part s
    t⁻¹*z=(P.output.old.log x U).part s ∧ Poly.toll P.w s*‖t⁻¹*z‖≤(8*Ω^P.op.count)*P.rent+ε*gf^p := by
  intro s U t z
  have widthPos : 0≤width:=by linarith only [(Ψ i).p.exponent_pos]
  have hw:=P.issued.earning.positive
  have aw:=Scene.Armada.paid student P.w grades P.issued.earning (Ψ i).p P.issued.Waffle.soon
  have hs:=aw.sums widthPos hw x U
  have hr:=P.issued.tuition.sums widthPos hw x U
  have hj:=(Lamps.joinPaid aw P.issued.tuition).sums widthPos hw x U
  have force:=P.issued.kept
  have one : 1≤Ω^6:=one_le_pow₀ P.issued.Waffle.cool
  have hd:=Hard.packet_summing P.output.hard force (Ψ i).p.exponent_pos.le
    (fun j=>div_pos (hw j) (lt_of_lt_of_le zero_lt_one one)) x U
  have report:=congrFun (WilsonOriginalReceivedChain.report R hk D Q π Γ Ψ books ahead actors pieces grades order shelf
    seats i hi physical P x) U
  have unpacked:=(WilsonCenteredSingletonMass.ordinary gauge x U v hj hd)
  have clear : flags (Ψ i).p.threshold U=∅ := UVNext.CouplingReset.flags_one (Ψ i).p
  have empty : s≠(Stock.census V).quiet:=by
    intro eq
    exact (Finset.singleton_nonempty v).ne_empty (congrArg Subtype.val eq)
  have hardZero : ((gauge).gas x U).part s=0:=by
    rw [WilsonFirstReceivedGalleryRegular.clear gauge x U clear,Poly.one_part]
    exact if_neg empty
  have join : ((gauge).E.log x U).part s=((lamps).log x U).part s+(P.output.old.log x U).part s :=
    congrArg (fun z : Poly (Stock.census V)=>z.part s) (Lamps.joinLog x U hs hr)
  have whole : ((lamps).log x U)=WilsonRootedKioskOccupiedSlip.bare lamps x U := by
    unfold Lamps.log WilsonRootedKioskOccupiedSlip.bare
    apply tsum_congr
    intro b
    change Poly.send _ ((lamps).light x b U)=Poly.send _ ((lamps).nominal x b U)
    congr 1
    unfold Lamps.light
    split
    · rfl
    exact masked_eq _ _ _ _ (one_healthy _ _ (Ψ i).p.threshold_pos.le)
  have nominal : WilsonRootedKioskOccupiedSlip.bare lamps x U=raw x U := by
    have hp : 0 < (R.family.path.rep N per (i+1)).beta:=Overlay.beta_positive R.makes.wilson cut
    let inks := fun b=>(student b).paint x
    have issued:=Air.license student inks grades P.w P.issued.earning (Poetry.Agenda.stem ..)
      (fun b=>P.issued.earning.honor b x)
    have reading:=Air.liftPassport student inks grades issued (π i) stages gf
      (inv_pos.mpr (Real.sqrt_pos.mpr hp)).ne' U
    refine Eq.trans ?_ reading.tsum_eq
    unfold WilsonRootedKioskOccupiedSlip.bare
    apply tsum_congr
    intro b
    have shift:=(course.1.walk (i+1) (Nat.le_succ_of_le hi) cut).beta
    simp only [rendered,Air.grainR,Row.nominal,inks,shift]
    rfl
  have row : (LocalComparison.actualPush R.family N per i (physical x) U).part s =
      t*((raw x U).part s+(P.output.old.log x U).part s) := by
    calc
      _ = ((gauge).density x U).part s:=congrArg (fun a : Poly (Stock.census V)=>a.part s) report
      _ = t*((gauge).E.log x U).part s+(Real.exp ((Ψ i).exponent U):ℂ)*((gauge).gas x U).part s:=unpacked
      _ = _ := by rw [hardZero,mul_zero,add_zero,join,whole,nominal]
  have live : t≠0 := Complex.ofReal_ne_zero.mpr WilsonCenteredCaptureUnit.physicalDenominator.ne'
  have pay : t⁻¹*z=(P.output.old.log x U).part s := by
    change t⁻¹*((LocalComparison.actualPush R.family N per i (physical x) U).part s-t*(raw x U).part s)=_
    rw [row,mul_add,add_sub_cancel_left,←mul_assoc,inv_mul_cancel₀ live,one_mul]
  have inc:=WilsonReceivedInheritedFee.original R hk D Q π Γ Ψ books hi cut P.op P.lesson ahead actors P.model
    P.w grades order shelf P.voter P.cost pieces P.input P.rent P.output P.issued simple p deep aged ep opened
  refine ⟨pay,?_⟩
  rw [pay]
  exact (WilsonFirstReceivedGalleryRegular.occupied P.output.old P.issued.tuition widthPos hw x U s v
    (mem_singleton_self _)).trans inc

include course cut in
theorem complete (way : WayStation R.kit) (simple : G.Simple)
    (late : WilsonCenteredCaptureClock.first R simple ≤ i) (p q : ℕ)
    (ready : q ≤ R.alloy.B.a.clock.J i) (deep : 2*(p+1)+8 ≤ order)
    (aged : p+4 ≤ 3*k+2) {ε : ℝ} (ep : 0<ε)
    (opened : WilsonFirstReceivedEarnedFee.opening R simple P.op.count p order k deep aged ep ≤ i)
    (x : Wallet actors) (v : V) (Z : Support (R.family.side i per)) (y : Site (R.family.side i per))
    (center : y∈Z) (member : homes v∈Z) (rad : ℕ) (near : separation (homes v) y≤rad)
    {F : Labels.Frame G 0} (S : SectionData F) (Y : Hol G) {μ : ℝ}
    (reader : Readable Y S (Ψ i).p (R.family.side i per) μ) :
    let s := (Stock.census V).fire v
    let toll := WilsonOlderSignedSingletonFare.fare (Ψ i).p S Y weights s 1 Z rad
      ((Ω^6)⁻¹*((8*Ω^P.op.count)*P.rent+ε*gf^p)) (βhat^(-(q:ℝ))*κ) κ
      (R.alloy.B.a.clock.forcedAllowance i) μ
    let gross := (Spill.allOver (Ψ i).p)^(order+shelf+1)*Ω
    let maskCost := WilsonOlderSignedOneMarkMasks.fare (Ψ i).p Z (R.alloy.B.a.clock.forcedAllowance i)
      (Poly.toll P.w s) gross κ
    ∃ A : Coefficient F (R.family.side i per), A.Format y Y (Ψ i) ∧
      A.remBound y (Ψ i) κ (toll+maskCost) ∧ (∀ U, A.density y S (Ψ i) U =
        (LocalComparison.actualPush R.family N per i (physical x) U).part s -
        ((Ψ i).eval U:ℂ)*(raw x U).part s) ∧
      (∀ pr : Probe G 0, runProbe F pr A.x=(P.output.old.log x 1).part s) ∧
      Poly.toll P.w s*F.coeffSize A.x≤testPrice F*((8*Ω^P.op.count)*P.rent+ε*gf^p) := by
  intro s toll gross maskCost
  obtain ⟨A,fit,price,allFields⟩:=WilsonOlderSignedOneMarkPlant.original R hk D Q π Γ Ψ course books hi cut
    ahead actors pieces grades order shelf seats physical P way simple late p q ready deep aged ep opened
    x v Z y center member rad near S Y reader
  have seen:=flat R hk D Q π Γ Ψ course books hi cut ahead actors pieces grades order shelf seats physical P
    simple p deep aged ep opened x v
  let unit := (P.output.old.log x (1 : Config G (R.family.side i per))).part s
  have read (pr : Probe G 0) : runProbe F pr A.x=unit := by
    have empty : pr.2.val=0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ pr.2.isLt)
    calc
      _ = ((Ψ i).eval (1:Config G (R.family.side i per)):ℂ)⁻¹*A.density y S (Ψ i) 1 :=
        WilsonCenteredDetectorUnit.flatProbe A fit reader.sound pr empty
      _ = _ := (congrArg (fun z:ℂ=>((Ψ i).eval (1:Config G (R.family.side i per)):ℂ)⁻¹*z)
        (allFields 1)).trans seen.1
  have cost : F.coeffSize A.x≤testPrice F*‖unit‖ :=
    (probe_budget F).choose_spec.choose_spec.2 A.x _ (norm_nonneg _) (fun i _=>(congrArg norm (read i)).le)
  have due : Poly.toll P.w s*‖unit‖ ≤ (8*Ω^P.op.count)*P.rent+ε*gf^p := by
    exact (congrArg (fun z:ℂ=>Poly.toll P.w s*‖z‖) seen.1).symm.le.trans seen.2
  refine ⟨A,fit,price,allFields,read,?_⟩
  calc
    _ ≤ Poly.toll P.w s*(testPrice F*‖unit‖) :=
      mul_le_mul_of_nonneg_left cost (Poly.worth P.issued.earning.positive s).le
    _ = testPrice F*(Poly.toll P.w s*‖unit‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left due (zero_le_one.trans (probe_budget F).choose_spec.choose_spec.1)


end YM.Integration.WilsonOlderSignedOneMarkScalar
