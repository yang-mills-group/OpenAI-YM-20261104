import YM.Integration.WilsonThermometerRegisteredFaceTable
import YM.Integration.WilsonThermometerRegisteredPlantedReturn

/-! A signed two-field reading on the one original three-field appointment. Taking
the difference of two charged complete tableaux retains the proper deposited row,
its independent forest response, and the actual normalized marked hard correction. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonThermometerRegisteredFacePair

open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open Ac OPE.Therm WilsonLimitConstruction RG16 MSbar.Heath Labels Source Pert.Asymptotics
open WilsonRootedKioskOccupiedSlip WilsonRegisteredAffineHalo WilsonRegisteredAxialRates
open WilsonReportingForestAngularFare WilsonJointAxialRoster
open Multi Extra.Trajectories Comparison.RG02.Cumulants WilsonIndependentOrdinaryPairGrade
open FVA1 Cells Extraction Table Climb Trace Trace.Pilot
open WilsonPositionThermometerCapStation WilsonOriginalThermometerPalette WilsonOriginalThermometerMicroscopic
open WilsonThermometerCourseHearing WilsonThermometerRegisteredPair WilsonPositionThermometerGradedReading
open WilsonPositionThermometerGradedSource
open scoped Classical BigOperators Topology

variable {G:Gauge} (R:Run G) (simple:G.Simple) (A:Group R.family 6) {m i per k:ℕ}
  (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
  (π:ℕ → Layout G) (Γ:ℕ → Pace.Coin) (Ψ:∀ j, RG.Rep G (R.family.side j per))
  (course:Concourse R.alloy R.kit R.T π Γ m (i+2) per k Ψ)
  {φ:ℕ → ℕ} (books:Mentor.Offices.Books D R.rolls Q φ) (hi:m ≤ i)
  (ahead:Mentor.Forecast D R.rolls Q φ books)
  (school:Syl.School k) (o:Positions (Fin 3) (R.family.side (i+2) per))
local notation "cut" => (Nat.lt_succ_of_lt (Nat.lt_succ_self i))
local notation "faces" => Stock.census (Fin 3)
local notation "source₀" => WilsonThermometerCourseHearing.offered R A simple cut o
variable (P:WilsonOriginalReceivedChain.Post (N:=i+2) R hk D Q π Γ Ψ books ahead WilsonThermometerCourseHearing.disks sectors levels
  school.order school.horizon school.pieces i hi (WilsonThermometerCourseHearing.offered R A simple (Nat.lt_succ_of_lt (Nat.lt_succ_self i)) o))

local notation "student" => Oak.student (n:=per) R hk D Q π Γ books hi P.op P.lesson ahead WilsonThermometerCourseHearing.disks
  P.model school.order P.voter
local notation "lamps" => (rendered student (Ψ i).p (Coat.gStep (Ψ (i+1)).beta))
local notation "placed" => P.passport.coarser (R.family.path.levels.clock.op i per).ratio
local notation "n" => (school.order+school.horizon+2)
local notation "gf" => Coat.gStep (R.family.path.rep (i+2) per (i+1)).beta
local notation "stage" => R.alloy.B.a.clock.J i


open MeasureTheory
open private exponential from YM.Integration.WilsonFiniteProgramFieldBorel
local notation "tape" => AllOrder.Floe.Step.tape (Burn.horizon k+2)
local notation "names₀" => WilsonThermometerCourseHearing.disks
variable (hearing:ℕ) (J:Voice G) (axes:Lattice.Order)
local notation "H₁" => radius R (invoice (Fintype.card (Fin 3)) (hearing+2*n)) 1 i
local notation "r₁" => amplitude R J (H₁) (i+2) per i
local notation "h₁" => (WilsonDegreeFourInheritedRange.height R (hearing+2*n) i)*(4*(Ψ i).p.B+2)+2*(Ψ i).p.B+1
local notation "τ₁" => angularCut (R.family.path.levels.clock.hatBeta i)
local notation "cold" => House.chilly (G:=G) (plaquettes (placed).origin (H₁)) (τ₁)
local notation "angle₁" => WilsonJointAxialHearing.angleOf (placed).origin (h₁) J axes (r₁) gf
local notation "link₁" z:max =>
  WilsonCapturedPrimaryPotential.potential gf ((r₁) • WilsonJointAxialWindow.direction (placed).origin (h₁) J axes (r₁) z)
local notation "who" x:max =>
  Air.craft student (fun v=>(student v).paint x) levels (π i) tape
local notation "intake" x:max => Air.craft P.model (fun v=>(P.model v).paint x) levels (π (i+1)) tape
local notation "step₁" => (RunFormalChain.fromRun R).step (i+2) i per cut
local notation "bank" x:max z:max => WilsonThermometerRegisteredAllFiled.numerical R A π Γ school o x z
local notation "panel₀" x:max z:max =>
  WilsonCoherentMayerWindingGrades.panel school.order (gf:ℂ) (fun d=>Air.discharge (who x) d z)


open WilsonThermometerCenteredAlgebra WilsonFiniteOrdinaryInverse Primitives.GCC.Anchor WilsonReceivedWholeFieldHot
open Multi Extra.Trajectories Comparison.RG02.Cumulants WilsonIndependentOrdinaryPairGrade Push.AbsoluteSums

local notation "finite₁" x:max F:max t:max U:max =>
  Order.value (gf:ℂ) (Order.ratio (Bulk.Fk (step₁) F t (intake x) (angle₁ U) school.order))


open FVA1 Planned.GuardedAtom Push.Local Extra.Histories Next.Foundations RG16.Literal Next.Rank Next.UVStress
open MergeProof.East OriginalForcedAddresses Exterior WilsonThermometerCourseIntake WilsonThermometerWeightedCapture
local notation "frame" => R.family.labels.level 0
local notation "section₀" => R.family.localSection 0
local notation "dose" U:max => ((Ψ i).eval U : ℂ)
local notation "original" U:max => (incoming R A simple (cut).le o U)
local notation "ids" => (fun h:Fin 3=>WilsonPositionThermometerCapStation.index A
    (WilsonPositionThermometerGradedSource.grade h))
local notation "vector₀" => WilsonPositionThermometerGradedReading.vector A (Finset.univ:Finset (Fin 3))


open WilsonMeasuredCoefficientTransport WilsonPhysicalMarkedDefect.RegularProjection
local notation "physical₁" Q₀:max => WilsonThermometerRegisteredPlantedFaces.physical R A o Q₀
local notation "numerical₁" Q₀:max => WilsonThermometerRegisteredPlantedFaces.predicted R simple A hk D Q π Γ Ψ books hi ahead school o P hearing J axes Q₀
local notation "declared₁" Q₀:max => WilsonThermometerRegisteredOlderMaterial.declared R simple A hk D Q π Γ Ψ books hi ahead school o P hearing J axes Q₀ fired
local notation "κ" => LocalComparison.forcedDivisor R.family i
local notation "rep₁" => R.family.path.rep (i+2) per i

local notation "C₃" => WilsonFiniteOrdinaryInverse.fee (faces)
local notation "profit" p:max => WilsonReceivedCloseOrdinaryGrade.invoice (faces) 3 0 (p+160) 1
local notation "extras" p:max => (4:ℝ)^(p+161+2*n*3)*(Fintype.card (Multi.parts (faces)).Mode)*((2:ℝ)^n)^3
variable (width : ∀ a k : ℕ, k ≤ a → ∀ b : ℝ, R.alloy.delay.betaEntry a ≤ b →
  Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) a)⁻¹ ^ 2) ≤ b)


open WilsonThermometerFullSignedPower WilsonMeasuredCoefficientTransport
local notation "coeffRent" α:max => WilsonFullFaceSignedPower.constants (section₀) R.family.params α ((2:ℝ)^n+4)
local notation "oldCost" p:max => C₃*((profit p)+(extras p))*gf^(p+1)+C₃*(profit p)*gf^(p+1)
local notation "hitCost" p:max α:max => |C₃*(coeffRent α)| *(4^hearing+2)*gf^(p+1)
local notation "unitCost" p:max => |testPrice (frame)*C₃*WilsonFullFaceSignedPower.inter*
    (Fintype.card (Multi.parts (faces)).Mode:ℝ)*125| *gf^(p+1)
local notation "actual₁" Q₀:max h:max => WilsonThermometerRegisteredPlantedSplit.retained R simple A hk D Q π Γ Ψ
    books hi ahead school o P hearing J axes Q₀ h


local notation "weights" => (fun v=>gf*P.w v)
local notation "face₁" t:max => WilsonThermometerCenteredAlgebra.complement t
local notation "sensitivity" t:max => WilsonThermometerRegisteredFaceTable.amp (weights) t
local notation "probe" t:max a:max => WilsonThermometerRegisteredFaceTable.table t ((a:ℝ):ℂ)
local notation "price" p:max α:max => (oldCost p)+((unitCost p)+(hitCost p α))

def physical (t:(faces).Mode) (U:Config G (R.family.side i per)) : ℂ :=
  actualTransport R.family (N:=i+2)
    (fun V=>∏ h∈(face₁ t).val,R.family.O (i+2) per
      (A.station.wheel.atCut (i+2,per) ((ids) h) ((vector₀) h)) (o.origin h) V) (cut).le U

def prescribed (t:(faces).Mode) (U:Config G (R.family.side i per)) : ℂ :=
  (cold).indicator (fun V=>(bank fired (link₁ V)).part (face₁ t)) U

def lowered (t:(faces).Mode) (a:ℝ) (blankBill markBill:Coefficient (frame) (R.family.side i per))
    (U:Config G (R.family.side i per)) : ℂ :=
  physical R A o t U-prescribed R simple A hk D Q π Γ Ψ books hi ahead school o P hearing J axes t U-
    (a:ℂ)⁻¹*(dose U)⁻¹*(account markBill (Ψ i) U-account blankBill (Ψ i) U)

theorem adjusted (t:(faces).Mode) (live:t≠(faces).quiet) (a:ℝ) (ha:0<a)
    (ref:∀v,R.family.ref ((ids) v) ≤ i+2) (blankBill markBill:Coefficient (frame) (R.family.side i per)) :
    lowered R simple A hk D Q π Γ Ψ books hi ahead school o P hearing J axes t a blankBill markBill=
        fun U=>(a:ℂ)⁻¹*((actual₁ (probe t a) markBill) U-(actual₁ (1:Poly (faces)) blankBill) U) :=by
  funext U
  let F:=WilsonThermometerCourseResidual.table R A simple (cut).le o U
  have read (q:Poly (faces)):(physical₁ q) U=(total F q).part full:=by
    rw [affine];unfold WilsonThermometerRegisteredPlantedFaces.physical
    apply Finset.sum_congr rfl
    intro s _
    rw [WilsonThermometerCourseResidual.observed R A simple (cut).le o ref U s]
  have phys : (physical₁ (probe t a)) U-(physical₁ (1:Poly (faces))) U=(a:ℂ)*physical R A o t U:=by
    rw [read,read,WilsonThermometerRegisteredFaceTable.ordinary F t live]
    rw [WilsonThermometerCourseResidual.observed R A simple (cut).le o ref U]
    rfl
  have nom : (numerical₁ (probe t a)) U-(numerical₁ (1:Poly (faces))) U =
      (a:ℂ)*prescribed R simple A hk D Q π Γ Ψ books hi ahead school o P hearing J axes t U:=by
    unfold WilsonThermometerRegisteredPlantedFaces.predicted prescribed
    by_cases hu:U∈cold
    · simp only [Set.indicator_of_mem hu]
      exact WilsonThermometerRegisteredFaceTable.ordinary _ t live _
    · simp only [Set.indicator_of_notMem hu,sub_zero,mul_zero]
  have nz:(a:ℂ)≠0:=Complex.ofReal_ne_zero.mpr ha.ne'
  dsimp only [lowered,WilsonThermometerRegisteredPlantedSplit.retained]
  calc
    _ = (a:ℂ)⁻¹*(((physical₁ (probe t a)) U-(physical₁ (1:Poly (faces))) U)-
      ((numerical₁ (probe t a)) U-(numerical₁ (1:Poly (faces))) U)-
      (dose U)⁻¹*(account markBill (Ψ i) U-account blankBill (Ψ i) U)) := by
        rw [phys,nom]
        field_simp [nz]
    _ = _ := by ring

theorem difference {G:Gauge} (R:Run G) {i N per:ℕ} (live:i≤N)
    (f g:Config G (R.family.side i per) → ℂ) (hf:RG.Envelope f) (hg:RG.Envelope g)
    (B:ℝ) (pf:(∫ U,‖f U‖ ∂scene R.family.path N per i)≤B)
    (pg:(∫ U,‖g U‖ ∂scene R.family.path N per i)≤B) (z:ℂ) :
    let F:=fun U=>z*(f U-g U)
    RG.Envelope F ∧ ∀ j (age:j ≤ i),(∫ U,‖actualTransport R.family (N:=N) F age U‖
      ∂scene R.family.path N per j)≤‖z‖*(2*B) :=by
  intro F
  let μ:=scene R.family.path N per i
  haveI : IsProbabilityMeasure μ:=OPE.Therm.probability (H:=R.family.path) (p:=per) R.makes.wilson live
  obtain ⟨mf,V,fv⟩:=hf
  obtain ⟨mg,W,gw⟩:=hg
  have f₀:Integrable f μ:=Integrable.of_bound mf.aestronglyMeasurable V (ae_of_all _ fv)
  have g₀:Integrable g μ:=Integrable.of_bound mg.aestronglyMeasurable W (ae_of_all _ gw)
  have h (U):‖F U‖≤‖z‖*(‖f U‖+‖g U‖):=by
    rw [show F U=z*(f U-g U) from rfl,norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_sub_le ..) (norm_nonneg z)
  have env:RG.Envelope F:=⟨measurable_const.mul (mf.sub mg),‖z‖*(V+W),fun U=>
    (h U).trans (mul_le_mul_of_nonneg_left (add_le_add (fv U) (gw U)) (norm_nonneg z))⟩
  refine ⟨env,fun j age=>?_⟩
  calc
    _ ≤ ∫ U,‖F U‖ ∂μ:=ActualWilsonAbsoluteTransport.first R.family R.makes live
      (ActualWilsonAbsoluteTransport.weighted R.family R.makes live env) age
    _ ≤ ∫ U,‖z‖*(‖f U‖+‖g U‖) ∂μ := integral_mono ((f₀.sub g₀).const_mul z).norm ((f₀.norm.add g₀.norm).const_mul _) h
    _ = ‖z‖*((∫ U,‖f U‖ ∂μ)+(∫ U,‖g U‖ ∂μ)) := by rw [integral_const_mul,integral_add f₀.norm g₀.norm]
    _ ≤ ‖z‖*(2*B) := mul_le_mul_of_nonneg_left (by linarith only [pf,pg]) (norm_nonneg z)

def Capture (p:ℕ) (t:(faces).Mode) (a:ℝ) (y:Site (R.family.side i per)) (α:ℝ) : Prop :=
  ∃ blankBill markBill:Coefficient (frame) (R.family.side i per),
    (∀h∈({blankBill,markBill}:Set _),h.Format y R.family.params (Ψ i) ∧ h.remBound y (Ψ i) κ (hitCost p α) ∧
      (frame).coeffSize h.x ≤ unitCost p ∧ ∀U,account h (Ψ i) U≠0 →
        ∃ l,h.forced l U≠0 ∧ y∈((rep₁).activities.forced l).support ∧
          ∃ z,z∈((rep₁).activities.forced l).inventory ∧ z∈flags (rep₁).p.threshold U) ∧
    (∀U,blankBill.density y (section₀) (Ψ i) U=(total (original U) 1).part full-
      (dose U)*(total (Poly.pass (bare lamps fired U)) 1).part full) ∧
    (∀U,markBill.density y (section₀) (Ψ i) U=(total (original U) (probe t a)).part full-
      (dose U)*(total (Poly.pass (bare lamps fired U)) (probe t a)).part full) ∧
    let X:=lowered R simple A hk D Q π Γ Ψ books hi ahead school o P hearing J axes t a blankBill markBill
    RG.Envelope X ∧ ∀ j (age:j ≤ i),(∫ U,‖actualTransport R.family (N:=i+2) X age U‖
      ∂scene R.family.path (i+2) per j)≤‖((a:ℂ)⁻¹)‖*(2*(price p α))

include course in
theorem by_table (p:ℕ) (t:(faces).Mode) (live:t≠(faces).quiet)
    (a:ℝ) (apos:0<a) (fee₀:Poly.toll (weights) t*‖(a:ℂ)‖≤1)
    (ref:∀v,R.family.ref ((ids) v) ≤ i+2) (y:Site (R.family.side i per)) (α:ℝ)
    (filed:∀q:Poly (faces),Poly.price (weights) (inverseMass q)≤C₃ →
      WilsonThermometerRegisteredPlantedReturn.Report R simple A hk D Q π Γ Ψ books hi ahead school o P hearing J axes p q y α) :
    Capture R simple A hk D Q π Γ Ψ books hi ahead school o P hearing J axes p t a y α :=by
  have paidG : 0<gf:=(congrArg Coat.gStep (course.1.walk (i+1) (Nat.le_succ_of_le hi) (cut)).beta) ▸ P.issued.Waffle.soon.1
  have caps:=WilsonThermometerRegisteredFaceTable.fixed (weights) (fun v=>mul_pos paidG (P.salary.positive v))
    t live (a:ℂ) fee₀
  obtain ⟨blankBill,f₀,z₀,x₀,baseField,F₀,M₀,E₀⟩:=filed 1 caps.1
  obtain ⟨markBill,f₁,markCost,x₁,markField,markOwner,markEnvelope,markPrice⟩:=filed _ caps.2
  refine ⟨blankBill,markBill,?_,baseField,markField,?_⟩
  · intro c member
    rcases Set.mem_insert_iff.mp member with eq|eq
    · rcases eq with rfl;exact ⟨f₀,z₀,x₀,F₀⟩
    · rcases Set.mem_singleton_iff.mp eq with rfl;exact ⟨f₁,markCost,x₁,markOwner⟩
  · have blankBilla:=E₀ i (le_refl i)
    have markBilla:=markPrice i (le_refl i)
    simp only [actualTransport_base R.family R.makes (cut).le] at blankBilla markBilla
    rw [adjusted R simple A hk D Q π Γ Ψ books hi ahead school o P hearing J axes t live a apos ref blankBill markBill]
    exact difference R (cut).le _ _ markEnvelope M₀ _ markBilla blankBilla _

include course in
theorem selected (p:ℕ) (t:(faces).Mode) (live:t≠(faces).quiet)
    (ref:∀v,R.family.ref ((ids) v) ≤ i+2) (y:Site (R.family.side i per)) (α:ℝ)
    (filed:∀q:Poly (faces),Poly.price (weights) (inverseMass q)≤C₃ →
      WilsonThermometerRegisteredPlantedReturn.Report R simple A hk D Q π Γ Ψ books hi ahead school o P hearing J axes p q y α) :
    Capture R simple A hk D Q π Γ Ψ books hi ahead school o P hearing J axes p t (sensitivity t) y α :=by
  have gp:0<gf:=(congrArg Coat.gStep (course.1.walk (i+1) (Nat.le_succ_of_le hi) (cut)).beta) ▸ P.issued.Waffle.soon.1
  have positive (v):(0:ℝ)<(weights) v:=mul_pos gp (P.salary.positive v)
  have toll:=Poly.worth positive t
  have large:0<1+Poly.toll (weights) t:=by linarith
  have rad:0<(sensitivity t):=inv_pos.mpr large
  apply by_table R simple A hk D Q π Γ Ψ course books hi ahead school o P hearing J axes p t live
    (sensitivity t) rad _ ref y α filed
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos rad]
  change Poly.toll (weights) t*(1+Poly.toll (weights) t)⁻¹≤1
  rw [←div_eq_mul_inv,div_le_one large]
  linarith

include course in
theorem by_unit (p:ℕ) (t:(faces).Mode) (live:t≠(faces).quiet)
    (capped:∀v,P.w v≤1) (ref:∀v,R.family.ref ((ids) v) ≤ i+2) (y:Site (R.family.side i per)) (α:ℝ)
    (filed:∀q:Poly (faces),Poly.price (weights) (inverseMass q)≤C₃ →
      WilsonThermometerRegisteredPlantedReturn.Report R simple A hk D Q π Γ Ψ books hi ahead school o P hearing J axes p q y α) :
    Capture R simple A hk D Q π Γ Ψ books hi ahead school o P hearing J axes p t 1 y α :=by
  have beta:=congrArg Coat.gStep (course.1.walk (i+1) (Nat.le_succ_of_le hi) (cut)).beta
  have gp:0<gf:=beta ▸ P.issued.Waffle.soon.1
  have small:gf≤1:=beta ▸ P.issued.Waffle.soon.2.1
  have toll:Poly.toll (weights) t≤1:=by
    apply Finset.prod_le_one
    · intro v _;exact (mul_pos gp (P.salary.positive v)).le
    · intro v _;exact (mul_le_of_le_one_right gp.le (capped v)).trans small
  exact by_table R simple A hk D Q π Γ Ψ course books hi ahead school o P hearing J axes p t live 1 zero_lt_one
    (by simpa using toll) ref y α filed

include course in
theorem on_post {η:ℝ} {T:Campaign R} {W:Campaign.Pillars R T}
    (funded:FundedOriginalProperties.{u} simple η W)
    (slow:WilsonWindowReportingPace.Slow R.kit)
    (clear:Clear G J) {ε:ℝ} (ep:0<ε) (modest:ε ≤ (1:ℝ)/4) (p:ℕ)
    (reserve:(p+1)+247 ≤ hearing)
    (law:VowsR.LawScroll G φ) (enrolled:VowsR.Chamber law R.kit D Q books)
    (fund:Volume.Fund D R.rolls Q φ books R.alloy.delay)
    (late:max (WilsonJointAxialRoster.opening R simple funded slow.2 J clear (Fintype.card (Fin 3)) n hearing ep)
        (WilsonReceivedAxialFiling.opening R simple D φ width school.order school.horizon (Fintype.card (Fin 3)) ep) ≤ i)
    (finiteLate:max (WilsonReceivedAxialFinite.opening R simple hearing ep)
        (WilsonReceivedAxialFinite.massOpening R D levels school.order school.horizon school.pieces (k:=k) simple width) ≤ i)
    (clockLate:(eventually_atTop.mp (WilsonJointAxialClock.original R simple)).choose ≤ i)
    (pass:Pass D Q R.alloy R.kit)
    (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (fit:k ≤ stage) (visible:WilsonThermometerRegisteredAllStation.Visible R simple A hk D Q π Γ Ψ books
      school o ahead hi P hearing ε)
    (t:(faces).Mode) (live:t≠(faces).quiet)
    (fraction:ε*(3^hearing+2) ≤ 1) (gate:WilsonReportingForestAngularReflection.posted R)
    (rareLate:WilsonJointAxialScalar.opening (V:=Fin 3) R simple gate hearing n (p+161+2*n*3) ≤ i)
    (F:Forest (R.family.path.levels.clock.op i per).ratio) (tag:(R.family.path.levels.clock.op i per).Choices)
    (way:WayStation R.kit) (station:WilsonCenteredCaptureClock.first R simple ≤ i) (sec:R.t 0 ≤ i)
    (ready:WilsonReportLampForecast.Ready R.family.path.levels)
    (early:(eventually_atTop.mp (WilsonCenteredReporterClock.original R simple slow.2 ready)).choose ≤ i)
    (haloPay:(eventually_atTop.mp (WilsonRootedKioskPostRadius.original R simple)).choose ≤ i)
    (force:hearing ≤ stage) (deep:2*(hearing+1)+8 ≤ school.order) (aged:hearing+4≤3*k+2)
    (opened:WilsonThermometerFullSignedAppointment.gate R simple school hearing deep aged ≤ i)
    (saved:(eventually_atTop.mp (WilsonFullFaceSignedReserved.original R simple hearing)).choose ≤ i)
    (ref:∀v,R.family.ref ((ids) v) ≤ i+2)
    (y:Site (R.family.side i per)) (Z:Support (R.family.side i per)) (center:y∈Z)
    (taken:∀v:Fin 3,(placed).origin v∈Z) (rad:ℕ) (near:∀v:Fin 3,separation ((placed).origin v) y ≤ rad)
    (radius:rad ≤ (Ψ i).p.B) (box:Z⊆halo (Ψ i).p.B {y}) (α:ℝ) (strength:(Ψ i).p.supportExponent ≤ α) :
    Capture R simple A hk D Q π Γ Ψ books hi ahead school o P hearing J axes p t (sensitivity t) y α :=by
  apply selected R simple A hk D Q π Γ Ψ course books hi ahead school o P hearing J axes p t live ref y α
  intro q paid
  exact WilsonThermometerRegisteredPlantedReturn.on_post R simple A hk D Q π Γ Ψ course books hi ahead school o P
    hearing J axes width funded slow clear ep modest p reserve law enrolled fund late finiteLate clockLate pass hospital fit
    visible q paid fraction gate rareLate F tag way station sec ready early haloPay force deep aged opened saved ref y Z center
    taken rad near radius box α strength

include course in
theorem literal {η:ℝ} {T:Campaign R} {W:Campaign.Pillars R T}
    (funded:FundedOriginalProperties.{u} simple η W)
    (slow:WilsonWindowReportingPace.Slow R.kit)
    (clear:Clear G J) {ε:ℝ} (ep:0<ε) (modest:ε ≤ (1:ℝ)/4) (p:ℕ)
    (reserve:(p+1)+247 ≤ hearing)
    (law:VowsR.LawScroll G φ) (enrolled:VowsR.Chamber law R.kit D Q books)
    (fund:Volume.Fund D R.rolls Q φ books R.alloy.delay)
    (late:max (WilsonJointAxialRoster.opening R simple funded slow.2 J clear (Fintype.card (Fin 3)) n hearing ep)
        (WilsonReceivedAxialFiling.opening R simple D φ width school.order school.horizon (Fintype.card (Fin 3)) ep) ≤ i)
    (finiteLate:max (WilsonReceivedAxialFinite.opening R simple hearing ep)
        (WilsonReceivedAxialFinite.massOpening R D levels school.order school.horizon school.pieces (k:=k) simple width) ≤ i)
    (clockLate:(eventually_atTop.mp (WilsonJointAxialClock.original R simple)).choose ≤ i)
    (pass:Pass D Q R.alloy R.kit)
    (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (fit:k ≤ stage) (visible:WilsonThermometerRegisteredAllStation.Visible R simple A hk D Q π Γ Ψ books
      school o ahead hi P hearing ε)
    (t:(faces).Mode) (live:t≠(faces).quiet) (capped:∀v,P.w v≤1)
    (fraction:ε*(3^hearing+2) ≤ 1) (gate:WilsonReportingForestAngularReflection.posted R)
    (rareLate:WilsonJointAxialScalar.opening (V:=Fin 3) R simple gate hearing n (p+161+2*n*3) ≤ i)
    (F:Forest (R.family.path.levels.clock.op i per).ratio) (tag:(R.family.path.levels.clock.op i per).Choices)
    (way:WayStation R.kit) (station:WilsonCenteredCaptureClock.first R simple ≤ i) (sec:R.t 0 ≤ i)
    (ready:WilsonReportLampForecast.Ready R.family.path.levels)
    (early:(eventually_atTop.mp (WilsonCenteredReporterClock.original R simple slow.2 ready)).choose ≤ i)
    (haloPay:(eventually_atTop.mp (WilsonRootedKioskPostRadius.original R simple)).choose ≤ i)
    (force:hearing ≤ stage) (deep:2*(hearing+1)+8 ≤ school.order) (aged:hearing+4≤3*k+2)
    (opened:WilsonThermometerFullSignedAppointment.gate R simple school hearing deep aged ≤ i)
    (saved:(eventually_atTop.mp (WilsonFullFaceSignedReserved.original R simple hearing)).choose ≤ i)
    (ref:∀v,R.family.ref ((ids) v) ≤ i+2)
    (y:Site (R.family.side i per)) (Z:Support (R.family.side i per)) (center:y∈Z)
    (taken:∀v:Fin 3,(placed).origin v∈Z) (rad:ℕ) (near:∀v:Fin 3,separation ((placed).origin v) y ≤ rad)
    (radius:rad ≤ (Ψ i).p.B) (box:Z⊆halo (Ψ i).p.B {y}) (α:ℝ) (strength:(Ψ i).p.supportExponent ≤ α) :
    Capture R simple A hk D Q π Γ Ψ books hi ahead school o P hearing J axes p t 1 y α :=by
  apply by_unit R simple A hk D Q π Γ Ψ course books hi ahead school o P hearing J axes p t live capped ref y α
  intro q paid
  exact WilsonThermometerRegisteredPlantedReturn.on_post R simple A hk D Q π Γ Ψ course books hi ahead school o P
    hearing J axes width funded slow clear ep modest p reserve law enrolled fund late finiteLate clockLate pass hospital fit
    visible q paid fraction gate rareLate F tag way station sec ready early haloPay force deep aged opened saved ref y Z center
    taken rad near radius box α strength

end YM.Integration.WilsonThermometerRegisteredFacePair
