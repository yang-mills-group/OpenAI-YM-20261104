import YM.Integration.WilsonOriginalTwoFlatRoseMerWage
import YM.Integration.WilsonOriginalTwoFlatRoseMerAssessed
import YM.Integration.WilsonOriginalTwoFlatRoseVariation
import YM.Integration.WilsonOriginalTwoFlatRoseMerRoster
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatRoseCellSum
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor QuadraticLocal.Affinity Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open Push Push.PriceCompiler Push.AbsoluteSums Stationary Comparison.RG02 QuadraticLocal.Rebirth
open VowsR LocalComparison ConnectedActivityE6
open scoped Classical BigOperators

variable {G:Gauge} (R:Run G) (simple:G.Simple) {m i N per k:ℕ}
  (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
  (π:ℕ → Layout G) (Γ:ℕ → Pace.Coin) (Ψ:∀ j, RG.Rep G (R.family.side j per))
  (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ:ℕ → ℕ} (scroll:LawScroll G φ) (books:Mentor.Offices.Books D R.rolls Q φ)
  (hi:m ≤ i) (cut:i < N)
  (op:Mentor.Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i))
  (lesson:Lesson (N:=N) R hk D Q π Γ hi)
  (cal:Oak.Calendar R hk D Q π Γ Ψ hi (N:=N) lesson)
  (ahead:Mentor.Forecast D R.rolls Q φ books)
  (chamber:VowsR.Chamber scroll R.kit D Q books)
  (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)

open WilsonOriginalMixedBlockRows WilsonRegisteredPairUnaryWallet Filter MintClock Multi
local notation "H" => Ψ (i+1)
local notation "σ₀" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))


open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Soil FundedMarkedPathSelection WilsonOlderFreshConnectedRobe
open WilsonOriginalCollarElection WilsonIndependentCollarCensusCourse WilsonReceivedCanonicalVerseBasis
open WilsonThermometerDeclaredSeeds WilsonReceivedFixedDigitHistory WilsonIndependentCollarAddressedSource
open WilsonOriginalCensusDatedMaterial (Material)
open WilsonOriginalCensusFaceSites (binder port)
open Pert.Asymptotics
open WilsonOriginalTwoFlatIRFlatEarned (whole)
open WilsonOriginalTwoFlatIRFlatMarked (seat)
open WilsonOriginalTwoFlatIRFlatPaidParts (wage)
open WilsonOriginalTwoFlatIRFlatPartitions (crop)
open WilsonOriginalTwoFlatIRFlatMeasured (cash)
open WilsonReceivedChronologicalMaterialEndpoint (submitted)


open WilsonReceivedCanonicalVersePortfolio (Selection)
open WilsonReceivedCanonicalVerseWeighted (full)
open WilsonOriginalMicroscopicEntranceGridRow (pin)
open WilsonReceivedChronologicalBasis (fare)
open WilsonIndependentCollarDatedPrior (onLevels)
variable {f n cap q:ℕ}(grades axis:Fin 3→ℕ){V:Realm G (q+1) Credit.leanC}{draw:V.draws=R.family.path.levels}
    {rate δ:ℝ}(κ:(v:Fin 3)→Knob (axis v))(pt:Fin 3→WilsonCoeffUV.Embroider.Chamber)
    (o:Fin 3→Site (R.family.side f per))(upper:f+n≤N)(t:WilsonCoeffUV.Wheel.Case axis)
local notation "J" => Stock.census (Fin 3)
local notation "age" => i+1
local notation "g" => regulatorRun R.family N per (age)
local notation "side" => R.family.side (age) per
local notation "seats" => Hot (J)
local notation "D₀" => (∑v:Fin 3,grades v)+1
local notation "room" => WilsonOriginalMixedBlockRows.room (Fin 3)
local notation "top" => f+n
local notation "high" => (Nat.le_add_right f n).trans upper
local notation "sitesN" => pin R (high) o


open WilsonReceivedChronologicalMaterialRoster (Filed)
open WilsonOriginalTwoFlatRoseFixedFiles (site cells retained)
open WilsonOriginalMicroscopicEntranceGridRow (pin)
open Function Finset Lattice Laurent Wilson RG Precision Tree Exterior Bloch Matrix PowerSeries
open PhysicalNext.Repeat.Legato FreeResolvent WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Motion WilsonCoeffUV.Embroider WilsonCoeffUV.Soil Stationary WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank.Mosaic.Near
open OriginalMarkedSourceComet IndependentSourcePathFamily
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner


open Pert.Asymptotics MeasureTheory Source Labels Extra.Histories RG16.Literal
open WilsonMaxwellThermometerNominatedCofactor (native)
open WilsonThermometerAlignedCells (atOrigin)
open WilsonNeutralOffsetCutoff (named)
open WilsonOriginalTwoFlatRoseIdentity (entry cross)
open WilsonOriginalTwoFlatGridScaling (gap)
open WilsonThermometerUnitFilingFlatTelescope (numerator feeAt)

local notation "home" s:max => site R o upper cut s
local notation "ports" => fun (s:(J).Mode)(_y:Selection R grades s.val)=>port (side) (home s)
local notation "binders" => fun (s:(J).Mode)(_y:Selection R grades s.val)=>binder (side) (home s)
local notation "restore" => cells R (draw:=draw) o upper
local notation "FC" => Finset (Fin 3)
variable (M:∀(s:(J).Mode)(_y:Selection R grades s.val),Material R N (i+1) q grades
      (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1)))
      (binder (R.family.side (i+1) per) (site R o upper cut s)))
    (xx:(s:(J).Mode)→Wallet (room))
    (v:∀a:Fin 3,R.family.label (grades a))(c:Fin 3→ℂ)
    (previous:∀(s:(J).Mode)(_y:Selection R grades s.val),∀j:ℕ,Config G (R.family.side j per)→Poly (J))
    (A₀:WilsonPositionThermometerCapStation.Group R.family 6)
local notation "x" => fun (s:(J).Mode)(_y:Selection R grades s.val)=>xx s
local notation "records" => fun (s:(J).Mode)(y:Selection R grades s.val)=>
  WilsonReceivedChronologicalMaterialEndpoint.submitted R (N:=N) (i:=i) (per:=per) (k:=k) (n:=3) (I:=seats) D Ψ
    ((ports) s y) ((binders) s y) grades q (M s y) (x s y)
local notation "rows" => WilsonReceivedChronologicalSocketMix.stock R grades (day:=i+1) (records) previous
local notation "wallet" => fare R grades v c N per (top)
local notation "stamped" => WilsonReceivedChronologicalMixture.mix R (wallet) (rows)
local notation "programme" => WilsonReceivedChronologicalPlant.rows R grades (n:=n) (N:=N) o v c (stamped)
local notation "held" T:max => WilsonReceivedChronologicalReadout.face R N per (programme) (seat T)
local notation "pairAt" => (pin R (high) o 1,pin R (high) o 2)
local notation "phys" T:max => WilsonOriginalTwoFlatRoseNominated.face (N:=N) (per:=per) R A₀ (pairAt) T
local notation "physical" => fun s:FC=>R.family.omega N per (phys s)
local notation "readAt" => WilsonMaxwellThermometerNominatedCofactor.reading R A₀ N per (pairAt) (native R A₀ N per (pairAt) 0)
local notation "trueAt" a:max s:max => retained R (cap:=cap) (draw:=draw) cut grades axis κ pt o upper t x v c a (seat s)
local notation "nativeAt" a:max s:max => WilsonOriginalTwoFlatIRFlatChronicle.total R D (f:=f) (n:=n) grades v c (ports) (binders) q M x a (seat s)
local notation "gross" s:max => WilsonOriginalTwoFlatIRFlatChronicle.salary R D (f:=f) (n:=n) grades v c (ports) (binders) q M x (seat s)
local notation "charge" a:max s:max => WilsonMaxwellThermometerNominatedSecant.bill (physical) (fun z=>trueAt a z) s
local notation "invoice" u:max uc:max vc:max ck:max s:max =>
  gap R N per u (((uc).trans (ck)).trans upper) (phys s)+entry R ((uc).trans (ck)) upper (phys s) (held s)+
  (∑j∈Ico cap (top),feeAt R N per u (held s) j)+cross R (N:=N) uc vc (held s)+
  (∑j∈Ico (age) cap,feeAt R N per (age) (held s) j)


open WilsonOriginalTwoFlatRoseMerWage (factor variation)
open WilsonOlderFreshSoftSocketRestored (degree)
local notation "weights" T:max => variation R (f:=f) (n:=n) (N:=N) (per:=per) grades v c (seat T)
local notation "printed" => factor R (i:=i) (q:=q) (δ:=δ) (rate:=rate) grades axis t
local notation "trueFigure" s:max p:max =>
  WilsonOriginalTwoFlatRoseMerFigure.figure R (i:=i) (cap:=cap) (draw:=draw) κ pt o upper cut t xx v c (seat s) p (g)
local notation "costFigure" s:max p:max =>
  WilsonOriginalTwoFlatRoseMerFigure.expense R (i:=i) (cap:=cap) (draw:=draw) κ pt o upper cut t xx v c (seat s) p (g)
local notation "chargeFigure" s:max p:max => WilsonMaxwellThermometerNominatedSecant.bill
  (physical) (fun s:FC=>trueFigure s p) s
local notation "hasPoles" p:max => ∀(s:FC)(y:Selection R grades s),degree R grades s (full R grades y)≤p


open Pert.Asymptotics
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Bank.Mosaic.Near
local notation "assessed" s:max p:max target:max E:max B:max =>
  WilsonOriginalTwoFlatRoseMerRoster.charge R (N:=N) (per:=per) (i:=i) (f:=f) (n:=n) t xx v c
    (seat s) p target E B


/-- One filed original Rose node.  Its debit keeps the two held flat readings,
all true dated charges, and the income of every occupied mark exactly once. -/
structure Sale (O:FC→ℂ)(reading:ℂ) where
  table : FC → ℂ
  debit : FC → ℂ
  wage : FC → ℝ
  bound : ‖reading-WilsonPositionThermometerConnected.value table-
    ∑s:FC,WilsonMaxwellThermometerNominatedSecant.bill O table s*debit s‖≤
    ∑s:FC,‖WilsonMaxwellThermometerNominatedSecant.bill O table s‖*wage s

include simple course cut in
def issued (old:age<top)(order shelf:ℕ)(income:Fin 3→ℝ)(tol:ℝ)
    (posted:∀s y,WilsonOriginalCensusMaterialPosting.Posted R hk D Q π Γ Ψ books hi op lesson ahead
      ((ports) s y) ((binders) s y) grades order shelf q income (M s y) tol)
    (filed:∀s y,Filed (K:=top) (draw:=draw) (rate:=rate) (δ:=δ) (restore)
      κ pt (full R grades y) (side) (home s) t (M s y))
    {u:ℕ}(uc:u≤cap)(vc:age≤cap)(ck:cap≤top)
    (reg:∀s:FC,∀j:ℕ,min u (age)≤j→j≤top→Integrable (numerator R N per j ((held s) j)) (prior G _))
    (ratio:LocalRatio R.metals.O)(hg:0≤g)(small:g≤1)(p:ℕ)(bound:p≤q)(kept:hasPoles p)
    (target capDebt:ℕ)(W:Realm G (p+1) Credit.leanC)
    (board:W.draws=R.family.path.levels)(paid:W.paid=R.metals.O)
    (dorm:∀s:FC,s≠∅→Dormitory W (WilsonCoeffUV.Wheel.Mark.mass grades s) 0 Credit.leanC)
    (atW:W.anchor≤age)(E B:ℝ)(first:PadRank W cap (top) E)(second:PadRank W (age) cap B)
    (warm:regulatorRun R.family N per (top)≤1)
    (clock:WilsonOriginalTwoFlatRoseMerClock.Charged R N per (age) (top) p target capDebt)
    (bought:hasPoles capDebt):
    Sale (physical) (readAt) where
  table:=fun s=>trueFigure s p
  debit:=fun s=>invoice u uc vc ck s
  wage:=fun s=>g^(p+1)*((weights s)*(printed))+assessed s p target E B
  bound:=WilsonOriginalTwoFlatRoseMerAssessed.original R simple hk D Q π Γ Ψ course books hi cut op lesson ahead
    grades axis κ pt o upper t M xx v c previous A₀ old order shelf income tol posted filed uc vc ck reg ratio
    hg small p bound kept target capDebt W board paid dorm atW E B first second warm clock bought

section Tested
variable (φ:Test 3)(r:ℝ)(fine:f≤N)
local notation "SiteF" => Site (R.family.side f per)
local notation "Jumps" => SiteF × SiteF
local notation "sample" y:max => fun a:Fin 3=>WilsonThermometerAlignedCells.atOrigin y a
local notation "pins" y:max => WilsonOriginalMicroscopicEntranceGridRow.pin R fine (sample y)
local notation "offsets" y:max => ((pins y) 1,(pins y) 2)
local notation "μ" y:max => WilsonThermometerAlignedCells.mass (R:=R) r (f,per) φ y
local notation "observed" y:max => fun s:FC=>R.family.omega N per (WilsonOriginalTwoFlatRoseNominated.face R A₀ (offsets y) s)
local notation "readNode" y:max => WilsonMaxwellThermometerNominatedCofactor.reading R A₀ N per (offsets y)
  (WilsonMaxwellThermometerNominatedCofactor.native R A₀ N per (offsets y) 0)
local notation "Valid" => {y:Jumps // μ y≠0}

def residual {O:FC→ℂ}{a:ℂ}(s:Sale O a):ℂ:=
  a-WilsonPositionThermometerConnected.value s.table-
    ∑t:FC,WilsonMaxwellThermometerNominatedSecant.bill O s.table t*s.debit t

def cost {O:FC→ℂ}{a:ℂ}(s:Sale O a):ℝ:=
  ∑t:FC,‖WilsonMaxwellThermometerNominatedSecant.bill O s.table t‖*s.wage t

/-- The signed finite source has the one common translation weight at the public
mesh.  Only its nonempty-weight cells call their genuine node financing. -/
theorem tested (sale:∀y:Valid,Sale (observed y.val) (readNode y.val)):
    ‖∑y:Valid,(μ y.val)*residual (sale y)‖≤∑y:Valid,‖μ y.val‖*cost (sale y):=by
  apply (norm_sum_le ..).trans
  apply sum_le_sum
  intro y _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (sale y).bound (norm_nonneg _)

theorem original (sale:∀y:Valid,Sale (observed y.val) (readNode y.val))
    (B:ℝ)(nonneg:0≤B)(each:∀y,cost (sale y)≤B):
    ‖∑y:Valid,(μ y.val)*residual (sale y)‖ ≤ (∫z:Points 3,‖φ z‖)*B:=by
  apply (tested R A₀ φ r fine sale).trans
  calc
    _≤∑y:Valid,‖μ y.val‖*B:=sum_le_sum fun y _=>mul_le_mul_of_nonneg_left (each y) (norm_nonneg _)
    _=(∑y:Valid,‖μ y.val‖)*B:=(sum_mul ..).symm
    _≤_:=by
      apply mul_le_mul_of_nonneg_right _ nonneg
      apply le_trans _ (WilsonThermometerAlignedCells.variation (R:=R) r (f,per) φ)
      let inclusion:Valid↪Jumps:=⟨Subtype.val,Subtype.val_injective⟩
      have reindex:(∑y:Valid,‖μ y.val‖)=∑z∈(univ:Finset Valid).map inclusion,‖μ z‖:=by
        rw [sum_map]
        rfl
      rw [reindex]
      exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun z _ _=>norm_nonneg _)
end Tested
end YM.Integration.WilsonOriginalTwoFlatRoseCellSum
