import YM.Integration.WilsonOriginalTwoFlatIRFlatChronicle
import YM.Integration.WilsonOriginalTwoFlatRoseNominated

/-! Physical seven-face reading on an aligned Rose node. At the moving
flat its target is the actual finite covered table of the filed chronological
source. The signed upper, all dated defects and the two true stop readings
remain on their original Wilson numerator. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatRoseFlatPrice
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

open WilsonReceivedCanonicalVersePortfolio (Selection)
open WilsonReceivedChronologicalMaterialEndpoint (submitted word)
open WilsonReceivedChronologicalBasis (fare)
open WilsonOriginalMicroscopicEntranceGridRow (pin)
variable {f n:ℕ}(d:Fin 3→ℕ)(o:Fin 3→Site (R.family.side f per))
  (v:∀a:Fin 3,R.family.label (d a))(c:Fin 3→ℂ)
local notation "age" => i+1
local notation "J" => Stock.census (Fin 3)
local notation "X" j:max => Config G (R.family.side j per)
local notation "A" => WilsonOriginalMixedBlockRows.room (Fin 3)
variable {ι:∀s:(J).Mode,Selection R d s.val→Type}
  [∀s y,Fintype (ι s y)]
  (ports:∀(s:(J).Mode)(_y:Selection R d s.val),Earn.Passport (R.family.side (i+1) per) (Fin 3))
  (B:∀s y,ι s y→Earn.Binder (ports s y) (J))
  (q:ℕ)(M:∀s y,WilsonOriginalCensusDatedMaterial.Material R N (i+1) q d
    (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))) (B s y))
  (x:∀(s:(J).Mode)(_y:Selection R d s.val),Wallet (A))
  (previous:∀(s:(J).Mode)(_y:Selection R d s.val),∀ j:ℕ,Config G (R.family.side j per)→Poly (Stock.census (Fin 3)))

local notation "records" => fun (s:(J).Mode)(y:Selection R d s.val)=>
  WilsonReceivedChronologicalMaterialEndpoint.submitted R (N:=N) (i:=i) (per:=per) (k:=k) (n:=3) (I:=ι s y) D Ψ (φ:=φ) (ports s y) (B s y) d q (M s y) (x s y)
local notation "rows" => WilsonReceivedChronologicalSocketMix.stock R d (day:=i+1) (records) previous
local notation "wallet" => fare R d v c N per (f+n)
local notation "stamped" => WilsonReceivedChronologicalMixture.mix R (wallet) (rows)
local notation "programme" => WilsonReceivedChronologicalPlant.rows R d (n:=n) (N:=N) o v c (stamped)



open Pert.Asymptotics MeasureTheory Source Labels Extra.Histories RG16.Literal
open WilsonMaxwellThermometerNominatedCofactor (native)
open WilsonThermometerAlignedCells (atOrigin)
open WilsonNeutralOffsetCutoff (named)
open WilsonOriginalTwoFlatRoseIdentity (entry cross)
open WilsonOriginalTwoFlatGridScaling (gap)
open WilsonThermometerUnitFilingFlatTelescope (numerator feeAt)
local notation "FC" => Finset (Fin 3)
private def seat (s:Finset (Fin 3)):(Stock.census (Fin 3)).Mode:=⟨s,mem_univ _⟩
local notation "finish" T:max => WilsonOriginalTwoFlatIRFlatLast.returned R D (f:=f) (n:=n) d v c ports B q M x (seat T)
local notation "held" T:max => WilsonReceivedChronologicalReadout.face R N per (programme) (seat T)
variable (upper:f+n≤N) (A₀:WilsonPositionThermometerCapStation.Group R.family 6)
local notation "high" => (Nat.le_add_right f n).trans upper
local notation "pairAt" => (pin R (high) o 1,pin R (high) o 2)
local notation "phys" T:max => WilsonOriginalTwoFlatRoseNominated.face (N:=N) (per:=per) R A₀ (pairAt) T
local notation "top" => f+n
local notation "readAt" => WilsonMaxwellThermometerNominatedCofactor.reading R A₀ N per (pairAt) (native R A₀ N per (pairAt) 0)


local notation "g" => regulatorRun R.family N per (age)
local notation "cutRow" p:max T:max => WilsonOriginalTwoFlatIRFlatChronicle.total R D (f:=f) (n:=n) d v c ports B q M x p (seat T)
local notation "cash" T:max => WilsonOriginalTwoFlatIRFlatChronicle.salary R D (f:=f) (n:=n) d v c ports B q M x (seat T)
local notation "physical" => fun s:FC=>R.family.omega N per (phys s)
local notation "charge" p:max s:max => WilsonMaxwellThermometerNominatedSecant.bill (physical) (fun t=>cutRow p t) s
local notation "invoice" u:max cap:max uc:max vc:max ck:max s:max =>
  gap R N per u (((uc).trans (ck)).trans upper) (phys s)+entry R ((uc).trans (ck)) upper (phys s) (held s)+
  (∑j∈Ico cap (top),feeAt R N per u (held s) j)+cross R (N:=N) uc vc (held s)+
  (∑j∈Ico (age) cap,feeAt R N per (age) (held s) j)

include course cut in
theorem original (old:age<top)(order shelf:ℕ)(income:Fin 3→ℝ)(tol:ℝ)
    (paid:∀s y,WilsonOriginalCensusMaterialPosting.Posted R hk D Q π Γ Ψ books hi op lesson ahead
      (ports s y) (B s y) d order shelf q income (M s y) tol)
    {u cap:ℕ}(uc:u≤cap)(vc:age≤cap)(ck:cap≤top)
    (registered:∀s:FC,∀j:ℕ,min u age≤j → j≤top →
       Integrable (numerator R N per j ((held s) j)) (prior G _))
    (hg:0≤g)(small:g≤1)(p:ℕ):
    ‖(readAt)-WilsonPositionThermometerConnected.value (fun s=>cutRow p s)-
      ∑s:FC,(charge p s)*(invoice u cap uc vc ck s)‖ ≤
      g^(p+1)*∑s:FC,‖charge p s‖*(cash s):=by
  rw [WilsonMaxwellThermometerNominatedCofactor.original,WilsonMaxwellThermometerNominatedSecant.signed,
    ←Finset.sum_sub_distrib,Finset.mul_sum]
  apply (norm_sum_le ..).trans (sum_le_sum _)
  intro s _
  have bridge:=WilsonOriginalTwoFlatRoseIdentity.figure R uc vc ck upper (phys s)
    (WilsonOriginalTwoFlatRoseNominated.paid R A₀ (pairAt) s) (held s) (registered s) (cutRow p s)
  have earned:=WilsonOriginalTwoFlatIRFlatChronicle.original R hk D Q π Γ Ψ course books hi cut op lesson ahead
    d o v c ports B q M x previous old order shelf income tol paid hg small p (seat s)
  change ‖(charge p s)*((physical) s-(cutRow p s))-(charge p s)*(invoice u cap uc vc ck s)‖≤_
  rw [←mul_sub,bridge,add_sub_cancel_left,norm_mul]
  exact (mul_le_mul_of_nonneg_left earned (norm_nonneg _)).trans_eq (by ring)

end YM.Integration.WilsonOriginalTwoFlatRoseFlatPrice
end
