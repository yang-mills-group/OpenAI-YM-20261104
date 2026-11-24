import YM.Integration.WilsonPositionSeparatedProfileMayerInitialLogCohort
import YM.Integration.WilsonPositionSeparatedProfileMayerInitialLogFiling

/-! The whole authentic initial source on one and the same registered finite group field. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileMayerInitialLogRegistered
open Function Filter Lattice Wilson RG Precision Tree Marker Multi Exterior
open PhysicalNext.Repeat.Legato LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep IterationFour IterationFour.Vacuum
open Comparison.RG02 Comparison.RG02.Order Comparison.RG02.Actual Pert.Asymptotics WilsonLimitConstruction
open scoped Classical Topology BigOperators

variable {G:Gauge} {B:MS.Local.Physical.Deck G} {V:Type} [DecidableEq V] [Fintype V]
  (R:Run G) (hG:G.Simple) (u:V→MS.Rake.Label B) (J:Request V) (A:NumericSchedule R.family J)
  (d:LocalFormal.Datum R.family (Stock.census V)) (Q:MS.Land.Prescription B)
  (o:V→Site (R.family.side (d.level+1) d.period)) (μ:ℝ) (orders:V→ℕ)
  (profile:∀k,k≤(R.metals.p.profile k).order ∧ k≤(R.metals.p.profile k).power)
  (hm:ActualOriginalQInitialInput.start R hG u J A profile≤d.level)
  (hp:(ActualOriginalQPointSetup.request R u J).physicalPeriodLower≤(R.family.S.period d.period).val)
local notation "J₀" => ActualOriginalQPointSetup.request R u J
local notation "W" => FundedMatchedPointOpening.colors R hG u J A d Q o μ orders profile hm hp
local notation "K" => (RunFormalChain.fromRun R).step (d.level+1) d.level d.period (Nat.lt_succ_self _)
local notation "S" => R.family.path.levels.clock.op d.level d.period

local notation "D" => ActualOriginalQPointSetup.pointDatum R J d.period (d.level+1) o
local notation "clock₀" => μ-R.family.S.scale d.cutoff
open FVA2.CityHistory RGComparison.Core16

open FormalOPE.RG10 FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Splice

local notation "g₀" => regulatorRun R.family (d.level+1) d.period (d.level+1)

open WilsonMatrixTicketLanesReportedPrepaid WilsonPositionSeparatedProfileMayerInitialLogCohort
local notation "Γ" => Stock.census V

theorem entered (paid:Paid G R.kit) (top:d.cutoff=d.level+1) (t:TestSpace (J₀).tests)
    (F:Forest (S).ratio) (tag:(S).Choices) (a:fieldDir G (R.family.side d.level d.period) 1)
    (cap K₀ guard E n:ℕ) (C:ℝ) (cp:0≤C) (limits:∀i,orders i≤K₀)
    (inside:∀i,‖Exterior.collect G a i‖≤(cap:ℝ)+1)
    (degree:∀(s:(Γ).Mode)(z:∀i,WilsonMatrixTicketLanesTerminalQWords.Piece R (roster u s i)),
      Spool.power (WilsonMatrixTicketLanesTerminalQWords.word R (roster u s) z)≤n)
    (window:∀s:(Γ).Mode,Window R Q (roster u s) K₀ cap guard E n μ C d.level):
    let reader:=WilsonPositionSeparatedProfileMayerInitialThermalWords.reader R hG u J A d Q o μ orders t
    let w:=WilsonPositionSeparatedProfileMayerInitialLogWeights.weight reader
    let x:=Bulk.Fk (K) F tag (W t) a n
    let f:=Order.unitScale (Bare.realMoment (K) F (W t) tag a (g₀))
    (∀s:(Γ).Mode,Poly.toll w s*‖(f-Order.value ((g₀):ℂ) (Order.ratio x)).part s‖≤(g₀)^guard) ∧
    ∀j≤n,∀s:(Γ).Mode,Poly.toll w s*‖Laplace.detail (Order.ratio x) s j‖≤C/(g₀)^E:=by
  classical
  intro reader w x f
  let nt:(Descent.nil (top:=R.family.side (d.level+1) d.period)).Tags:=()
  let large:Bid.Larger (G:=G) (S):=paid.1 d.level d.period
  have gp:0<(g₀):=IterationFour.Currency.g_pos R.makes _ _ _ le_rfl
  have amounts (s:(Γ).Mode):
      let e:=enumerate s
      let rd:=fun i=>reader (e i).val
      let sites:=fun i=>ActualRunQlocalNativeTuple.root (D) (e i).val
      let ordersₛ:=fun i=>orders (e i).val
      let pin:=Exterior.collect G a
      (‖f.part s-(Order.value ((g₀):ℂ) (Order.ratio x)).part s‖≤
         (g₀)^guard*(∏i,‖rd i‖)) ∧
      ∀j≤n,(g₀)^E*‖Laplace.detail (Order.ratio x) s j‖≤C*(∏i,‖rd i‖):=by
    intro e rd sites ordersₛ pin
    have invoice:=window s d.period ordersₛ (fun i=>limits _) rd large F pin sites tag nt inside
    constructor
    · dsimp only [x,f]
      rw [WilsonPositionSeparatedProfileMayerInitialThermalDisplay.measured R hG u J A d Q o μ orders
        profile hm hp t F tag a s e,
        WilsonPositionSeparatedProfileMayerInitialThermalDisplay.filed R hG u J A d Q o μ orders profile hm hp t
          F tag a s e n (R.family.path.levels.budget (d.level+1)) large ((cap:ℝ)+1)
          (by positivity) inside nt (degree s),top]
      exact invoice.1
    · intro j hj
      dsimp only [x]
      rw [WilsonPositionSeparatedProfileMayerInitialLogFiling.coefficient R hG u J A d Q o μ orders
        profile hm hp t F tag a s e n (R.family.path.levels.budget (d.level+1)) large
        ((cap:ℝ)+1) (by positivity) inside nt j hj,top]
      exact invoice.2 j hj
  have wp:=WilsonPositionSeparatedProfileMayerInitialLogWeights.positive reader
  constructor
  · intro s
    have tariff:=WilsonPositionSeparatedProfileMayerInitialLogWeights.paid reader s (enumerate s)
    rw [Extra.Trajectories.part_sub]
    calc
      _≤Poly.toll w s*((g₀)^guard*(∏i,‖reader ((enumerate s) i).val‖)):=
        mul_le_mul_of_nonneg_left (amounts s).1 (Poly.worth wp s).le
      _=(g₀)^guard*(Poly.toll w s*(∏i,‖reader ((enumerate s) i).val‖)):=by ring
      _≤_:=mul_le_of_le_one_right (pow_nonneg gp.le _) tariff
  · intro j hj s
    have tariff:=WilsonPositionSeparatedProfileMayerInitialLogWeights.paid reader s (enumerate s)
    apply (le_div_iff₀ (pow_pos gp _)).2
    calc
      _=Poly.toll w s*((g₀)^E*‖Laplace.detail (Order.ratio x) s j‖):=by ring
      _≤Poly.toll w s*(C*∏i,‖reader ((enumerate s) i).val‖):=
        mul_le_mul_of_nonneg_left ((amounts s).2 j hj) (Poly.worth wp s).le
      _=C*(Poly.toll w s*∏i,‖reader ((enumerate s) i).val‖):=by ring
      _≤_:=mul_le_of_le_one_right cp tariff

end YM.Integration.WilsonPositionSeparatedProfileMayerInitialLogRegistered
