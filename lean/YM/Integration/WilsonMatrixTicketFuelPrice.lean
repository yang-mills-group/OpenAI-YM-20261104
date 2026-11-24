import YM.Integration.WilsonMatrixTicketFuel
import YM.Integration.WilsonMatrixTicketCommonExpenses
import YM.OPE.Compatible.Eyrie.Ice

/-! Buy the retained quantitative frame, tower and null-field prices before
the final delay. The resulting licence can be cashed on every authentic
realization of the selected factor. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketFuelPrice
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext Roost Graces
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open OPE OPE.Owl Eyrie Bandage
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open WilsonLimitConstruction.FundedCompanySelection

variable {G:Gauge} {g:G.Simple} {s:Sheet G} {price:MapPrices} {H:Votive.Sponsor G}
  {K:Votive.Seasons H} {a:Axis} {X:Stroke.PriceBook (chart_ok G) K} {t:ℕ→ℕ}
  {U:Rolls (ThroughLaunch.raise s t)} {pad:Spells.Pad G}
  {desk:Desk (ThroughLaunch.raise s t) X a g}
  {A:Alloy (ThroughLaunch.bountyV s price t) U}

/-- All permitted finite native frame tests at this purchased beta threshold. -/
def Frozen (desk:Desk (ThroughLaunch.raise s t) X a g) (pad:Spells.Pad G)
    (ε:ℝ) (θ:Protection U) (V:Delays θ):Prop :=
  ∀ (i j r l : ℕ) (he : desk.cost l ≤ i), r ≤ i → i ≤ j →
    ∀ (x : ℝ), V.betaEntry j ≤ x →
      Freeze g pad (desk.stream l) he (s.profile i) (desk.OAuth l i he) (θ.theta i) ε x (rim i r)

structure Paid (desk:Desk (ThroughLaunch.raise s t) X a g) (pad:Spells.Pad G)
    (ε:ℝ) (books:Arms (M:=ThroughLaunch.bountyV s price t) U) (θ:Protection U) (V:Delays θ) :Prop where
  frame : BeatV desk pad θ books V
  tower : TowerCap (M:=ThroughLaunch.bountyV s price t) θ V
  nullField : Frozen desk pad ε θ V

/-- The three delay elections work together on the physical factor's predetermined books. -/
theorem buy (desk:Desk (ThroughLaunch.raise s t) X a g) (pad:Spells.Pad G)
    {ε:ℝ} (finance:Glacier (a:=a) g ε) (frame:FrameBill desk U)
    (books:Arms (M:=ThroughLaunch.bountyV s price t) U) (θ:Protection U) (V:Delays θ):
    ∃ W:Delays θ, DelayLe V W ∧ ∀ Y, DelayLe W Y → Paid desk pad ε books θ Y := by
  obtain ⟨W₁,h₁,hb⟩:=Rhythm desk pad θ books frame V
  obtain ⟨W₂,h₂,hc⟩:=TowerCap.grind θ W₁ (M:=ThroughLaunch.bountyV s price t)
  obtain ⟨W₃,h₃,hd⟩:=effort pad desk W₂ finance
  refine ⟨W₃,h₁.trans (h₂.trans h₃),?_⟩
  intro Y later
  exact ⟨hb Y (h₂.trans (h₃.trans later)),hc Y (h₃.trans later),hd Y later⟩

/-- A quantitative frame over the indicated family and the indicated physical factor. -/
structure Licence (g:G.Simple) (a:Axis) (ε:ℝ) {M:Metals G} {U₀:Rolls M.p}
    {B₀:Alloy M U₀} (F₀:Factor B₀) (family:Family G) where
  sheet : Sheet G
  price : MapPrices
  sponsor : Votive.Sponsor G
  season : Votive.Seasons sponsor
  ledger : Stroke.PriceBook (chart_ok G) season
  stages : ℕ→ℕ
  rolls : Rolls (ThroughLaunch.raise sheet stages)
  pad : Spells.Pad G
  desk : Desk (ThroughLaunch.raise sheet stages) ledger a g
  alloy : Alloy (ThroughLaunch.bountyV sheet price stages) rolls
  physical : FuelV g sheet price sponsor season a ledger stages rolls pad desk alloy
  factor_eq : HEq physical.cabinet F₀
  family_eq : physical.Holds = family
  frozen : Frozen desk pad ε alloy.θ alloy.delay

def Eligible (g:G.Simple) (a:Axis) (ε:ℝ) : Prediction G := fun {_} {_} {A₀} F₀ =>
  ∀ (y:ℕ→ℝ) (worth:Bid.Worth) (_:Bandage F₀ y worth) (history:Bolt A₀) (ref:ℕ→ℕ)
    (fields:∀ d N p, TransferData ((Labels.frames G).level d) (Issue.trail history) N p),
    Nest F₀ history →
    (Family.mk (Issue.trail history) (hol G) (Labels.frames G) (localSection G) ref fields).Makes →
    Nonempty (Licence g a ε F₀ (Family.mk (Issue.trail history) (hol G) (Labels.frames G) (localSection G) ref fields))

theorem deliver (F:Factor A) (tell:Votive.Lend s K) (large:∀ i,16 ≤ (U.L i).val)
    (kinetic:ThroughLaunch.Imperial (s:=s) H.X price H.l A.post A.B.a A.B.M A.B.kin)
    {ε:ℝ} (paid:Paid desk pad ε F.books A.θ A.delay) :
    Eligible g a ε F := by
  intro y worth band history ref fields nest makes
  let physical : FuelV g s price H K a X t U pad desk A :=
    ⟨y,worth,F,band,history,ref,fields,nest,makes,tell,large,kinetic,paid.frame,paid.tower⟩
  exact ⟨⟨s,price,H,K,X,t,U,pad,desk,A,physical,HEq.rfl,rfl,paid.nullField⟩⟩

theorem on_run {R:Run G} {g:G.Simple} {a:Axis} {ε:ℝ} (issued:Eligible g a ε R.kit) :
    Nonempty (Licence g a ε R.kit R.family) :=
  issued R.y R.w R.b R.T R.t R.stories R.tuning.receipts R.makes

end YM.Integration.WilsonMatrixTicketFuelPrice
