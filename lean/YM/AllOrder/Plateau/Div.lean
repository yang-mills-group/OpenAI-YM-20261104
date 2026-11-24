import YM.AllOrder.Plateau.Bank
import YM.AllOrder.Plateau.Stoke
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Plateau
open Function Filter Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure PhysicalNext Repeat Lapis Bid Planned.JetPort
open Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush Poll ConnectedActivityE6.Coat
open AbsoluteSums Fare Shellac Work.G05
open Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Sienna
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G: Gauge} {n : Side} {k j w N : ℕ}
variable {σ C Z β x₀:ℝ}
local notation "E"=>Positions (Primary n G)
section know
open Kinetic.Port
variable (P:Patch)(K:KernelChoices){a Λ:ℝ}
local notation "S[" n "]"=> dock P K n
variable (O:ChartRatio G)(hO:LocalRatio O)
set_option quotPrecheck false
local notation "L"=>P.L
variable (p q:Stage) (B:ℝ) (v:ℕ)
local notation "a₁"=>p.paths
local notation "a₂"=>q.paths
local notation "t'"=>q.width
local notation "p'"=>p.clip
local notation "q'"=>q.clip
open Further.PhysicalPeriodLimitF933 Macrame Shop
local notation "I"=>Ticket P K O p q B
local notation "R"=> (fun x:I=> x.north)
local notation "D₀"=> (fun x:I=> x.south)
local notation "Λ₀"=> (fun x:I=> x.paid)
local notation "G'"=> (fun x:I=> x.alpha)
variable (F:Folio P K O hO p q B N)
local notation "A"=> F.rooftop
local notation "H"=> F.well
local notation "δ"=> (fun i=>i.upCost)
local notation "ε₀"=> Chop.cost hG -- not here
local notation "Ξ"=> F.canvas
local notation "Y"=> (fun x:ℝ=> betaF G x P.L ^ Shop.air N)
local notation "X"=> (fun x:ℝ=> (Trio.paySide G P.L v x:ℝ))
-- post flags Cut.V 

def slenderK (x:ℝ)(j k:ℕ) :Prop:= ∀ (n:Side)(z:I)(β:ℝ),region G P.L v Λ₀ x (z,n,β) → Ad G P K n → ∀ (T:Tube G (dock P K n)), T.up=z.north → T.high=p.clip → T.down=z.south → T.low=q.clip → ∀ (F':Forest (dock P K n).ratio)(ρ:Bid.Dir G n→AxisChart G F')(l₀:(dock P K n).Choices), Critical (S:=dock P K n) F' T.high T.up ρ→
   ∀ y:Positions (Primary n G), ‖y‖ < Y x →
      Brush j (betaF G x P.L ^ Shop.output k (edgeW N)) (Y x)⁻¹ (Shellac.off (paid_corner P K O T F' ρ l₀ β z.alpha k-peal F.reps z (gStep β) (radiusB x) k n)) y ∧
      Brush j (betaF G x P.L ^ Shop.output 2 (2*edgeW N)) (Y x)⁻¹ (peal F.reps z (gStep β) (radiusB x) k n) y
variable (hk:k≤N)
include F hk
set_option maxRecDepth 3000 in
lemma awning [Nonempty (Ticket P K O p q B)] (hj:k+3 ≤ j)(hp:2 ≤ N)(hG:G.Simple): ∀ᶠ x in atTop, slenderK P K O hO p q B v F x j k := by
 let t(x:ℝ):= betaF G x P.L; have hy:= Shop.buys_air N; let g:=F.grant; let h:=F.canvas; let a:= F.rooftop; have hF:= Trio.circles G P.L v|>.uses
 let a':= Classical.choice (BareRates.offered G q.width q.paths j); let Z0:=F.presence
 let u:= Λ₀; obtain ⟨z,hZ⟩ := paint_supply G j; have hv:= corner_wind P K p.clip O R Λ₀ F.grant (fun i=>i.upCost) hO F.forms F.code F.well F.rooftop v hF hk (omegaL N k) j; have hg:=corner_cut P Λ₀ F.canvas v hF hk j z; have hK := corner_local P u v hF hk q.clip G' Λ₀ Ticket.money Ticket.paidGrade a'
 have hw := (price_phase u F.canvas hk P v X hF hp z j).bill (show Shop.output 2 (edgeW N) < Shop.output 2 (2*edgeW N) from (by unfold Shop.output; linarith [Shop.edge_pp N]))
 filter_upwards [Delay.shift_pos G P.L,(hK.add hv|>.add hg).bill (earns hk),hw,Sienna.below' G P.L Rate.power (hy.2.trans (by norm_num [Sienna.vow])) zero_lt_one] with x hx hg hw hy n z' β h hx' T hxU hT hJ he F' ρ l₀ hf y hY
 let G₀:= (z',n,β)
 have heq := Trio.quilt G P.L v x _ T F' h.size rfl hx'; have hp' := heq.overall; have hA: (Fintype.card (Primary n G):ℝ)≤X x:= ((Nat.cast_le (α:=ℝ)).2 (Fintype.card_le_of_injective Sum.inl (β:=Joint F' G) Sum.inl_injective)).trans hp'
 have hb : 0<Y x:= Real.rpow_pos_of_pos hx _; have hβ : 0 < β:= by exact (half_pos hx).trans_le h.flit.1
 refine ⟨?_,?_⟩
 · exact (crust P K p.clip O R Λ₀ F.grant (fun i=> i.upCost) hO F.forms F.code hx' T hxU hT F' l₀ hf q.clip D₀ G' Λ₀ (fun i=> i.downCost) F.well F.rooftop F.splice F.canvas hk hj hβ a' hJ he hb hy heq.one hA y hY.le hG hZ).climb ((le_abs_self _).trans (hg G₀ h)) le_rfl
 exact (saliva Λ₀ F.canvas F.early heq.one hA hb hy.le hZ hk z' y (by omega) (gS _ hβ|>.1) hY).climb ((le_abs_self _).trans (hw G₀ h)) le_rfl
end know
end YM.AllOrder.Plateau
