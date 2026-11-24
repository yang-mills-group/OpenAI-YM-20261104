import YM.AllOrder.Plateau.Clarity
/-!
# Assemble memory Shore by charging lookup region at DIR physical workload,
then withdrawal unmasked projections from exact kinetic body across all periods,
comparison including winding. Handoff Pledger. Prepare Demand earlier. -/
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
-- P only Kernels. horizon A family includes Wilson geometry, paths immutable & request on any n, alpha leader etc.
variable (p q:Stage) (B:ℝ) (v:ℕ)
local notation "a₁"=>p.paths
local notation "a₂"=>q.paths
local notation "t"=>p.width
local notation "t'"=>q.width
local notation "p'"=>p.clip
local notation "q'"=>q.clip
open Further.PhysicalPeriodLimitF933 Macrame
-- ℝ≤ B. Pressure.Channels aux helper. Param present at each Booth proof; rho ext transport.
structure Ticket where
 tower : Towers P.L
 north : PathData G
 south : PathData G
 alpha : ℝ
 paid : ℝ
 upCost : north.Bounds p.clip p.width p.paths paid
 downCost : south.Bounds q.clip q.width q.paths paid
 bounded : |alpha| ≤ B
 stationary : ∃ a h c:ℝ, 0<h ∧ ∀ (n:Side) (F:Forest (dock P K n).ratio), Ad G P K n → ∃ ρ,
     Critical (S:=dock P K n) F p.clip north ρ∧ ClassicalMatch F p.clip q.clip north south ρ∧
      FiniteBound F north south p.clip q.clip alpha O ρ a h c

local notation "I"=>Ticket P K O p q B
-- Canopy footpoint
abbrev Art := Push.Uniform.Before G p.width p.paths P.J K (N+3) -- include G,N binder
lemma Art.has (hk:5≤N+3): Nonempty (Art (N:=N) (G:=G) P K p) := Uniform.pre_order _ _ _ _ _ (by omega) -- proof?
local notation "R"=> (fun x:I=> x.north)
local notation "D₀"=> (fun x:I=> x.south)
local notation "Λ₀"=> (fun x:I=> x.paid)
local notation "G'"=> (fun x:I=> x.alpha)
variable (hB:P.Branches K G)
include hB
lemma Ticket.grant (F:I→candidates P K G) (Q:Art (N:=N) (G:=G) P K p) (hr:proofC P K p' R Q F) (i:I)(n:Side) : Channels P K p' O R F q' D₀ G' i n:= by
 obtain ⟨s,h,c,hc,H⟩:=i.stationary; obtain ⟨a,ha⟩:=dock_larger P K hB; obtain ⟨b,hb⟩:= (eventually_atTop.1 (Ink.Echo.limitless n |>.eventually (eventually_ge_atTop a))); let w j:= Ink.Echo.amplify n (b+j); refine ⟨w,fun i=> (b+i+1)^4,fun i=> ⟨Ink.Echo.arm n (b+i)⟩,fun _=>by positivity,(Ink.Echo.limitless n).comp (show Tendsto (fun j=>b+j) atTop atTop from ?_),s,h,c,hc,fun j=>?_⟩ ;
 · exact tendsto_atTop_mono (f:=id) (fun j=>Nat.le_add_left j b) tendsto_id
 have hh : Ad G P K (w j):=ha _ (hb _ (by omega)); obtain ⟨ρ,hρ,hK,hA⟩:=H (w j) (trees P K _) hh; have ht: F i (w j)=ᶠ[𝓝 0] ρ := (Before.Service.is_extension (hr i (w j) hh) hρ).symm; let T:= channel P K p' R q' D₀ i.tower i (w j);
 exact ⟨hh,Pane.payouts («R»:=T) ht.symm hK hA⟩
structure Folio (N:ℕ) where
 grant : Art (N:=N) (G:=G) P K p
 forms : Ticket P K O p q B → candidates P K G
 code : proofC P K (p.clip) (fun i : Ticket P K O p q B=> i.north) grant forms
 presence : ℕ→Ticket P K O p q B→ Ink.Field (Coarse G)
 well : Kinetic.Port.Presence P K p.clip O (fun i:Ticket P K O p q B=>i.north) (fun i:Ticket P K O p q B=> i.paid) grant (fun i=> i.upCost) hO forms code presence
 reps : Repertoire (Ticket P K O p q B) G
 splice : Spliced (fun i:Ticket P K O p q B=>i.paid) ((fun i k n=>(presence k i).table n)+(fun i:Ticket P K O p q B=> Stipend q.clip i.south i.alpha)) reps (N+1)
 early : ∀ i<3, reps i= unpop (Ticket P K O p q B) G i
 rooftop : Canopy P K p.clip O (fun i:Ticket P K O p q B=>i.north) (fun i:Ticket P K O p q B => i.paid) grant (fun i=> i.upCost) hO forms code (fun i:Ticket P K O p q B=> i.paid) presence well -- Ticket .. syntax 
 canvas : BillBoard (fun i:Ticket P K O p q B=>i.paid) reps N
variable {P K O p q B}
omit hB
lemma Ticket.paidGrade : Grade (Λ₀) (fun i:I=>i.paid):= givenG fun i=> budget_nonneg i.upCost.two
lemma Ticket.money : Grade (Λ₀) (fun i:I=> |i.alpha|):= Grade.down (gia |B| (abs_nonneg B)) (fun i=> i.bounded.trans (le_abs_self _)) (fun _=>abs_nonneg _)
local notation "T"=> Folio (N:=N) -- T actually `_`
variable (P K O p q B)
include hB
lemma Folio.ok (hG:G.Simple) (hv:2≤N)(hI:Nonempty (Ticket P K O p q B)): Nonempty (Folio P K O hO p q B N) := by
   let Q:= Classical.choice (Art.has (G:=G) P K p (N:=N) (by omega)); obtain ⟨F,H⟩:=tens P K p' R Λ₀ Q (fun i=> i.upCost)
   obtain ⟨M,U,hM,hU,H₀⟩:= flux P K p' O R Λ₀ Q hB (fun i=> i.upCost) hO F H q' D₀ G' Λ₀ (fun i=> i.downCost) (fun i:I=>i.tower) Ticket.paidGrade Ticket.money hv hG (Ticket.grant P K O p q B hB F Q H)
   exact ⟨Q,F,H,M,hM,U,hU,H₀, (canopy_exists P K p' O R Λ₀ Q (fun i=> i.upCost) hO F H hM).some,(BillBoard.ok Λ₀ hU).some⟩

end know
end YM.AllOrder.Plateau
