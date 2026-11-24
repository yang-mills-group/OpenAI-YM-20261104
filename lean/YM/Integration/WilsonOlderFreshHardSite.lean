import YM.QuadraticLocal.Startup.Pavilion
import YM.QuadraticLocal.Class.Divisor

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshHardSite
open Function Filter Finset Lattice Wilson RG RG.Supply Pressure Input Org Precision Next.Scheduling
open Next.Scheduling.Clock AnalyticBridge VerifiedReset ConnectedActivityE6 PhysicalNext Repeat
open QuadraticLocal QuadraticLocal.Advent QuadraticLocal.Advent.Uplink
open Progress.DirectedRecipe Payments Push AbsoluteSums PriceCompiler
open AllOrder AllOrder.Transit WheelP AllOrder.Floe AllOrder.Floe.Step PlanV Pane ThroughLaunch
open Roost Legato Graces
open Extra.Iteration
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius Asymptotics
open Extra.Histories
variable {G: Gauge} (R:Run G) (g : G.Simple)
local notation "S"=> R.alloy.B.a
local notation "Ta"=> R.T
local notation "Sz"=> R.metals.p
local notation "A"=> R.alloy
local notation "F"=> R.kit
local notation "Z"=> R.family
local notation "c"=> R.family.side
variable {m n i b q k N:ℕ} (h:WayStation R.kit) (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
variable (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls)
set_option quotPrecheck false
local notation "ρ"=> Burn.horizon k
local notation "Φ"=> R.alloy.B.a.clock.hatBeta
local notation "τ"=> R.alloy.B.a.clock.op i n
local notation "Y"=> R.alloy.B.a.clock.J (i+1)
local notation "I"=> R.alloy.B.a.clock.J i
local notation "L"=> R.rolls.L Y
local notation "X"=> R.alloy.B.a.budget i
local notation "W"=> R.alloy.B.a.budget (i+1)
local notation "xd"=> Φ i
local notation "γ"=> Φ (i+1)
local notation "Vd"=> (Φ i)
variable (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin)(Ψ:(i:ℕ)→RG.Rep G (R.family.side i n))
variable (v:Concourse R.alloy R.kit R.T π Γ m N n k Ψ)
variable (K₀:TicketP R.alloy R.kit D Q)
variable (l:m≤ i)
local notation "P"=> Ψ (i+1)
local notation "P'"=> Ψ i
local notation "H"=> Opera.Guide R.alloy.B (R.kit.shape)
local notation "wa"=> Time.forecastK S i (R.kit).scout (P).beta
local notation "wp"=> Time.quoteHard S i (R.kit).book (P).beta
local notation "y₀"=> Willow.haloSlack (X).B
local notation "Γ'"=> R.T.history N n
open Integration.LocalComparison
local notation "κ'"=> forcedDivisor Z i
open Travel
variable (hP: AllOrder.Transit.WheelP.Topline (Ψ N) (R.family.path.levels.clock.forcedAllowance N))
open QuadraticLocal.Hard QuadraticLocal.Spes QuadraticLocal.Kiosk Marker Spes.Market ComparisonDensity.Address
private lemma dummy {K: Marker.Census PUnit.{1}} (x:K.Mode): x.val.card≤1:= by simpa using Finset.card_le_univ x.val
private def Kes : Marker.Census PUnit.{1} := ⟨Finset.univ,Finset.mem_univ _,fun _=>Finset.mem_univ _,fun _ _ _=>Finset.mem_univ _⟩
private def empty {n:Side}{V:Type}[DecidableEq V]{T: Marker.Census V}{o:V→Site n}{p:BudgetPoint}: Lamps Unit Empty G p o T:= ⟨(fun i=> Empty.elim i),(fun i=> Empty.elim i),(fun i=> Empty.elim i),(fun i=> Empty.elim i),fun _=> (fun i=> Empty.elim i),fun _=> (fun i=> Empty.elim i),(fun i=> Empty.elim i),fun _=>  (fun i=> Empty.elim i)⟩ -- V T bind
local notation "τφ"=> R.family.path.levels.clock.op i n
local notation "hΞ"=> (P').p.supportExponent
local notation "β!"=> (P).beta
include h v l K₀
theorem raw (r:i < N) : Topline P' (quoteR R (Ψ (i+1)).beta i):=by
   obtain ⟨U,hU,⟨WC⟩⟩:= (v.2 i l r).earns; have hm' :(1:ℕ)≤ I:= by have hm:= (S).clock.adm i; omega
   obtain ⟨Wq,y,bω,hT⟩:= h.frost.license _ _ (step_paid S i) 1 I hm' le_rfl hm'; let P₁:=hT (Φ i) (R.alloy.B.valid.pays i); obtain ⟨E,he⟩:= invited R h D Q π Γ Ψ v K₀ l r I U P₁
   have hp:=(later R π Γ Ψ v (Nat.le_succ_of_le l) r).truep; have h':= hp.valid.labels;
   let v0:PUnit.{1}→ Site (c (i+1) n):=fun _=>0
   let X':= rentValid h'.forced h'.boundK; let Λ:Gallery Unit Empty v0 P Kes:= ⟨empty,Hard.rent X'⟩
   have hb₀ := (Hard.leasing (w:=1) (α:=Unit) («R»:=Kes) (o:=v0) X'); have hγ : (A).B.a.clock.forcedAllowance (i+1) ≤ 1:=by unfold RG.Calendar.forcedAllowance RG.Calendar.monitor; exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
   have hp' : Λ.Pays 1 (P).p.supportExponent 1 1:= ⟨⟨Empty.elim,(fun e=> e.elim),(fun e=> e.elim),fun x=> budget_finite (fun e=>e.elim) (by rw [Finset.univ_eq_empty,Finset.sum_empty]; exact zero_le_one)⟩,Hard.mono _ hb₀ hγ⟩
   obtain ⟨w'⟩:= Travel.sealed Λ 1 hp'; have hx:= spare R π Γ Ψ v (Nat.le_succ_of_le l) r
   have hn(i:PUnit.{1}):0<(1:PUnit.{1}→ℝ) i:=zero_lt_one
   have ht:= (Travel.docket U WC E Λ 1 w' hn hx dummy (by norm_num) () (Classical.choice (Tree.select (τφ).ratio ((τφ).patch.odd_side)))).2.1
   have hL:= Hard.transfer _ _ () ht hn; unfold Topline; rw [show (Ψ i).p.B=(X).B from congr_arg BudgetPoint.B (later R π Γ Ψ v l r.le).truep.point]; exact ⟨WC.intermediate,_,⟨WC.second⟩, hL⟩

omit h v l K₀ in
theorem increase {sid:Side}{baseRep:RG.Rep G sid}{f a:ℝ}(old:Topline baseRep f)(hne:f ≤ a):Topline baseRep a:=by
  obtain ⟨midstage,loan,⟨secondPass⟩,rent⟩:=old.room
  let same:Kiosk.Second baseRep.p midstage baseRep.activities loan a baseRep.p.supportExponent (Willow.haloSlack baseRep.p.B):=
    { secondPass with funds := { secondPass.funds with returns:=secondPass.funds.returns.trans hne } }
  exact ⟨midstage,loan,⟨same⟩,rent⟩

include h v l K₀ in
theorem squared (active:i<N):Topline (Ψ i) (((S).clock.forcedAllowance i)^2):=by
  have bound: (Ψ (i+1)).beta ∈ Shoot.band (S) (i+1):=by
    rw [(later R π Γ Ψ v (Nat.le_succ_of_le l) active).beta]
    exact (R.makes.wilson.represents N n (i+1) active).band
  exact increase (raw R h D Q π Γ Ψ v K₀ l active) (Consequence.calmPrice R.kit bound)

include h v l K₀ hP in
theorem original (live:i ≤ N):Topline (Ψ i) ((S).clock.forcedAllowance i):=by
  rcases eq_or_lt_of_le live with eq|lt
  · subst i
    exact hP
  · have price:=squared R h D Q π Γ Ψ v K₀ l lt
    have nonnegative:0 ≤ (S).clock.forcedAllowance i:=(Real.exp_pos _).le
    have small:(S).clock.forcedAllowance i ≤ 1:=by
      unfold RG.Calendar.forcedAllowance RG.Calendar.monitor
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
    exact increase price (by simpa only [pow_two,mul_one] using mul_le_mul_of_nonneg_left small nonnegative)
end YM.Integration.WilsonOlderFreshHardSite
end
