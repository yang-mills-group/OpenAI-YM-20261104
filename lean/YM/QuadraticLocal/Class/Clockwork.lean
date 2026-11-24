import YM.QuadraticLocal.Class.Tracks

/-! # Nonempty close corridors and resource costs

Preprocess L (as slowly increasing as needed) at all marker width orientation tasks. Keep all
adjacent levels close in the post log geometry. No restrictions on length of proof call except
as announced in the close lemma. In particular don't accidentally request a separated multipole
1 derivative valuation over a stepped area using this (
full reindexing/preimage cost for that assembly isn't estimated here).
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Spill.Walking
open Function Filter Finset Lattice RG Pressure Ac Marker Next.Scheduling
open Wilson RG.Supply PhysicalNext Repeat
open ConnectedActivityE6 Push Push.AbsoluteSums Coat RemainderComparison
open AnalyticBridge VerifiedReset QuadraticLocal.Earn QuadraticLocal.Mentor Animals
open AllOrder AllOrder.Burn MintClock
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Asymptotics
open AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open Input Org Wilson ThroughLaunch PriceCompiler
open Legato.VowsR
variable (G:Gauge){X: Metals G} (R:Roots (G:=G) X.p.profile X.K X.p.kernel)
variable {D:Rolls X.p} {P:Protection D}(W:Delays P)
variable (φ:ℕ→ℕ)

-- lengths funded before increasing to manuscript width model. Plus-one variants to avoid
-- failure at the very coarse conditioned windows. `whirl` equivalent z_i.
def whirl (x:ℝ):ℝ:= Real.log (2+Real.log x)
def Reach : Prop:= ∀ x y, StepStages x y → ∀ t,W.betaEntry x≤ t →
   Real.log ( ( D.L x ).val:ℝ ) ≤ whirl t ∧ 1 ≤ whirl t ∧ ∀ i ≤ y,(Poetry.Agenda.seed R φ i y)⁻¹ ≤ whirl t
lemma aside : Tendsto whirl atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_const_nhds.add_atTop (Real.tendsto_log_atTop))
lemma outcomes : ∃ Y:Delays P, DelayLe W Y ∧ ∀ Z:Delays P, DelayLe Y Z → Reach G R Z φ:= by
 let P₀ x y t:= Real.log ( ( D.L x ).val:ℝ ) ≤ whirl t ∧ 1 ≤ whirl t ∧ ∀ i ≤ y,(Poetry.Agenda.seed R φ i y)⁻¹ ≤ whirl t
 have ht(x y):∀ᶠ t in atTop,P₀ x y t:=by
   filter_upwards [ (aside.eventually_ge_atTop _), (aside.eventually_ge_atTop 1), (eventually_all_finset (Finset.Iic y)).2 fun i (hi: i∈ Finset.Iic y)=> aside.eventually_ge_atTop (( Poetry.Agenda.seed R φ i y )⁻¹) ] with t hv hp hh
   exact ⟨hv,hp,fun i hi=> hh i (mem_Iic.mpr hi)⟩
 obtain ⟨t',-,hx,hy⟩:= collect_upper W.betaEntry _ (fun x=> eventually_transitions x _ _ fun y _=> ht x y); exact ⟨{W with betaEntry:=t'},⟨hx,le_rfl,le_rfl,le_rfl⟩,fun _ he j i h x hk=> hy _ _ ((he.beta j).trans hk) i h⟩
def short : LawScroll G φ where
    clause (Y') D PP C R₀ q Wp Z Q₀ S R Yr Kq T' V':= Reach G R V' φ
    permits := by
      intro S Tq R C E' h; refine ⟨(fun _=> (0:ℕ)),fun l hL D q Wp Z Q' S' he Pw T₀ Yr Book hP V'=>?_⟩; exact outcomes (X:=ThroughLaunch.currency S Tq l) G R V' φ
end YM.QuadraticLocal.Spill.Walking
namespace YM.QuadraticLocal.Advent.Sycamore
open Function Filter Finset Lattice RG Pressure Ac Marker Next.Scheduling
open Wilson RG.Supply PhysicalNext Repeat
open ConnectedActivityE6 Push Push.AbsoluteSums Coat RemainderComparison
open AnalyticBridge VerifiedReset QuadraticLocal.Earn QuadraticLocal.Mentor Animals
open AllOrder AllOrder.Burn MintClock
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Asymptotics
open AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open Input Org Wilson ThroughLaunch PriceCompiler
open Legato Legato.VowsR PaceR Boot Eon
variable {G:Gauge} (R:Run G)
variable (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
variable {m i u k b:ℕ}
local notation "A"=> R.alloy.B.a
local notation "S"=> R.family.S
set_option quotPrecheck false
local notation "Φ"=> R.alloy.B.a.clock.hatBeta
open Spill.Walking
namespace Shuttle
variable {φ:ℕ→ℕ} (θ : Spill.Walking.Reach G D R.alloy.delay φ)
local notation "K_"=> R.family.path.levels.clock.J i
local notation "J_"=> R.family.path.levels.clock.J (i+1)
include θ
lemma spending (i:ℕ) : (S).scale (i+1)-(S).scale i≤ whirl (Φ i) ∧ 1≤ whirl (Φ i)∧ ∀ k ≤ R.alloy.B.a.clock.J i, (Poetry.Agenda.seed D φ k (R.alloy.B.a.clock.J i))⁻¹ ≤ whirl (Φ i) :=by
 rw [ ( S ).scale_succ, add_sub_cancel_left, show ( S ).block i=( R.rolls.L ( R.alloy.B.a.clock.J (i+1) ) ) from ( PriceCompiler.block_eq R.alloy.B.valid i ) ]
 exact θ _ _ (step_paid ( A ) i) _ ( R.alloy.B.valid.pays i )
omit θ
variable (g:G.Simple)
include g
lemma raising (hi:i≤b) : whirl (Φ i) ≤ whirl (Φ b):= Real.log_le_log ( add_pos zero_lt_two (PaceR.positive_log ..) ) ( add_le_add_right ( Real.log_le_log ( PaceR.positive R i ) ( PaceR.clock_mono R g hi )) _)
include θ
lemma farther (h:i≤b): ( S ).scale b-( S ).scale i ≤ (( b-i:ℕ ):ℝ)* whirl (Φ b):=by
 induction h using Nat.decreasingInduction with
 | self=> simp
 | of_succ i h hi=>
   have he:=(Shuttle.spending R D θ i).1; let hx:= raising R g h.le
   have ht :(b-i:ℕ)= b-(i+1)+1:=(by omega); rw [ht]; push_cast; linarith only [ hi,he,hx ]
lemma sprints {b₀:ℕ} (h:i≤b)(he:b-i≤ b₀): PaceR.Close R 1 ( b₀:ℝ ) i b:= by
 have hp:0 < whirl (Φ b):= PaceR.positive_clock R b
 unfold PaceR.Close; rw [pow_one]; exact ( farther R D θ g h ).trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr he) hp.le)
-- publish, consumer use with `Kℓ≥Boot.Need` unchanged data. no engineering or joining larger spaces here.
variable (C:LawScroll G φ)(β:ℝ)(hβ:0<β)(hψ:MintClock.splits≤φ)
omit θ
include hβ C hψ
lemma posts : ∃ (R:Run G)(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls)(Q0:Mentor.Offices.Books D R.rolls Q φ)(Qa:Mentor.Forecast D R.rolls Q φ Q0), WithStage R.metals.p Tracks.readings ∧ R.family.path.levels.clock.kernel.penalty= β∧ Spill.Raffle.Warm G D R.alloy.delay φ∧ Oak.Tutoring.Quarterly R D Q C Q0 Qa ∧ Spill.Walking.Reach G D R.alloy.delay φ:= by
 obtain ⟨R,D,Q,Q0,Qa,h,hB,hR,hQ⟩:= Tracks.scheme g (MintClock.both (ψ:=φ) G C (Spill.Walking.short G φ) ) Tracks.readings Tracks.preview.1 Tracks.preview.2.1 hψ β hβ
 let t:= hQ.employed; exact ⟨R,D,Q,Q0,Qa,h,hB,hR,⟨ ⟨ t.station,t.bears,t.warm,t.crews,t.leased,t.orientation,t.sales,t.education,t.obligation.1⟩, hQ.monthly,hQ.forecast,hQ.year,hQ.forms,hQ.edges,hQ.plan ⟩, t.obligation.2⟩
omit hβ hψ
variable (Q:D.Tab R.rolls)(Q0:Mentor.Offices.Books D R.rolls Q φ)(Qa:Mentor.Forecast D R.rolls Q φ Q0)
variable (hX:Oak.Tutoring.Quarterly R D Q C Q0 Qa)(hx:Spill.Raffle.Warm G D R.alloy.delay φ)
variable (F:Syl.School k)(r K Sx:ℕ)(ε:ℝ)(h₀:0<ε)(h₁:ε≤1/8)
include hX hx h₀ h₁ θ
-- includes every stipulated single or multiple adjacency, using those receipts.
lemma future : ∀ᶠ b:ℕ in atTop,∀ m≤b,b-m≤ Sx→ PaceR.Close R 1 ( Sx:ℝ ) m b∧ Boot.Alumni R D Q Q0 F Qa r 1 K ε ( Sx:ℝ ) b m:= by
 filter_upwards [ Boot.lectures R g D Q C Q0 F Qa hX hx r 1 K ε ( Sx:ℝ ) h₀ h₁ (Nat.cast_nonneg _) ] with b ht m hm hb; exact ⟨sprints R D θ g hm hb, ht m ⟩
end Shuttle
end YM.QuadraticLocal.Advent.Sycamore
