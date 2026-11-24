import YM.QuadraticLocal.Class.Stair
import YM.QuadraticLocal.Class.Viewbook

/-! # Paying for fixed perturbative, representational and position orders setup in one Run

Still with any applicable additional delay strengthening. Can request these rates with `announce`.
Retains shot β and the official reconstruction properties (see `Legato.Run.ramp & again`).
-/
set_option autoImplicit false
noncomputable section

namespace YM.QuadraticLocal.Advent.Sycamore

open Function Filter Finset Lattice Wilson RG RG.Supply Pressure Input Org Precision
open Next.Scheduling Next.Scheduling.Clock AnalyticBridge VerifiedReset ConnectedActivityE6 PhysicalNext Repeat
open Progress.DirectedRecipe Payments Push AbsoluteSums PriceCompiler
open AllOrder AllOrder.Transit WheelP AllOrder.Floe AllOrder.Floe.Step PlanV Pane ThroughLaunch
open Roost Legato Graces Extra.Iteration Extra.Histories
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius Asymptotics

variable {G: Gauge} (R:Run G) (g : G.Simple)
local notation "S"=> R.alloy.B.a
local notation "A"=> R.alloy
local notation "F"=> R.kit
local notation "Z"=> R.family
variable {m n i b q k N:ℕ} (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
variable (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls)
set_option quotPrecheck false
local notation "ρ"=> Burn.horizon k
local notation "Φ"=> R.alloy.B.a.clock.hatBeta
local notation "τ"=> R.alloy.B.a.clock.op i n
local notation "Y"=> R.alloy.B.a.clock.J (i+1)
local notation "I"=> R.alloy.B.a.clock.J i
local notation "xd"=> Φ i
variable (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin)(Ψ:(i:ℕ)→RG.Rep G (R.family.side i n))
variable (v:Concourse R.alloy R.kit R.T π Γ m N n k Ψ)
open Integration.LocalComparison VowsR QuadraticLocal.Mentor
variable {φ:ℕ→ℕ} (C:VowsR.LawScroll G φ) (Q0:QuadraticLocal.Mentor.Offices.Books D R.rolls Q φ)
variable (Qa: Mentor.Forecast D R.rolls Q φ Q0)

namespace Tracks
open Oak Tutoring Rebirth Rebirth.Scholar MintClock
open ThroughLaunch
open PaceR
variable (u:Orders)(hu:Draft u) (he:∀ i,100≤u.supportExp i)
variable (hψ: MintClock.splits ≤ φ)
-- Prepack ANY clause. Beware of needed stage pair in each supplemental levy
local notation "Λ"=> MintClock.both (ψ:=φ) G
local notation "W"=> WithStage R.metals.p u
local notation "QV"=> Tutoring.Quarterly
include hψ in
def extra : LawScroll G φ:= Λ ( MintClock.anchor (ψ:=φ) G hψ ) ( Λ (Volume.wind G φ) ( Λ (Λ C ( Scholar.genesis G φ )) ( Λ ( Spill.Raffle.scroll G φ ) ( Λ (Scholar.Vacuum.readyYear G φ ) (Scholar.Vacuum.training G φ ) ) ) ) )
local notation "C'"=> (extra C hψ)
include g
variable (β:ℝ)(hβ:0<β)
include hψ hβ hu he C
lemma scheme : ∃ (R:Run G)(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls)(Q0:Mentor.Offices.Books D R.rolls Q φ)(Qa:Mentor.Forecast D R.rolls Q φ Q0), WithStage R.metals.p u ∧ R.family.path.levels.clock.kernel.penalty= β∧ Spill.Raffle.Warm G D R.alloy.delay φ∧ Tutoring.Quarterly R D Q C Q0 Qa := by
 obtain ⟨R,hq,⟨D,Q,Q0,hC⟩,hu⟩:= Run.attain_aligned C' g u hu _ hβ he
 obtain ⟨Qa,hB⟩:= hC.obligation.1; have hX: VowsR.Chamber C R.kit D Q Q0:= ⟨hC.station,hC.bears,hC.warm,hC.crews,hC.leased,hC.orientation,hC.sales,hC.education,hC.obligation.2.2.1.1⟩
 exact ⟨ R,D,Q,Q0,Qa,hu,hq,hC.obligation.2.2.2.1,hX,hC.obligation.2.2.1.2,hB,hC.obligation.2.2.2.2.1,hC.obligation.2.2.2.2.2,hC.obligation.2.1,Oak.roll R g D Q C Q0 hX Qa hB ⟩
omit hψ hβ he C g hu

-- position support reservation at chosen level. Numbers follow current budget point, not remote.B?
variable (hS: WithStage R.metals.p u)(hn:i≤N)(hp:m≤ i)
include v hS hp hn
lemma point : NormAt R.family i ((Ψ i).p) (u.jets (R.alloy.B.a.clock.J i)) (u.position (R.alloy.B.a.clock.J i)) (u.supportExp (R.alloy.B.a.clock.J i)):= by
 have ht (x:ℕ):= ( params_eq R.alloy.B.valid x ); rw [(later R π Γ Ψ v hp hn).truep.point]
 refine ⟨rfl,rfl,?_,?_,?_⟩
 · change ((( S ).params i).order)= u.jets _; rw [ht i]; exact (hS.jets _)
 · change ((( S ).params i).power)= u.position _; rw [ht i]; exact (hS.powers _)
 change ((( S ).params i).supportExponent)= u.supportExp _; rw [ht i]; exact (hS.prices _)
omit v hp hn
include g hu
variable (hg : Tendsto u.supportExp atTop atTop)(b₀:ℕ)(b₁:ℝ)
include hg
-- arbitrary h = (field deriv budget lower, position budget lower, support exponent minimum,
--           warmth tolerance (p count in Stage), support10). On each canvas of epoch.
lemma top_orders (d₁ d₂ d₃:ℕ)(x:ℝ) : ∀ᶠ b:ℕ in atTop,∀ m≤ b, PaceR.Close R b₀ b₁ m b → ∀ (n i k N:ℕ) (π:ℕ→Layout G) (Γ:ℕ→ Pace.Coin) (Ψ:(i:ℕ)→RG.Rep G (R.family.side i n)), Concourse R.alloy R.kit R.T π Γ m N n k Ψ→ m ≤ i → i ≤ N → d₁ ≤ ( Ψ i ).p.order ∧ d₂ ≤ ( Ψ i ).p.power ∧ d₃ ≤ R.alloy.B.a.clock.J i ∧ x≤ ( Ψ i ).p.supportExponent :=by
 obtain ⟨l,hl⟩:= (hg.eventually_ge_atTop x).exists
 filter_upwards [ PaceR.on_tail R g b₀ b₁ d₁, PaceR.on_tail R g b₀ b₁ d₂, PaceR.on_tail R g b₀ b₁ d₃, PaceR.on_tail R g b₀ b₁ l ] with b h₁ h₂ h₃ h₄ m hm h n i k N π Γ Ψ v hn hp
 have hr(d:ℕ)(hd:d≤R.alloy.B.a.clock.J m): d≤ ( R.alloy.B.a.clock.J i ):= hd.trans (( S ).fits.mono hn);
 let Tt:=(point R π Γ Ψ v u hS hp hn); let j:=( R.alloy.B.a.clock.J i ); exact ⟨( (hr d₁ ( h₁ m hm h )).trans ( (le_max_right 6 j).trans (hu.k j))).trans_eq Tt.order.symm, ((hr d₂ (h₂ m hm h)).trans ( (le_max_right 2 j).trans (hu.heights j))).trans_eq Tt.distance.symm,hr d₃ (h₃ m hm h), (hl.trans (hu.ascend (hr l (h₄ m hm h)))).trans_eq Tt.reserve.symm⟩
omit hg hS g hu

-- Combined statement: enough room across every demand. `Scheme` buys any Draft, but for
-- this application all counts increase without bound. Include explicit existence also of scroll
-- and profile so not introducing model-witness costs after the fact. Consumer can substitute any
-- different monotone `Draft` to meet later Mark.Field derivatives occupancy budget.
noncomputable def readings : Orders:= ⟨4,fun i=>6+i,fun i=>2+i,fun i=>100+i⟩
lemma preview : Draft readings ∧ (∀ i,100≤ readings.supportExp i) ∧ Tendsto readings.supportExp atTop atTop:= by
 let v:=readings; have hE (i:ℕ): 100 ≤ readings.supportExp i:= by change (100:ℝ) ≤ 100+i; simp
 refine ⟨?_,hE,?_⟩
 · refine ⟨le_rfl,fun i j hij=> Nat.add_le_add_left hij 6,fun i j hij=> Nat.add_le_add_left hij 2,fun i j hij=>?_,fun i=> lt_of_lt_of_le (by norm_num) (hE i),fun i=>by change _ ≤6+i; omega,fun i=>by change _≤2+i; omega⟩
   change (100:ℝ)+i≤100+j; gcongr
 exact tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop

include g hβ
open Eon Syl
-- endpoint for now; don't install silly-specific affected costs. `LawScroll probe` no third quotes.
theorem purchases : ∃ (R:Run G)(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls)(Q0:Mentor.Offices.Books D R.rolls Q MintClock.splits)(Qa:Mentor.Forecast D R.rolls Q MintClock.splits Q0), WithStage R.metals.p Tracks.readings ∧ R.family.path.levels.clock.kernel.penalty= β∧ Spill.Raffle.Warm G D R.alloy.delay MintClock.splits∧ Tutoring.Quarterly R D Q (VowsR.probe G MintClock.splits) Q0 Qa ∧
     ∀ (k:ℕ)(U:Syl.School k)(ε:ℝ),0 < ε → ε≤1/8 → ∀ (ℓ:ℝ) (l a d:ℕ), 0≤ℓ → ∀ᶠ b:ℕ in atTop,∀ i:ℕ, Boot.Alumni R D Q Q0 U Qa a l d ε ℓ b i := by
 obtain ⟨R,D,Q,Q0,Qa,hP,hB,hW,hQ⟩:= scheme g (VowsR.probe G MintClock.splits) Tracks.readings Tracks.preview.1 Tracks.preview.2.1 le_rfl β hβ
 exact ⟨R,D,Q,Q0,Qa,hP,hB,hW,hQ,fun _ U ε he hF ℓ l a d hh => Boot.lectures R g D Q _ Q0 U Qa hQ hW a l d ε ℓ he hF hh⟩

end Tracks
end YM.QuadraticLocal.Advent.Sycamore
