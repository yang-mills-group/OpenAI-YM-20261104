import YM.QuadraticLocal.Class.Clockwork
import YM.QuadraticLocal.Vacuum.Admission
import YM.QuadraticLocal.Vacuum.Before
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
local notation "C'"=> (extra C hψ)
include g
variable (β:ℝ)(hβ:0<β)
include hψ hβ hu he C
lemma schemeGeneral : ∃ (R:Run G)(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls)(Q0:Mentor.Offices.Books D R.rolls Q φ)(Qa:Mentor.Forecast D R.rolls Q φ Q0), WithStage R.metals.p u ∧ R.family.path.levels.clock.kernel.penalty= β∧ Spill.Raffle.Warm G D R.alloy.delay φ∧ WheelP.Certified R.alloy R.kit ∧ Tutoring.Quarterly R D Q C Q0 Qa := by
 obtain ⟨R,hq,⟨⟨D,Q,Q0,hC⟩,huX,heX⟩,hu⟩:= Run.attain_audited C' g u hu _ hβ he
 obtain ⟨Qa,hB⟩:= hC.obligation.1; have hX: VowsR.Chamber C R.kit D Q Q0:= ⟨hC.station,hC.bears,hC.warm,hC.crews,hC.leased,hC.orientation,hC.sales,hC.education,hC.obligation.2.2.1.1⟩
 exact ⟨ R,D,Q,Q0,Qa,hu,hq,hC.obligation.2.2.2.1,huX,hX,hC.obligation.2.2.1.2,hB,hC.obligation.2.2.2.2.1,hC.obligation.2.2.2.2.2,hC.obligation.2.1,Oak.roll R g D Q C Q0 hX Qa hB ⟩
include g hβ C hψ
omit hu he
lemma airport : ∃ (R:Run G)(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls)(Q0:Mentor.Offices.Books D R.rolls Q φ)(Qa:Mentor.Forecast D R.rolls Q φ Q0), WithStage R.metals.p Tracks.readings ∧ R.family.path.levels.clock.kernel.penalty= β∧ Spill.Raffle.Warm G D R.alloy.delay φ∧ WheelP.Certified R.alloy R.kit ∧ Oak.Tutoring.Quarterly R D Q C Q0 Qa ∧ Spill.Walking.Reach G D R.alloy.delay φ:= by
 obtain ⟨R,D,Q,Q0,Qa,h,hB,hR,hP,hQ⟩:= schemeGeneral g ( MintClock.both (ψ:=φ) G C (Spill.Walking.short G φ) ) Tracks.readings Tracks.preview.1 Tracks.preview.2.1 hψ β hβ
 let t:= hQ.employed; exact ⟨R,D,Q,Q0,Qa,h,hB,hR,hP,⟨ ⟨ t.station,t.bears,t.warm,t.crews,t.leased,t.orientation,t.sales,t.education,t.obligation.1⟩, hQ.monthly,hQ.forecast,hQ.year,hQ.forms,hQ.edges,hQ.plan ⟩, t.obligation.2⟩
omit hβ C hψ
open Coat
set_option linter.unusedSectionVars false
local notation "L"=> (R.rolls.L Y)
local notation "eZ" => Φ (i+1)
-- gates, after size of each demand. No C pay bounded before stage Commission.
variable (p:ℕ)(y A₀ ε:ℝ)(hy:p≤ Burn.horizon k+1)(h2:2≤p)(ha:0≤ A₀)(hr: ε < 1/2)
local notation "ReadyAt" => fun x:ℝ=> (∀ β:ℝ, inBand x β → A₀*gStep β^ ((p:ℝ)+1-ε) ≤ AllOrder.High.serving x ∧ orderTarget x k ≤ (2*gStep β)^(p+1))
def DrawVac (p k:ℕ)(C₀ ε y:ℝ):Prop:= ∀ β:ℝ, inBand y β → C₀*gStep β^ ((p:ℝ)+1-ε) ≤ AllOrder.High.serving y ∧ orderTarget y k ≤ (2*gStep β)^(p+1)
omit g in
include h2 hy ha hr R -- R needed for gauge Rate contextual.
in
lemma requestAt : ∀ᶠ y:ℝ in atTop, DrawVac p k A₀ ε y:= by
 let d := ((p:ℝ)+1-ε); have ht: (5/2:ℝ)<d:= by unfold d; linarith only [hr,show (2:ℝ)≤ (p:ℝ) from (by exact_mod_cast h2)]
 have hp:-d/2 < -(9/8:ℝ)+1/80 := by linarith
 let v:=(A₀ * (2:ℝ)^d);
 filter_upwards [eventually_ge_atTop (1:ℝ),(Burn.tracks G (-d/2) |>.mul_left v) _ hp] with y hy₀ hv x hx
 rw [Burn.hat_this G] at hv
 have hh₀:0<y:=zero_lt_one.trans_le hy₀; have hx':0<x:=by have h': y/4 ≤ x:= hx.1; linarith only [hh₀,h']
 let z:=gStep y; have hz:0<z:=Fare.gS _ hh₀|>.1; obtain ⟨hη,hw⟩:= band_gap y x hh₀ hx; change z/2 ≤ gStep x at hη
 constructor
 · apply le_trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Fare.gS x hx'|>.1.le) (show gStep x ≤ 2*z from hw) (show 0≤d from (by linarith only[ht]))) ha) _
   refine le_trans ?_ ((le_abs_self _).trans hv); rw [Real.mul_rpow (by norm_num) hz.le]; unfold z v; rw [Burn.inv_sqrt y hh₀, ← Real.rpow_mul hh₀.le]; rw [show -(1/2:ℝ)*d= -d/2 by ring,← mul_assoc]
 -- power conversion no ε needed in target. Full next projection reach.
 refine le_trans ?_ ( pow_le_pow_left₀ hz.le ( show z ≤ 2*gStep x from (by linarith only[hη]) ) _ ); unfold z; rw [ Burn.inv_sqrt y hh₀, ← Real.rpow_mul_natCast hh₀.le ]; apply Real.rpow_le_rpow_of_exponent_le hy₀; have hh:= Nat.cast_le (α:=ℝ)|>.mpr hy; push_cast at hh ⊢ ; linarith only [hh]
variable (ΦK: WheelP.Certified R.alloy R.kit)
include R g
lemma smaller : Tendsto (fun i:ℕ=> vanishes (Φ (i+1))) atTop (𝓝 0):=by
 have hf : (Tendsto (fun i:ℕ=> i+1) atTop atTop):= tendsto_atTop_mono (f:=id) (g:=_) (fun i=> Nat.le_succ _) tendsto_id
 exact (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/160)).comp ((Sycamore.too R g).comp hf)
include h2 hy ha hr
lemma requested : ∀ᶠ i:ℕ in atTop, DrawVac p k A₀ ε (Φ (i+1)):= by
 have hf : (Tendsto (fun i:ℕ=> i+1) atTop atTop):= tendsto_atTop_mono (f:=id) (g:=_) (fun i=> Nat.le_succ _) tendsto_id; exact ((Sycamore.too R g).comp hf).eventually ( requestAt R p A₀ ε hy h2 ha hr )
end Tracks
end YM.QuadraticLocal.Advent.Sycamore
