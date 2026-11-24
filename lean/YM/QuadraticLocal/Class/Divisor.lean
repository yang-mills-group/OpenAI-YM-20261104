import YM.QuadraticLocal.Class.Value
/-!
# All forced members AFTER a step. The whole hard-row cost, even its vacuum coefficient.

Sharper purchase exp(-[...]/2), available at every emitted (reclosed) output before the next
report. In particular it will still meet the common zero-marker forcedAllowance. The stage was procured for the full band,
so since the SHOT satisfies the smaller band it grants this power for repaying the mark radii
and retaining strong hit prices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal
open Function Filter Finset Lattice Wilson RG RG.Supply Pressure Input Org Precision
open Next.Scheduling Next.Scheduling.Clock AnalyticBridge VerifiedReset Collection Quotes ConnectedActivityE6 PhysicalNext Repeat
open Progress.DirectedRecipe Payments Push AbsoluteSums PriceCompiler
open AllOrder AllOrder.Transit WheelP AllOrder.Floe AllOrder.Floe.Step PlanV Pane ThroughLaunch
open Roost Legato Graces UVNext.CouplingReset Time Coat
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius Asymptotics
namespace Consequence
variable {G:Gauge}{X:Metals G}{D:Rolls X.p}{A:Alloy X D}(R:Factor A)

-- Extremal use is allowed for shop only (not for running solver).
private lemma goal_price (F:Postage){z x:ℝ}(hz:0<z)(hx:0<x):
    Payments.Pairing.kGoal F z x = F.rate*((Instrument.plain.P z)^2/z*x):=by
    have hp:= Real.sqrt_pos.mpr hz; have hh:= Real.sqrt_pos.mpr hx
    unfold Payments.Pairing.kGoal Instrument.t Clock.gap
    rw [div_pow,mul_pow, inv_pow,inv_pow,Real.sq_sqrt hz.le,Real.sq_sqrt hx.le]; field_simp -- ring

lemma calmPrice {i:ℕ}{x:ℝ}(hx:x∈RG.Shoot.band A.B.a (i+1)):
    Time.quoteHard A.B.a i R.book x ≤ (A.B.a.clock.forcedAllowance i)^2:=by
    let c:=i+1;let B:= A.B.a;let j:=B.clock.J c;let m:=B.clock.J i;let z:=B.clock.hatBeta c;let u:=B.clock.hatBeta i; let F:=R.book j m
    have hz : 0 < z:= zero_lt_one.trans (A.B.a.fits.delayed _)
    let x₀:=z/4
    have hx': Next.Scheduling.inBand z x₀:=⟨le_rfl,by unfold x₀; linarith⟩
    have he:= R.machine.shops _ _ (A.B.valid.pays i) _ (step_paid B i)
    let P:=B.budget i
    have hZ : z=u+G.slopeConstant*Real.log (D.L j).val:= by unfold z u j c B; rw [←PriceCompiler.block_eq A.B.valid]; exact (Deployment.hat i).symm
    obtain ⟨_,_,_,Hθ,hw,_,hT⟩:=Deployment.clock_eqns B.clock i
    have hP:=PriceCompiler.params_eq A.B.valid i; have hs : Same (B.params i) P:= ⟨rfl,rfl,rfl⟩
    let M:= R.machine
    have hg:= (he P (hP ▸ hs) rfl hT).2.2 (R.exchange j m) 0 0 x₀ (show |(0:ℝ)| ≤ alphaBound D j from by
       unfold alphaBound; rw [abs_zero]; have h:= (X.p.profile j).drift_ge; positivity) (hZ ▸ hx')
    have hE:= (hg.2.2.2 (M.coverage _ _ (step_paid B i)).1).2
    have hr : Real.exp (-Payments.Pairing.kGoal F z x₀) ≤ B.clock.forcedAllowance i:=by rw [hZ,hw]; exact hE
    have hu : z/2 ≤ x:=hx.1
    have hy : 0<x:= lt_of_lt_of_le (half_pos hz) hu
    change Real.exp (-Payments.Pairing.kGoal F z x) ≤ _
    have hF : 2*Payments.Pairing.kGoal F z x₀ ≤ Payments.Pairing.kGoal F z x:=by
       rw [goal_price F hz hy, goal_price F hz (by unfold x₀; positivity)]
       have hC:0≤F.rate*((Instrument.plain.P z)^2/z):=by have h:=F.pos; positivity
       unfold x₀; linarith only [mul_le_mul_of_nonneg_left hu hC]
    calc _ ≤ Real.exp (-(2*Payments.Pairing.kGoal F z x₀)):= Real.exp_monotone (neg_le_neg hF)
         _ = (Real.exp (-Payments.Pairing.kGoal F z x₀))^2 := by rw [pow_two,← Real.exp_add];congr 1;ring
         _ ≤ _:=pow_le_pow_left₀ (Real.exp_pos _).le hr _

end Consequence
namespace Advent.Sycamore.Eon
open Function Filter Finset Lattice Wilson RG RG.Supply Pressure Input Org Precision
open Marker Integration.LocalComparison
variable {G: Gauge} (R:Run G)
variable {m n i b k N:ℕ}
variable (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
variable (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls)
variable (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin)(Ψ:(i:ℕ)→RG.Rep G (R.family.side i n))
variable (v:Concourse R.alloy R.kit R.T π Γ m N n k Ψ)
variable (hℓ:m≤ i) (hz:i<N)
set_option quotPrecheck false
local notation "P'" j:max=> Ψ j
local notation "S"=> R.alloy.B.a
local notation "Z"=> R.family
variable {Θ ι ιw α : Type} [Fintype Θ][DecidableEq Θ]{R₀: Marker.Census Θ}
variable {W': Θ→Type} [∀ i,AddCommGroup (W' i)][∀ i,Module ℝ (W' i)]
variable (Actors:∀ i, Set (W' i))(U:∀ i,Submodule ℝ (W' i))
variable (w:Θ→ℝ)(η:Θ→ℕ)(Z':Syl.School k)
local notation "σ"=> ( (Ψ i).p.supportExponent )
local notation "B"=> (Ψ i).p.B
local notation "T" j:max=> Pupil (Ψ j) R₀ ( Affinity.Wallet Actors )
variable (Vr:Pupil (Ψ i) R₀ ( Affinity.Wallet Actors )) (Vn:Pupil (Ψ (i+1)) R₀ ( Affinity.Wallet Actors ))
local notation "p"=> ( Ψ i ).p
local notation "Λ"=> Tint.Patrol.picture Vr.painter Vr.packet
local notation "Gp"=> (Coat.gStep (Ψ i).beta)
local notation "δ₀"=> ( forcedDivisor R.family i )
local notation "Φ"=> R.alloy.B.a.clock.hatBeta
local notation "I"=> R.alloy.B.a.clock.J i
local notation "κ"=> R.alloy.B.a.clock.J (i+1)
local notation "xd"=> Φ i
variable {φ:ℕ→ℕ}(C:VowsR.LawScroll G φ)(Q0: Mentor.Offices.Books D R.rolls Q φ) (Qa: Mentor.Forecast D R.rolls Q φ Q0)
variable (s:ℕ) (ε:ℝ)
local notation "ω₁"=> Pairing.kGoal ( R.kit.book (κ) (I) ) (Φ (i+1)) (( Ψ (i+1)).beta)
variable (hp:Printed R D Ψ (N:=N) (m:=m) (b:=b) (φ:=φ) Actors U w η Z' s ε (R₀:=R₀) Vn Vr)
local notation "V"=> ( R.family.path.levels.clock.forcedAllowance i )
local notation "ψ"=> Real.exp (-ω₁/2)
local notation "X0"=> ( Ψ (i+1) )
local notation "A₀"=> Real.sqrt ( quoteR R (Ψ (i+1)).beta i )
local notation "price*"=> quoteR R (Ψ (i+1)).beta i
include hℓ hz v hp
lemma force_prices :
    Vr.packet.hard.Paid w ((Ψ i).p.B) ((Ψ i).p.supportExponent) ( Real.exp (-ω₁ /2) ) ∧
    Real.exp ( -ω₁ /2 ) ≤ (R.family.path.levels.clock.forcedAllowance i) ∧
    Vr.packet.hard.Paid w ((Ψ i).p.B) ( (Ψ i).p.supportExponent ) (R.family.path.levels.clock.forcedAllowance i) :=by
 let z:= quoteR R (Ψ (i+1)).beta i
 have hX : ( Ψ (i+1) ).beta ∈ RG.Shoot.band ( S ) (i+1) := ( later R π Γ Ψ v (Nat.le_succ_of_le hℓ) hz ).beta.symm ▸ (( R.T.sticks N n|>.prices (i+1) ( Nat.zero_le _) hz).2)
 have hz : Real.sqrt ( z )=ψ:=by unfold z quoteR Time.quoteHard; rw [Real.sqrt_eq_rpow,← Real.exp_mul]; congr 1; ring
 have hf : ψ ≤ ( R.alloy.B.a.clock.forcedAllowance i ):= le_trans (hz.symm.trans_le (Real.sqrt_le_sqrt (Consequence.calmPrice R.kit hX))) (le_of_eq (Real.sqrt_sq (Real.exp_pos _).le))
 have ht:= Hard.mono Vr.packet.hard hp.fire ( min_le_right .. ); refine ⟨?_,hf, Hard.mono Vr.packet.hard ht ( hz.trans_le hf )⟩
 rw [← hz]; exact ht
end Advent.Sycamore.Eon
end YM.QuadraticLocal
