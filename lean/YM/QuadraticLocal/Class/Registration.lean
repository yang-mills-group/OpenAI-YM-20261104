import YM.QuadraticLocal.Class.Foundry
import YM.QuadraticLocal.Class.Raffle
import YM.QuadraticLocal.Class.Value
import YM.QuadraticLocal.Startup.Pavilion
/-!
# Prepare any fixed-load analytic generators for input before even the first of our estimates

Uses prepaid allowances at index `i`, including a path authorized for this re-expression also
when `i=cutoff`. Construct missing forced partners on the true flags. Not starting by
asserting a formal remainder at the initial index! No fine-mesh hypothesis on extent of the
requested markers here (torus from Run, parameters from earned `Passport` anchors,
 actual height and all kernel budgets from `Earn` and `Affinity` of the experiment).
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
variable (Y':VowsR.Chamber C R.kit D Q Q0)
variable (hℓ:m≤ i) (hz: i≤ N)

namespace Boot
open Oak Buffered Earn Marker QuadraticLocal.Tint QuadraticLocal.Syl
variable {Θ ι ιw α : Type} [Fintype Θ][DecidableEq Θ]{R₀: Marker.Census Θ}
variable {W': Θ→Type} [∀ i,AddCommGroup (W' i)][∀ i,Module ℝ (W' i)]
variable (Actors:∀ i, Set (W' i))(U:∀ i,Submodule ℝ (W' i))
variable (w:Θ→ℝ)(η:Θ→ℕ)(Z':School k)
local notation "μ" j:max=> ( Poetry.Agenda.seed D φ (Burn.horizon k) ( R.alloy.B.a.clock.J j ))
variable {Ξ: Passport ( R.family.side i n ) Θ} (T:ι→ Row Ξ R₀ G ( Affinity.Wallet Actors ))
variable (Yv:Scene.Armada T w η (Poetry.Agenda.seed D φ (Burn.horizon k) ( R.alloy.B.a.clock.J i )) 1 Z'.order Z'.pieces Z'.horizon) (hM:Tableau U Actors T)
local notation "T_"=> ( Tint.Incoming Ξ (Ψ i) ( Affinity.Wallet Actors ) Empty R₀ )
variable [ Countable ι ]
local notation "pB"=> (Ψ i).p
local notation "Gp"=> ( Coat.gStep (Ψ i).beta )
def release (V:T_): Pupil ( Ψ i ) R₀ ( Affinity.Wallet Actors ):= ⟨Ξ,ι,Empty,T,V⟩
variable (hw:Spill.Raffle.Warm G D R.alloy.delay φ) (hv:Topline (Ψ N) (R.family.path.levels.clock.forcedAllowance N)) (d:ℕ)
local notation "qT"=> ( Ψ i ).p.supportExponent
local notation "L!"=> ( S ).params i
local notation "CL"=> ( Spill.Raffle.fundsOne G ( L! ) ( μ i ) Z'.order Z'.horizon Z'.pieces xd )
local notation "v₀"=> ( MintClock.Page.temperature G 1 xd )

def need (n:ℕ) (Zp:Syl.School k):ℕ:= n+ Spill.Raffle.pad (Zp.order+Zp.horizon+1)*Zp.pieces
local notation "d₀"=> ( need d Z' )
local notation "r"=> (Z'.order+Z'.horizon+1)
local notation "Σ_"=> ( Invoice.price (pB) (v₀) r Z'.pieces (qT + 1) ( μ i /4) G )
local notation "δ"=> ( forcedDivisor R.family i )
local notation "Zt"=> ( δ * ( Φ i )^(-(d:ℝ)) )
include hz hℓ v
lemma tunes : Spes.Market.tuning ((S).params i) ((Ψ i).p) (Φ i):=by
 rw [(later R π Γ Ψ v hℓ hz).truep.point]; exact ⟨rfl,rfl,rfl,rfl,rfl⟩
omit hz hℓ v in
private lemma glyph : Blush.glyph (Φ i) = forcedDivisor R.family i:=rfl
include hk Y' hw Yv hM hv
local notation "Λ"=> (rendered T pB Gp)
local notation "M" v:max=> Tint.Patrol.picture T v
local notation "Ξ'" v:max=> Boot.release R Ψ Actors T v
-- RECORD period endorsements (no assuming mark normalization)
structure Bare (V:Tint.Incoming Ξ (Ψ i) ( Affinity.Wallet Actors ) Empty R₀) :Prop where
 clothes : Attire (φ:=φ) R D Ψ Actors U w η Z' 0 1 (Ξ' V)
 funding: ( rendered T (Ψ i).p Gp ).Paid w ( ( Ψ i ).p.B ) (qT+1) CL
 cost : CL ≤ MintClock.Page.reward (Φ i) ( Mentor.Tolerance I )
 crown : V.hard.Paid w ( Ψ i ).p.B qT Zt
 face (t: Affinity.Wallet Actors)(y: Config G (R.family.side i n)): Summable (fun i=> Spill.raw T Gp t i y) ∧ ( M V ).E.log t y=( Λ ).log t y ∧ ( M V ).density t y= (↑(( Ψ i ).eval y):ℂ) • Marker.Poly.pass ( Spill.Foundry.uncut T Gp t y )
lemma launching (hd: Boot.need d Z' ≤ R.alloy.B.a.clock.J i) : ∃ V,Bare R D Ψ (φ:=φ) Actors U w η Z' T d V:=by
 have hx : ρ+2 ≤ I:= hk.trans ((S).fits.mono hℓ)
 let hh:= tunes R π Γ Ψ v hℓ hz
 have ht :Spill.Raffle.Gains G ((S).params i) (Poetry.Agenda.seed D φ (Burn.horizon k) I) ( Mentor.Tolerance I ) Z'.order Z'.horizon Z'.pieces ( Φ i ):= by
    rw [PriceCompiler.params_eq R.alloy.B.valid i]
    have hq:= Z'.sense; have hr:= Z'.tall
    apply hw _ _ ( step_paid ( S ) i ) _ ( R.alloy.B.valid.pays i ) _ ( ( Nat.le_add_right .. ).trans hx ) _ (by omega) _ (by omega) _ (by omega)
 let x:= xd
 obtain ⟨hP,hK⟩:= ht.allowance pB hh (( Ψ i ).beta) ((later R π Γ Ψ v hℓ hz).beta.symm ▸ trial_in (( R.T.sticks N n|>.prices _ ( Nat.zero_le _) hz).2))
 let l:= Spill.Raffle.pad r
 let s:ℝ:= ( Φ i )^l
 have hp : 1 ≤ xd:= (S).fits.delayed i|>.le
 have hv' : 0 < xd:= zero_lt_one.trans_le hp
 have hs:1≤ s:= one_le_pow₀ hp
 have hCL : Σ_= CL:= Spill.Raffle.regular G ((S).params i) _ _ _ _ pB xd hh.2.2 hh.2.1
 obtain ⟨f,hf,hT⟩:= Uplink.runway R (Y'.ready C) D Q π Γ Ψ v Y'.station hℓ hv hd hz
 obtain ⟨A',f',⟨K⟩,hf'⟩:= hT.room
 let V:= Spill.Foundry.intake ( Ψ i ) T (Gp) K hf'
 let p := Ξ' V
 have hX : Spill.allOver pB ^ r * ( Σ_ * 1 ) ≤ (Willow.haloSlack (( Ψ i ).p.B))*s:= by
    rw [mul_one, hCL]; exact hK.trans_eq (mul_comm ..)
 have hκ : V.hard.Paid w ( Ψ i ).p.B qT Zt:= by
    apply Hard.mono V.hard ( Spill.Foundry.prices (Ψ i) T Gp K hf' Yv hP hs hX )
    refine ((mul_le_mul_of_nonneg_left hf (pow_nonneg (zero_le_one.trans hs) _))).trans_eq ?_
    unfold need; rw [ Real.rpow_neg hv'.le, Real.rpow_natCast, Real.rpow_neg hv'.le, Real.rpow_natCast,pow_add, pow_mul, glyph R ]; change s^_ * (δ * ((xd^d) * s^Z'.pieces)⁻¹) = _; field_simp
 obtain ⟨hH,hQ⟩:= Spill.Foundry.retention (Ψ i) Gp K hf' hM
 refine ⟨V,⟨Yv,hM,hH,hQ,Spill.Foundry.empty_lit ( Ψ i ) V qT ( Ψ i ).p.B , Hard.mono _ hκ (le_trans (mul_le_of_le_one_right (Graces.glyphBound S i).1.le (Real.rpow_le_one_of_one_le_of_nonpos hp (neg_nonpos.mpr (Nat.cast_nonneg _)))) ( Graces.glyphBound S i ).2)⟩, Lamps.loan_monotone _ ( Scene.Armada.paid _ _ _ Yv _ hP ) ( le_of_eq (( mul_one _ ).trans hCL) ), ht.limit,hκ, ?_⟩
 intro t y; exact Spill.Foundry.value (Ψ i) T Gp K hf' Yv hP hs hX rfl t y
end Boot
end YM.QuadraticLocal.Advent.Sycamore
