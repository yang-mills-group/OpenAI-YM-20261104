import YM.QuadraticLocal.Class.Tracks
import YM.QuadraticLocal.Class.Divisor
import YM.Pert.Asymptotics.RawAxis
/-!
# Stating the prices in `g` and after every admissible output

Explicit hypotheses of repeated application (see Boot.lectures & Tracks.purchases).
`Eon.shirt` is available on every Diploma for every r,d after a high-enough
registration. Reserve only at those chosen levels. Age certificates from Year separately.

See also `Eon.constitutes` for the Fk bindings each time.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Advent.Sycamore.Eon

open Function Filter Finset Lattice Wilson RG RG.Supply Pressure Input Org Precision Next.Scheduling
open Next.Scheduling.Clock AnalyticBridge VerifiedReset ConnectedActivityE6 PhysicalNext Repeat
open Progress.DirectedRecipe Payments Push AbsoluteSums PriceCompiler
open AllOrder AllOrder.Transit WheelP AllOrder.Floe AllOrder.Floe.Step PlanV Pane ThroughLaunch
open Roost Legato Graces Extra.Iteration Extra.Histories
open Marker Integration.LocalComparison Affinity Earn
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius Asymptotics

variable {G: Gauge} (R:Run G)
variable {m n i b k N:ℕ}
variable (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
variable (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls)
variable (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin)(Ψ:(i:ℕ)→RG.Rep G (R.family.side i n))
variable (v:Concourse R.alloy R.kit R.T π Γ m N n k Ψ)
variable (hℓ:m≤ i) (hz:i≤N)
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
local notation "M"=> ( rendered Vr.painter p Gp )

local notation "Σ_"=> ( remainder R Ψ Actors Vr )
local notation "δ₀"=> ( forcedDivisor R.family i )
local notation "Ω"=> ( (Vr).address.support )
local notation "Pc"=> (avatar R π Γ Ψ v hℓ hz)
variable (hw:∀ i,0<w i) {a a₁ a₂ c c₁ c₂ d d₁ d₂:ℝ}
variable [Nonempty Θ][Nonempty (Affinity.Wallet Actors)]
open RG3.Script.Picnic Overlay Display
local notation "Ψt" v:max=> (Display.taste v)
local notation "Rω" v:max a:max d:max=> ( Reader R Ψ (N:=N) Actors U w Vr v a d )
local notation "Φ"=> R.alloy.B.a.clock.hatBeta
local notation "I"=> R.alloy.B.a.clock.J i
local notation "xd"=> Φ i

variable {φ:ℕ→ℕ}(C:VowsR.LawScroll G φ)(Q0: Mentor.Offices.Books D R.rolls Q φ) (Qa: Mentor.Forecast D R.rolls Q φ Q0)
variable (A: Spill.Raffle.Warm G D R.alloy.delay φ)
variable (s:ℕ) (ε:ℝ)
local notation "Zr"=> ( Tint.Patrol.picture Vr.painter Vr.packet )
local notation "Zn"=> ( Tint.Patrol.picture Vn.painter Vn.packet )
local notation "tε"=> ( Sycamore.notice R i Z' ε )
local notation "κy"=> MintClock.Page.reward xd ( Mentor.Tolerance I )
local notation "h!"=> ( S ).params i
local notation "µ"=> ( Poetry.Agenda.seed D φ (Burn.horizon k) ( R.alloy.B.a.clock.J i ) )
local notation "F_"=> ( launchFee R D (φ:=φ) Z' i )
local notation "CL"=> ( Spill.Raffle.fundsOne G ( h! ) ( µ ) Z'.order Z'.horizon Z'.pieces xd )
local notation "Kq" a:max b:max d:max => ( Key R Ψ (N:=N) Actors U w Vr a b d )
open PaceR
variable (Ξ: Pupil ( Ψ b ) R₀ ( Affinity.Wallet Actors ))
variable (he:Attire (φ:=φ) R D Ψ Actors U w η Z' ( Sycamore.notice R b Z' ε ) 1 Ξ)
variable (program:∀ i :ℕ,∀ d:m ≤ i, i<b → Oak.Lesson R hk D Q π Γ d (N:=N))
variable (K:∀ i:ℕ,∀ d:m≤ i,i≤b→ Pupil (Ψ i) R₀ ( Affinity.Wallet Actors ))
variable (hA:Sycamore.Attends R Z' ε m b s)(hm:m≤b)(hb:b≤N)
variable (g:G.Simple)(hq: Oak.Tutoring.Quarterly R D Q C Q0 Qa)(hy: Step.PlanV.Path D R.alloy Q ( Burn.horizon k ) N m π Γ)

-- unpack `.Fingerprint`: ordinary output Price & reserved Hard. Supports in `Key`; ethics schedule quote.Metadata
local notation "Wa"=> ( Display.taste Zr )
local notation "Wn"=> ( Display.taste Zn )
local notation "xp" j:max=> ( notice R j Z' (2*ε))
local notation "fc"=> ( (Φ b)^ε )
local notation "τp"=> ( (Φ b) ^ (-(s:ℝ)) )
variable (H:Diploma R hk D Q π Γ Ψ Q0 Actors U w η Z' Qa s ε Ξ program K)
local notation "v_" h:max=> ( K i hℓ h )
local notation "u_" h:max=> ( K (i+1) (Nat.le_succ_of_le hℓ) h )
local notation "FΩ" x:max=> ( launchFee R D (φ:=φ) Z' x )


variable (Ht: Step.PlanV.Path D R.alloy Q ( Burn.horizon k ) N m π Γ)
local notation "y₀"=> Coat.gStep (Ψ i).beta
local notation "xy"=> ( Ψ i ).p
open Oak Rector
-- Keep cost in the stage units.
include hz hℓ v
local notation "B₁"=> ( Pert.Asymptotics.regulatorRun R.family N n i )
-- field reporting parameter as actually requested at site. all powers with threshold normalization
lemma true_b : ( Coat.gStep ( Ψ i ).beta )= Pert.Asymptotics.regulatorRun R.family N n i:= by
    rw [( later R π Γ Ψ v hℓ hz ).beta]; rfl
lemma vacuum_young : Burn.young (Φ i) k ≤ ( 2*Pert.Asymptotics.regulatorRun R.family N n i )^(Z'.order+1):= by
    rw [← (true_b R π Γ Ψ v hℓ hz)]; let c:= (Φ i); have hc:1 ≤ c:= (S).fits.delayed i|>.le; have he: 0<c:= zero_lt_one.trans_le hc
    have hx : 0<Coat.gStep c:= Fare.gS _ he|>.1
    have hz':= trial_in (( later R π Γ Ψ v hℓ hz ).beta.symm ▸ (( R.T.sticks N n|>.prices i ( Nat.zero_le _) hz ).2))
    have ht : Coat.gStep c/2 ≤ y₀:= ( band_gap _ ( Ψ i ).beta he hz' ).1
    apply le_trans _ (pow_le_pow_left₀ hx.le ( show Coat.gStep c ≤ 2*( Coat.gStep ( Ψ i ).beta ) from (by linarith only[ht])) ( Z'.order+1 ))
    unfold Burn.young; rw [ Burn.inv_sqrt c he,← Real.rpow_mul_natCast he.le ]
    apply Real.rpow_le_rpow_of_exponent_le hc
    rw [Burn.sale_eq]; push_cast
    have h': ( Z'.order:ℝ ) ≤ (Burn.horizon k:ℝ)+1:= by exact_mod_cast Z'.price
    unfold Burn.horizon at h'; push_cast at h'; linarith only [h'] -- `linarith` inside term?
omit v hz hℓ
include H hA he hq v hy g
variable (hl:i<b) (r :ℝ) (hr:4*ε≤r) (hε:ε≤1/8)
local notation "tℓ"=> Sycamore.notice R b Z' (2*ε)
local notation "age!"=> Pert.Asymptotics.regulatorRun R.family N n b
local notation "δu"=> ((2:ℝ)^((Z'.order:ℝ)+1-4*ε)) * ( ( age! )^((Z'.order:ℝ)+1-r) )
local notation "κ"=> ( R.family.path.levels.clock.forcedAllowance i )
local notation "Bz"=> ( (Ψ i).p.threshold )
local notation "fyr"=> ( ( 2* ( age! )) ^ ( 2*s ) )
local notation "Uº"=> ( K i hℓ hl.le )
local notation "Vº"=> ( K (i+1) (Nat.le_succ_of_le hℓ) hl )
set_option maxHeartbeats 400000
include hε hr A hℓ
-- σ = current .SupportExponent. Native bells ℝ multislot. Norm through the sturdy Lamp derivative.
lemma shirt (R' : T i) (Qn : T (i+1)) (hs:R'= K i hℓ hl.le) (hv:Qn= K (i+1) (Nat.le_succ_of_le hℓ) hl) : Eon.Output R hk D Q π Γ Ψ v hℓ Actors U w η Z' Q0 Qa s ε program hb hl Qn R' ∧
      ( R'.packet.old.Paid w ( Ψ i ).p.B (σ+1+1) ( ((2:ℝ)^((Z'.order:ℝ)+1-4*ε)) * ( Pert.Asymptotics.regulatorRun R.family N n b )^((Z'.order:ℝ)+1-r) ) ) ∧ R'.packet.hard.Paid w (( Ψ i ).p.B) ((Ψ i).p.supportExponent) (( (2*( age! ))^(2*s) ) * forcedDivisor R.family i) ∧
      R'.packet.hard.Paid w ((Ψ i).p.B) σ ( Real.exp (-(Payments.Pairing.kGoal ( R.kit.book ( R.alloy.B.a.clock.J (i+1) ) ( R.alloy.B.a.clock.J i ) ) (Φ (i+1)) (( Ψ (i+1)).beta))/2 ) ) ∧ R'.packet.hard.Paid w ((Ψ i).p.B) ((Ψ i).p.supportExponent) (R.family.path.levels.clock.forcedAllowance i) ∧ Key R Ψ (N:=N) Actors U w R' fc δu fyr:= by
 subst R' Qn; let R':= Uº
 have Zℓ:= ( true_b R π Γ Ψ v (hℓ.trans hl.le) hb ); have h:= constitutes R hk D Q π Γ Ψ v hℓ Actors U w η Z' C Q0 Qa A s ε Ξ he program K hb g hq hy H hl
 obtain ⟨he',hh⟩:= estate R hk D Q π Γ Ψ v Q0 hℓ Actors U w η Z' Qa s ε Ξ hl (hℓ.trans hl.le) hb hA program K H hr hε
 have hn:= h.finances
 obtain ⟨hk₁,h1,h2⟩:= Eon.force_prices R D π Γ Ψ v hℓ (lt_of_lt_of_le hl hb) Actors U w η Z' (Uº) (Vº) s ε h.finances
 have hw:= h.finances.market.positive; have hu:=(h.view.entry.born.paid).budget
 refine ⟨h,?_,?_, hk₁, h2, Eon.publishes R π Γ Ψ v hℓ (hl.le.trans hb) Actors U w R' hw fc δu fyr ⟨ hu,?_⟩ hn.retina ⟨hn.knotted,hn.crown⟩ ?_⟩
 all_goals rw [← Zℓ]
 · exact he'
 · exact hh
 · exact hh
 exact Lamps.tenure _ _ hw he' (by linarith only [])

end YM.QuadraticLocal.Advent.Sycamore.Eon
