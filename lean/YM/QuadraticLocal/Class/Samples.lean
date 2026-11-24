import YM.QuadraticLocal.Class.Leaves

/-!
# Key.Price distributions from the Alumni path

Costs include unmarked K in the whole `Gallery`. In particular we announce on the actually
calibrated β. This also projects to `FullBudget` and `ExactStep`, not conflating the kernel
winding prices with an actual term's derivative cost (see `Proxy` for normalization there).
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
def launchFee (i:ℕ):ℝ:= Spill.Raffle.fundsOne G ( R.alloy.B.a.params i ) ( Poetry.Agenda.seed D φ (Burn.horizon k) ( R.alloy.B.a.clock.J i ) ) Z'.order Z'.horizon Z'.pieces ( R.alloy.B.a.clock.hatBeta i )
local notation "F_"=> ( launchFee R D (φ:=φ) Z' i )
local notation "CL"=> ( Spill.Raffle.fundsOne G ( h! ) ( µ ) Z'.order Z'.horizon Z'.pieces xd )
local notation "Kq" a:max b:max d:max => ( Key R Ψ (N:=N) Actors U w Vr a b d )
variable (Pt: Attire (φ:=φ) R D Ψ Actors U w η Z' a c Vr)
include v hℓ hz hk A
-- exports even an experimental (non-virgin) launch with its witnesses at original weights
-- Note that the input (at b) hard.Mark here ONLY requires currency 1. Thus output still
-- sharp after a repeat even with unprepared Partner. If at launch using divided budget,
-- use `Bare.crown` for that stronger currency (ph^−d * strong geom).
omit [Nonempty Θ] [Nonempty (Affinity.Wallet Actors)] in
lemma earn : Spill.Raffle.Gains G (h!) µ (Mentor.Tolerance I) Z'.order Z'.horizon Z'.pieces ( Φ i ):= by
    have hx: Burn.horizon k+2 ≤ I:= hk.trans ((S).fits.mono hℓ); rw [PriceCompiler.params_eq R.alloy.B.valid i]; have hq:= Z'.sense; have hr:= Z'.tall; apply A _ _ ( step_paid ( S ) i ) _ ( R.alloy.B.valid.pays i ) _ ( ( Nat.le_add_right .. ).trans hx ) _ (by omega) _ (by omega) _ (by omega)
include Pt
lemma launch_key : Key R Ψ (N:=N) Actors U w Vr ( launchFee R D (φ:=φ) Z' i * c + a ) a (forcedDivisor R.family i)⁻¹ ∧ ( F_ ) ≤ κy:= by
 have hh:= Boot.tunes R π Γ Ψ v hℓ hz
 have hr:= earn R hk D π Γ Ψ v hℓ hz Z' A -- v/hz included?
 obtain ⟨hQ,hF⟩:=hr.allowance p hh (( Ψ i ).beta) ((later R π Γ Ψ v hℓ hz).beta.symm ▸ trial_in (( R.T.sticks N n|>.prices _ ( Nat.zero_le _) hz).2)); have he := Scene.Armada.paid _ _ _ Pt.total _ hQ;
 have hCL := Spill.Raffle.regular G (h!) µ Z'.order Z'.horizon Z'.pieces p xd hh.2.2 hh.2.1;
 rw [hCL] at he; let hW:=Pt.total.positive; refine ⟨publishes R π Γ Ψ v hℓ hz Actors U w Vr hW ( launchFee R D (φ:=φ) Z' i * c + a ) a ((forcedDivisor R.family i)⁻¹) ?_ Pt.school ⟨Pt.seeds, Pt.supplementary⟩ Pt.repair,hr.limit⟩
 refine ⟨Lamps.joinPaid (Lamps.tenure _ _ hW he (le_add_of_nonneg_right zero_le_one)) Pt.repair,?_⟩
 rw [inv_mul_cancel₀ (show forcedDivisor R.family i≠0 from (Graces.glyphBound S i).1.ne')]; exact Pt.policy
omit hk A Pt v hℓ hz -- later exports on ANY receipt not needing hp.acc_R.

local notation "tκ"=> ( Sycamore.notice R b Z' (2*ε) )
local notation "μy"=> (( Φ b )^ε)
local notation "ϕF"=> ( ( Φ b )^(-(s:ℝ)) )
local notation "pℓ"=> ( R.family.path.levels.clock.op i n )
variable (R₀)
variable (hp:Printed R D Ψ (N:=N) (m:=m) (b:=b) (φ:=φ) Actors U w η Z' s ε (R₀:=R₀) Vn Vr)
-- exports ALL on every post and intermediate, including frames. State-of-the-art Seam gates elsewhere
include v hℓ hz hp
lemma print_key : (Key R Ψ (N:=N) Actors U w Vr (( Φ b )^ε) (notice R b Z' (2*ε)) (( Φ b )^(-(s:ℝ)))):= by
 let hW:= hp.market.positive; refine publishes R π Γ Ψ v hℓ hz Actors U w Vr hW μy (notice R b Z' (2*ε)) ϕF ?_ hp.retina ⟨hp.knotted,hp.crown⟩ ?_
 · refine ⟨Lamps.tenure _ _ hW hp.budgets (by linarith only []), Hard.mono _ hp.fire ( min_le_left ( ϕF * δ₀ ) _ )⟩
 exact Lamps.tenure _ _ hW hp.correction (by linarith only [])

local notation "Fc"=> ( Pc )
local notation "Wc"=> ( Display.taste Zr )
local notation "W₀"=> ( Display.taste ( remainder R Ψ Actors Vr ) )
local notation "Wn"=> ( Display.taste Zn )
local notation "pA"=> ( Printed R D Ψ (N:=N) (m:=m) (b:=b) (φ:=φ) Actors U w η Z' s ε Vn Vr )
-- mention explicit roots. Avatar `Carrier` ALWAYS convention β=Ψ.actual, p. θ resolution before receipts. ExactStep preserves even if meter subsequently picks other test valuations.
omit hz
lemma line (hu:i < N)(pf : Key R Ψ (N:=N) Actors U w Vn a c d)(he : Key R Ψ (N:=N) Actors U w Vr a₁ c₁ d₁): ExactStep (avatar R π Γ Ψ v (Nat.le_succ_of_le hℓ) hu) (avatar R π Γ Ψ v hℓ hu.le) Vn.address.origin Vr.address.origin ( Display.taste ( Tint.Patrol.picture Vn.painter Vn.packet ) ) ( Display.taste ( Tint.Patrol.picture Vr.painter Vr.packet ) ):= by
 refine ⟨ fun x=> (by rw [ hp.bind ]; rfl ),fun x=>?_⟩
 have hz := (hp.reads x).symm
 have hx(t:Config G ( R.family.side i n )):= (he.entry.calls x t).1
 have hp'(t:Config G ( R.family.side (i+1) n )):= (pf.entry.calls x t).1
 exact (congr_arg (Integration.LocalComparison.actualPush Z N n i («R»:=R₀)) (funext hp')).trans (hz.trans (funext hx).symm)

end YM.QuadraticLocal.Advent.Sycamore.Eon
