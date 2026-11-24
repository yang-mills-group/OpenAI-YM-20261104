import YM.QuadraticLocal.Class.Match
/-!
# Estimates at the original marker weights

`ScaleU.stellar` bounds the painter and old packet using an `Attire` at the
scaled weights. `ScaleU.aster` gives separate bounds on the old, hard and
regular parts of the output packet at the positive weights `w0`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Advent
open Function Filter Finset Lattice Wilson RG RG.Supply Pressure Input Org Precision Next.Scheduling
open Next.Scheduling.Clock AnalyticBridge VerifiedReset ConnectedActivityE6 PhysicalNext Repeat
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
variable (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin)(Ψ:(i:ℕ)→RG.Rep G (R.family.side i n))
variable (v:Concourse R.alloy R.kit R.T π Γ m N n k Ψ)
variable (K₀:TicketP R.alloy R.kit D Q)
local notation "P"=> Ψ (i+1)
local notation "P'"=> Ψ i
local notation "H"=> Opera.Guide R.alloy.B (R.kit.shape)
local notation "wa"=> Time.forecastK S i (R.kit).scout (P).beta
local notation "wp"=> Time.quoteHard S i (R.kit).book (P).beta
local notation "y₀"=> Willow.haloSlack (X).B
local notation "Γ'"=> R.T.history N n
open Integration.LocalComparison VowsR QuadraticLocal.Mentor
variable {φ:ℕ→ℕ} (C:VowsR.LawScroll G φ) (Q0:QuadraticLocal.Mentor.Offices.Books D R.rolls Q φ)
variable (Y':VowsR.Chamber C R.kit D Q Q0)
local notation "pE"=> Y'.education
local notation "hZ"=> Y'.station.pledge
local notation "hr"=> Y'.ready C
variable (hℓ:m≤ i) (hz: i<N)
local notation "ℓ"=> (R.alloy.B.a.S.oneStep i n).exact_size
variable (Pt:QuadraticLocal.Mentor.Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i))
variable (X': Card R.rolls D (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i) (R.alloy.B.a.clock.adm (i+1)) (Burn.horizon k)) (hP:Journey D R.alloy (m:=i) (N:=N) X')
local notation "hx"=> (show Burn.horizon k+2≤R.alloy.B.a.clock.J i from hk.trans ((S).fits.mono hℓ))
open Oak
open Buffered
open Marker QuadraticLocal.Tint QuadraticLocal.Syl
namespace Sycamore
open Earn
variable {Θ ι ιw α : Type} [Fintype Θ][DecidableEq Θ]{R₀: Marker.Census Θ}
variable {W': Θ→Type} [∀ i,AddCommGroup (W' i)][∀ i,Module ℝ (W' i)]
variable (Actors:∀ i, Set (W' i))(U:∀ i,Submodule ℝ (W' i))
variable (w:Θ→ℝ)(η:Θ→ℕ)(Z':School k)
local notation "T" j:max=> Pupil (Ψ j) R₀ ( Affinity.Wallet Actors )
local notation "money" i:max=> ( Poetry.Agenda.seed D φ (Burn.horizon k) ( R.alloy.B.a.clock.J i ))
set_option quotPrecheck false
local notation "vR"=> ( (Ψ i).p.supportExponent )
local notation "W0" => (Ψ i).p.B
variable (a c₀:ℝ)
local notation "X₀"=> T i
variable (Ξ: Pupil ( Ψ (i+1) ) R₀ ( Affinity.Wallet Actors ))
variable (E : Attire (i:=i+1) R D Ψ (φ:=φ) Actors U w η Z' a c₀ Ξ)
variable (V₁: Oak.Lesson (N:=N) R hk D Q π Γ hℓ)
local notation "pC"=> (Ξ).painter
local notation "xC"=> (Ξ).packet
local notation "K₁"=> (Ξ).address
local notation "k0"=> V₁.entry
local notation "µ"=> (R.family.path.levels.clock.op i n).ratio
local notation "Q_"=> ( PriceCompiler.step_paid ( S ) i )
local notation "pH"=> (School.room Z' Q_ hx)
local notation "j'"=> Z'.order
local notation "S_i"=> (money (i+1))
include E
local notation "Vₜ"=> ( voters R hk D Ψ (φ:=φ) hℓ Actors U w η Z' a c₀ Ξ E )
variable (Qa: Mentor.Forecast D R.rolls Q φ Q0)
local notation "Kp"=> (Ξ).packet
local notation "G'"=> ( Coat.gStep (P).beta )
local notation "g'"=> ( Coat.gStep (( Ψ i ).beta))
local notation "Ep"=> Oak.era R hk D Q π Γ hℓ pH V₁
local notation "uP"=> ( Mentor.Cruise.publish D R.rolls Q A φ Q0 pH Ep (ℓ) pC Z'.order Vₜ k0)
local notation "qρ"=> ( Mentor.Cruise.funded D R.rolls Q A φ Q0 pH Ep (ℓ) pC Z'.order Vₜ k0 V₁.studied Qa)
open Rebirth
local notation "tΩ"=> ( Oak.student (n:=n) R hk D Q π Γ Q0 hℓ pH V₁ Qa Actors pC Z'.order Vₜ )
local notation "Yh"=> ( Buffered.born (n:=n) R hk D Q π Γ Q0 hℓ pH V₁ Qa Actors pC Z'.order Vₜ )
local notation "ψ"=> (Poetry.Agenda.seed D φ (Burn.horizon k))
variable {J:Type}
local notation "φξ" Λ:max=> Sycamore.pupil R hk D Q π Γ Ψ Q0 hℓ Actors U w η Z' a c₀ Ξ E V₁ Qa Λ
local notation "X_" v:max=> ( (φξ v) )
open Integration.LocalComparison
open PaceR
variable {ε ℓq:ℝ} (mU:ℕ)
local notation "Ω"=> (Oak.expenseReal R hk D Q π Γ Q0 hℓ pH V₁ Qa Z'.order Z'.horizon)
local notation "V'"=> (Oak.figureReal R hk D Q π Γ Q0 hℓ pH V₁ Qa Z'.order Z'.horizon)
local notation "Ξv"=> Buffered.Reborn R hk D Q π Γ Ψ Q0 hℓ pH V₁ Qa Actors U pC xC w η Z'.order Z'.horizon Vₜ a c₀
local notation "Zρ"=> ( Oak.rebate R hk D Q π Γ hℓ pH V₁ )
local notation "Hξ"=> ( ( Ψ i ).p.supportExponent )
local notation "ξ"=> ( ( Ψ i ).p.B )
local notation "H₀"=> (roof R m b)
local notation "P₀"=> (budgetR R i)
local notation "f"=> (Φ b)
local notation "T!" i:max=> (Sycamore.life R i b Z' ε)
local notation "Ω₀" i:max=> (Sycamore.rent R m i b)
local notation "U₀"=> Z'.pieces
local notation "δ"=> ( forcedDivisor (Z) i )
local notation "z_e"=> min ((((Φ b)^(-(mU:ℝ))) * δ)) (Real.sqrt ( quoteR R (Ψ (i+1)).beta i ))
variable (ht:i<b)(hb:b≤N)(M':Tint.Incoming (Ξ.address.coarser (R.family.path.levels.clock.op i n).ratio) (Ψ i) (Affinity.Wallet Actors) J R₀) [Countable J]
variable (hK: Sycamore.Attends R Z' ε m b mU)

namespace ScaleU
variable (PiX : Pupil (Ψ i) R₀ ( Affinity.Wallet Actors )) (hw:∀ z,0<w z)
local notation "w'"=> (Eon.minted R m b w)
local notation "U'"=> life R m b Z' ε
local notation "B1"=> ( (Ψ i).p.B )
local notation "φo"=> (Φ b)
local notation "Y_R"=> (PaceR.roof R m b)
local notation "Vw"=> ( money i )
local notation "wh"=> w'
local notation "Rp"=> ( Sycamore.notice R b Z' (2*ε) )
local notation "r𝒮"=> Z'.pieces
variable (fV:Attire (φ:=φ) R D Ψ Actors U ( Eon.minted R m b w ) η Z' ( Sycamore.life R i b Z' ε ) ( Sycamore.rent R m i b ) PiX)
include fV hℓ hK hw
omit E

lemma stellar (ht:i≤b): Scene.Armada PiX.painter w η (money i) (( Y_R )^(2*Z'.pieces)) Z'.order Z'.pieces Z'.horizon∧ PiX.packet.old.Paid w ( (Ψ i).p.B ) Hξ ( Sycamore.notice R b Z' (2*ε) ) :=by
    let H' := Y_R; have hΘ:1 ≤ H':= roof_ge R m b; have hp:= one_le_pow₀ (n:=2) hΘ; have he :0< H':= lt_of_lt_of_le zero_lt_one hΘ; let Ly:= Sycamore.rent R m i b; have hg: (H'^2)^Z'.pieces=H'^(2*Z'.pieces):= (pow_mul ..).symm; constructor
    · apply ( Eon.liftModel (b:=i) R Ψ Actors η PiX («w'»:=w) (r:=H'^2) hw hp fV.total ).higher; rw [← (hg:_= Y_R ^ _)]; exact mul_le_of_le_one_right (by positivity) ( Sycamore.rent_le R hℓ ht )
    apply Lamps.loan_monotone _ (Stoop.retake w _ fV.total.quota hw hp fV.repair) (le_trans _ hK.hope); rw [hg]; apply mul_le_mul_of_nonneg_left _ (pow_pos he _).le; unfold Sycamore.life; exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (zero_le_one.trans (PaceR.roof_ge ..)) (Sycamore.roof_longer R hℓ ht) _) (Sycamore.behalf R Z'|>.le)
omit fV
-- The equality hm identifies the working weights with the rescaling of w0.
variable (w0:Θ→ℝ) (hp:∀ v,0<w0 v)(hm:w=Eon.minted R m b w0)
omit hw
include hp hm E v g Y' hK ht hb
local notation "π'"=> (X_ M')
local notation "Vx"=> ( (Ψ i).p )
local notation "θq"=> Vx.Clock.Price
local notation "f₁"=> (life R (i+1) b Z' ε)
local notation "Kx"=> ( P₀ )
variable (he:a=(Sycamore.life R (i+1) b Z' ε)) (hc: c₀=Sycamore.rent R m (i+1) b)
include he hc
lemma aster (H': (Buffered.Reborn R hk D Q π Γ Ψ Q0 hℓ pH V₁ Qa Actors U (Ξ.painter) (Ξ.packet) w η Z'.order Z'.horizon Vₜ a c₀ M')) : (π').packet.old.Paid w0 ξ (Hξ+1+1) Rp ∧ (π').packet.hard.Paid w0 ξ Hξ ( z_e ) ∧ ( ( Tint.Patrol.picture (π').painter (π').packet ).E.Paid w0 ξ (Hξ+1+1) ((Φ b)^ε) ) :=by
    let XX:=H'; let TT:=π'; let h' := H'.updates; let iT :=Outdoor.promotes R g hk D Q π Γ Ψ v C Q0 Y' hℓ Actors U w η Z' a c₀ Ξ E V₁ Qa mU ht hb M' hK he hc H'; obtain ⟨hT,hQ'⟩:= Outdoor.estimates R g hk D Q π Γ Ψ v C Q0 Y' hℓ Actors U w η Z' a c₀ Ξ E V₁ Qa mU ht hb M' hK he hc H';
    let H0:= PaceR.roof R m b; have hv:1≤H0:= PaceR.roof_ge R m b; let g_V:=(H0^2)^Z'.pieces; let K:= Ω; have hg:0<K:= h'.paysAbove; have hq:g_V= Y_R^(2*Z'.pieces) := (pow_mul ..).symm
    have hℓ': K ≤ Y_R:= H'.Story.Beamwork.trans ( (roof_small R ht).trans ( roof_longer R hℓ ht.le ) ); have hP₁: 4≤ Y_R:= (h'.strong).trans hℓ'; have hx0:1≤H0^2:=one_le_pow₀ hv; let ν:= ((V').outFee G (Ψ i).p); let Y'':= Sycamore.life R i b Z' ε; have hy: notice R b Z' ε≤Y'':= Sycamore.advance R Z';
    have hr₀ : TT.packet.old.Paid w ξ (Hξ+1+1) Y'':= hT; let P_X := hr₀;
    refine ⟨ Lamps.loan_monotone _ (Stoop.retake w0 TT.packet.old iT.total.quota hp hx0 (?_: TT.packet.old.Paid (Stoop.radius w0 (H0^2)) ξ (Hξ+1+1) Y'')) ?_, Hard.mono TT.packet.hard (Stoop.budget w0 iT.total.quota _ hp hx0 (?_: TT.packet.hard.Paid (Stoop.radius w0 (H0^2)) ξ Hξ ((Ω^6)^Z'.pieces * wp))) ?_, ?_⟩
    · exact (Eq.mp (congr_arg (fun d:Θ→ℝ=>TT.packet.old.Paid d ξ (Hξ+1+1) Y'') hm) P_X)
    · rw [show (H0^2)^Z'.pieces= Y_R^(2*Z'.pieces) from hq]; refine (mul_le_mul_of_nonneg_left (?_: Y'' ≤ Sycamore.life R m b Z' ε) (pow_nonneg (zero_le_one.trans hv) _)).trans hK.hope; unfold Y'' Sycamore.life; exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (zero_le_one.trans (PaceR.roof_ge ..)) (Sycamore.roof_longer R hℓ ht.le) _) (Sycamore.behalf R Z'|>.le)
    · have hQ : TT.packet.hard.Paid w ξ Hξ ((Ω^6)^Z'.pieces* wp) := H'.force; exact (Eq.mp (congr_arg (fun d:Θ→ℝ=>TT.packet.hard.Paid d ξ Hξ _) hm) hQ)
    · rw [show (H0^2)^Z'.pieces= Y_R^(2*Z'.pieces) from hq]; exact hQ'
    let Yv:= TT.painter; let cc:= Sycamore.rent R m i b; let Xv:= ( ( Tint.Patrol.picture TT.painter TT.packet ).E ); have hX : Xv.Paid w ξ (Hξ+1+1) (ν*cc + Y''):= Lamps.joinPaid (Scene.Armada.paid Yv w η iT.total ((Ψ i).p) h'.soon) hr₀; refine Lamps.loan_monotone _ ( Stoop.retake w0 Xv iT.total.quota hp hx0 (Eq.mp (congr_arg (fun d:Θ→ℝ=> Xv.Paid d ξ (Hξ+1+1) _) hm) hX) ) ?_; rw [show (H0^2)^Z'.pieces= Y_R^(2*Z'.pieces) from hq]; apply le_trans _ hK.finance; rw [pow_add]; apply mul_le_mul_of_nonneg_left _ (pow_nonneg (zero_le_one.trans hv) _); let he:= hK.seat i hℓ ht.le; have hℓ: ν*cc≤ K:= (mul_le_of_le_one_right h'.minted.le (Sycamore.rent_le R hℓ ht.le)).trans h'.quote;
    let Lw:= Y_R; have hx0 : K≤ Lw:= hℓ'; nlinarith only [ hℓ, (show Y'' ≤1 from he), (show 4 ≤ Lw from hP₁), hx0, (show 0≤ (Lw-3)^2 from sq_nonneg _) ]
end ScaleU
end Sycamore
end YM.QuadraticLocal.Advent
