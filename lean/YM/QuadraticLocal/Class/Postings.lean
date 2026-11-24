import YM.QuadraticLocal.Class.Current

/-! # Examining any one step on the consumer's chosen epoch

Return all the data behind comparing the chosen payout to the Fk prescription, for *exactly*
these program settings. Includes the unmarked pledge, rather than treating the general formal
jet comparison off a bare-Wilson proof as sufficient. Optional post comparators can use this
certificate even if their proximate ledger only sees the log-polynomial decomposition.
Keep these receipts at temporary minted weights for the iteration; use `Plot.tolls` to recover
the original cost of the winding errors if needed. None of this licenses comparing to an
**exact** Fk kernel periodisation with no reference to seam tolerance.
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
-- Pupil for any mesh of this path, budgets & wallets not yet charged. Countable life. Records real root address registry; may change by specified Parent in Packet predicate but ALL rolls refer to chosen Owner geometry at the previous step. All marks & Census retained.
variable {Θ ι ιw α : Type} [Fintype Θ][DecidableEq Θ]{R₀: Marker.Census Θ}
variable {W': Θ→Type} [∀ i,AddCommGroup (W' i)][∀ i,Module ℝ (W' i)]
variable (Actors:∀ i, Set (W' i))(U:∀ i,Submodule ℝ (W' i))
variable (w:Θ→ℝ)(η:Θ→ℕ)(Z':School k)
local notation "T" j:max=> Pupil (Ψ j) R₀ ( Affinity.Wallet Actors )
local notation "money" i:max=> ( Poetry.Agenda.seed D φ (Burn.horizon k) ( R.alloy.B.a.clock.J i )) -- hygienic
set_option quotPrecheck false
local notation "vR"=> ( (Ψ i).p.supportExponent )
local notation "W0" => (Ψ i).p.B

variable (a c₀:ℝ)
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
local notation "Vₜ"=> ( voters R hk D Ψ (φ:=φ) hℓ Actors U w η Z' a c₀ Ξ E ) -- parameters
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

include E
local notation "φp" v:max=> (Sycamore.pupil R hk D Q π Γ Ψ Q0 hℓ Actors U w η Z' a c₀ Ξ E V₁ Qa v)
local notation "op"=> ( R.family.path.levels.clock.op i n )
local notation "Side₀"=> R.family.side i n
local notation "Side₁"=> R.family.side (i+1) n
open Integration RunFormalChain
open Marker Affinity Earn RemainderComparison
open Comparison.RG02
open Laurent Stationary AllOrder.Ink Fire Tree Kinetic.Port
local notation "W₁" t:max=> Air.craft pC ( fun i':Ξ.index=> ( (Ξ).painter i' ).paint t ) η (π (i+1)) (Step.tape (Burn.horizon k+2))
local notation "vr"=> (V₁)
local notation "Pp"=> pH
local notation "Ψinp"=> ((Ξ).packet)
local notation "ΨStudy"=> ( LessonR R hk D Q π Γ Ψ Q0 hℓ Actors U w η Z' a c₀ Ξ E V₁ Qa )
variable (Yq:Oak.Tutoring.Quarterly R D Q C Q0 Qa)
namespace Eon
structure Poster (Vr: T i) : Prop where
    born : ∃ (J:Type) (hH:Countable J)(M': Tint.Incoming ((Ξ).address.coarser µ) (Ψ i) (Affinity.Wallet Actors) J R₀),
       Oak.Buffered.Reborn R hk D Q π Γ Ψ Q0 hℓ pH V₁ Qa Actors U pC xC w η Z'.order Z'.horizon Vₜ a c₀ M' ∧ (Vr= by exact φp M')
    read (q':Affinity.Wallet Actors) (u: Stationary.Link G (R.family.side i n)) (Tt: Forest ( R.family.path.levels.clock.op i n ).ratio) (k' :( R.family.path.levels.clock.op i n ).Choices) :
           Tutoring.Rollback R hk D Q π Γ Q0 hℓ pH V₁ Qa Actors pC η Z'.order Vₜ q' u ∧
             Tutoring.Unearthed R hk D Q π Γ Q0 hℓ hz pH V₁ Qa Actors pC w η Z'.order Vₜ c₀ q' Tt k' u ∧
           Rector.Ledger R hk D Q π Γ Ψ hℓ hz V₁ (W₁ q' ) Tt k'
    upstream : Rector.Material R D π Ψ (k:=k) (i:=i+1)
    downstream : Rector.Material R D π Ψ (k:=k) (i:=i)
variable (Fp:Pupil ( Ψ i ) R₀ ( Affinity.Wallet Actors ))
variable (hv:Step.PlanV.Path D R.alloy Q (Burn.horizon k) N m π Γ)
local notation "pf" u:max=> Poster R hk D Q π Γ Ψ Q0 hℓ hz Actors U w η Z' a c₀ Ξ E V₁ Qa u
include g v hv Yq C hz
lemma plot (hc:c₀≤1)(L₀:(ΨStudy Fp)) : pf Fp:= by
 refine ⟨L₀, fun y u Tt kt=> ?_,Rector.bracket R hk D Q π Γ Ψ v C Q0 Yq.employed (Nat.le_succ_of_le hℓ) hz hv Yq.forms,Rector.bracket R hk D Q π Γ Ψ v C Q0 Yq.employed hℓ hz.le hv Yq.forms⟩
 obtain ⟨J,hJ,M',hH,hh⟩:=L₀
 obtain ⟨T₀⟩:= Oak.agrees R hk D Q π Γ Ψ v hℓ hz V₁
 exact ⟨Tutoring.sits R hk D Q π Γ Ψ Q0 hℓ pH V₁ Qa Actors U pC xC w η Z'.order Z'.horizon Vₜ a c₀ y u M' hH, Tutoring.eligible R hk D Q π Γ Ψ v C Q0 Yq.employed hℓ hz pH V₁ T₀ Qa Actors pC w η Z'.order Z'.horizon Vₜ c₀ E.total y Tt kt u _ hH.Story.earning Yq.edges hc, Rector.trusted R g hk D Q π Γ Ψ v C Q0 Yq.employed hℓ hz pH V₁ ( W₁ y ) Tt kt Yq.year ⟩
omit E g v hv Yq C hz
open PaceR
variable (ε:ℝ)
local notation "tℓ" i:max=> (life R i b Z' ε)
local notation "κ" i:max=> (rent R m i b)
variable (agenda:∀ i:ℕ,∀ d:m ≤ i, i<b → Lesson R hk D Q π Γ d (N:=N))
variable (hu:i<b)(hb:b≤N)
local notation "a₁"=> (Sycamore.life R (i+1) b Z' ε)
local notation "c₁"=> ( Sycamore.rent R m (i+1) b )
local notation "ιη"=> ( agenda i hℓ hu )
local notation "vζ" e:max=> ( voters R hk D Ψ (φ:=φ) hℓ Actors U w η Z' a₁ c₁ Ξ e )
local notation "w₀"=> (minted R m b w)
local notation "ω"=> (roof R m b)^2
local notation "h!"=> ω ^ Z'.pieces
variable (hn : Eon.Studies R hk D Q π Γ Ψ Q0 Actors U ( minted R m b w ) η Z' Qa ε agenda hℓ hu Ξ Fp)
-- usable for each posting from Diploma or its `graduates`. z index authenticated using hb.
include g v hv Yq hn C
lemma clips (hxx:i<N) : ∃ e: Attire (φ:=φ) R D Ψ Actors U ( minted R m b w ) η Z' ( Sycamore.life R (i+1) b Z' ε ) ( Sycamore.rent R m (i+1) b ) Ξ, Poster R hk D Q π Γ Ψ Q0 hℓ hxx Actors U w₀ η Z' a₁ c₁ Ξ e ιη Qa Fp:= by
 obtain ⟨px,hp⟩:=hn
 exact ⟨px, plot R g hk D Q π Γ Ψ v C Q0 hℓ hxx Actors U w₀ η Z' a₁ c₁ Ξ px ιη Qa Yq Fp hv ( Sycamore.rent_le R (Nat.le_succ_of_le hℓ) hu ) hp⟩
omit g v hv Yq hn C
-- Recover seam currency (geometric cost already bounded on the temporary enrollment).
-- At fixed arity width tolerances. This bound never loses volume; implies prescribed
-- winding negligible cost remains a winding negligible cost above p + any needed height via
-- the close-stages choices. Not passing through resets here (see `Poster.read`'s `Rollback`).
local notation "Dk" y:max Tt:max k':max u:max=> (Tutoring.scholarship (k:=k) R π hz Actors pC η y Tt k' u)
local notation "Wo" t:max=> Air.craft ( tΩ ) ( fun i'=> ( tΩ i' ).paint t ) η (π i) (Step.tape (Burn.horizon k+2))
local notation "Kℓ"=> (( Integration.RunFormalChain.fromRun R ).step N i n hz)
local notation "δ₁" u:max => ( Tutoring.bill R hk D Q π Γ Q0 hℓ pH V₁ u c₀ )
variable (Tt:Forest ( R.family.path.levels.clock.op i n ).ratio) (k':( R.family.path.levels.clock.op i n ).Choices)(q':ℕ)(Qv:Affinity.Wallet Actors)(u: Stationary.Link G (R.family.side i n))
local notation "kΘ"=> Alliance.miss pC (fun i'=> ( (Ξ).painter i' ).paint Qv ) µ Kℓ Tt k' u (π (i+1)) (Step.tape (Burn.horizon k+2)) uP q'
variable (w₂:Θ→ℝ)(hw:∀ v,0<w₂ v)(hp:w=minted R m b w₂)
variable (hψ : Poster R hk D Q π Γ Ψ Q0 hℓ hz Actors U w η Z' a c₀ Ξ E V₁ Qa Fp)
include hp hw E hψ
include hz
-- no tV growth in link bound if remain with generated weights. Alias **sum on positions** inside each x as supported by actual Books.
lemma tolls (hh:q' ≤ Z'.order): ∃ e:Poly R₀, Comparison.RG02.Order.observe R₀ Z'.order ( ( Dk Qv Tt k' u ).markedLog ( Integration.RunFormalChain.fromRun R ) Z'.order ) q' = Air.discharge ( Wo Qv ) q' ( Stationary.arm G Side₀ 1 u )+ e ∧ Poly.price w₂ e ≤ h! * δ₁ u ∧ HasSum kΘ e ∧ SumBudget (fun i': Club pC=> Poly.price w₂ ( kΘ i')) (h! * δ₁ u) := by
 let Zp:= (hψ.read Qv u Tt k').2.1
 let a:= ω
 have ha:1≤a:= one_le_pow₀ (roof_ge ..)
 have h:0≤ (h!):= pow_nonneg (zero_le_one.trans ha) _
 have hxx (X':Poly R₀): Poly.price w₂ X'≤ h!* Poly.price w X':=by rw [hp]; unfold Poly.price; rw [mul_sum]; refine sum_le_sum fun i _=> ?_; rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (Stoop.recovered w₂ E.total.quota hw ha i) (norm_nonneg _)
 obtain ⟨e,hQ,hV,hE,hP⟩:= Zp.current q' hh
 exact ⟨e,hQ,(hxx e).trans (mul_le_mul_of_nonneg_left hV h),hE,budget_mono (budget_scale h hP) (fun z=> Poly.nonnegative hw _) (fun z=> hxx _)⟩
variable (d:ℕ)(hA: Attends R Z' ε m b d)
include Tt k' Qv
include hA hu
omit hp hw
lemma seam (hzell:‖u‖≤(R.alloy.B.a.clock.hatBeta (i+1)) ^ (R.alloy.B.a.clock.J (i+1))) : h! * δ₁ u ≤ 2* (Φ (i+1)) ^ (1- (Y:ℝ)):= by
    have hp' : 1 ≤ roof R m b:= PaceR.roof_ge _ _ _; let kΩ := (Φ (i+1))
    have hz: 0<kΩ:= zero_lt_one.trans ((S).fits.delayed _); have hk₀ : ( h! ) ≤ Φ b:= by rw [← pow_mul]; exact (pow_le_pow_right₀ hp' (by omega)).trans hA.affair
    have h := hA.half _ (Nat.le_succ_of_le hℓ) hu; have ht : Φ b ≤ 2*kΩ:= by linarith only [h]
    apply le_trans (mul_le_mul_of_nonneg_left ((hψ.read Qv u Tt k').2.1.numbers hzell) (pow_nonneg (pow_nonneg (zero_le_one.trans hp') _) _)); rw [sub_eq_add_neg, Real.rpow_add hz, Real.rpow_one, ← mul_assoc]; exact mul_le_mul_of_nonneg_right (hk₀.trans ht) (Real.rpow_pos_of_pos hz _).le
end Eon
end Sycamore
end YM.QuadraticLocal.Advent
