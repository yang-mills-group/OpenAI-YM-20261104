import YM.QuadraticLocal.Relative.Companion
import YM.QuadraticLocal.Class.Path
/-!
# Admission test repeated over the chosen school path. At the temporary costs.
 Actual holder tape before steps. `Era.Support` always purchased.
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
-- Worker.W.En.Auth with Compensated Poles.S.Std 
variable (Qa: Mentor.Forecast D R.rolls Q φ Q0)
variable {s:ℕ} (r₀:ℕ) (ε:ℝ)
set_option quotPrecheck false
open PaceR
namespace Academy
local notation "tℓ"=> (life R i b Z' ε)
local notation "κ" i:max=> (life R i b Z' ε)
local notation "ξ" i:max=> (rent R m i b)
noncomputable abbrev wages (R:Run G)(w:Θ→ℝ)(k i b:ℕ):= Stoop.radius w ( battery R k i b )
lemma end_paid : Academy.wages R w Z'.pieces b b=w:=by
    funext x; unfold wages Stoop.radius battery; rw [show roof R b b=1 by simp [roof],one_pow, div_one]
local notation "ν!" i:max=> (Academy.wages R w Z'.pieces i b)
lemma pays_step (hi:i<b) : Academy.wages R w Z'.pieces i b=Stoop.radius (ν! (i+1)) ( fare_R R Z'.pieces i ) := by
    funext x; unfold wages Stoop.radius; rw [ div_div, Sycamore.steps R Z' hi, mul_comm ]
lemma wage_pos (hw:∀ x,0<w x) (i:ℕ) : ∀ x,0 < Academy.wages R w Z'.pieces i b x:= by intro x; exact div_pos (hw x) (zero_lt_one.trans_le ( Sycamore.charged R ))
variable (Sx:Set Θ)
def Author (i:ℕ)(u: Pupil (Ψ i) R₀ ( Affinity.Wallet Actors)):= Ribbon R D Ψ (φ:=φ) (i:=i) Actors U η Z' Sx ( Academy.wages R w Z'.pieces i b ) (Sycamore.life R i b Z' ε) u
local notation "tε" z:max=> (Author (b:=b) R D Ψ (φ:=φ) Actors U w η Z' ε Sx z)
variable (program:∀ i :ℕ,∀ d:m≤ i, i<b → Lesson R hk D Q π Γ d (N:=N))
-- proof/program NOT keeping step occupancy AFTER selecting view.H planned.Policy.Time.World.Clock`. uses same V₁ for horizon.Tutor. `Life.Rich Resident Psi Monitor`.
def Studies (hi:m≤ i) (h:i<b) (Fx: Pupil (Ψ (i+1)) R₀ ( Affinity.Wallet Actors)) (u: Pupil (Ψ i) R₀ ( Affinity.Wallet Actors)):=∃ a:Author (b:=b) R D Ψ (φ:=φ) Actors U w η Z' ε Sx (i+1) Fx, Eraser.LessonWith R hk D Q π Γ Ψ Q0 hi Actors U (Academy.wages R w Z'.pieces (i+1) b) η Z' (Sycamore.life R (i+1) b Z' ε) Sx Fx a (program i hi h) Qa u
local notation "Φ_" i:max=> (Pupil (Ψ i) R₀ ( Affinity.Wallet Actors))
variable (Ξ : Pupil (Ψ b) R₀ ( Affinity.Wallet Actors)) (m₁:ℕ) (hμ:m₁ ≤ b)
-- Currency `w` here already temporarily resized for window; restore across whole region later
local notation "Θ☆" m:max=> (Φ_ m)
structure Stud {m₀:ℕ} (K:∀ i:ℕ
     ,∀ ht:m₀≤ i, i≤b→ Pupil (Ψ i) R₀ ( Affinity.Wallet Actors)) : Prop where
    landed : m₀≤ b
    head : m≤ m₀
    beginning : K b landed le_rfl=Ξ
    teachers i (ht : m₀ ≤ i) (hv:i≤b) : Author (b:=b) R D Ψ (φ:=φ) Actors U w η Z' ε Sx i (K i ht hv)
    graduates i (ht : m₀ ≤ i)(hv : i < b): Academy.Studies R hk D Q π Γ Ψ Q0 Actors U w η Z' Qa ε Sx program (head.trans ht) hv ( K (i+1) (Nat.le_succ_of_le ht) hv ) ( K i ht hv.le )

-- inside one window.Shape.Q_Frame pilot chosen `program` & `Qu.Call`. need actual Concourse obligations and initial teacher.
variable (Yq:Oak.Tutoring.Quarterly R D Q C Q0 Qa) (hL:b≤N)(hA:Sycamore.Session (ε:=ε) R m b r₀ k Z')
local notation "К"=> (Life.Program.El_T) -- placeholder
variable [Nonempty (Affinity.Wallet Actors)]
include v g Ξ Z' Yq hL hA
set_option maxHeartbeats 800000
lemma progress (hi:s≤b)(hm:m≤ s) (hV:ε≤1/8) (he: Author (b:=b) R D Ψ (φ:=φ) Actors U w η Z' ε Sx b Ξ) : ∃ K,Academy.Stud (m₀:=s) R hk D Q π Γ Ψ Q0 Actors U w η Z' Qa ε Sx program Ξ K:= by
 induction hi using Nat.decreasingInduction with
 | self=>
     let K(i:ℕ) (h:b≤ i) (u:i≤ b):= ( le_antisymm h u ▸ (Ξ) : Pupil (Ψ i) R₀ ( Affinity.Wallet Actors)); refine ⟨K,⟨le_rfl,hm,rfl,fun i ht hi=> ?_,fun i hi hv=> by omega⟩⟩; have hrK:i=b:=(by omega); subst i; exact he
 | of_succ i hi ih=>
     obtain ⟨K,hK⟩:= ih (Nat.le_succ_of_le hm); obtain ⟨u,ht,hg⟩:= Eraser.admits_next R g hk D Q π Γ Ψ v C Q0 hm Actors U (ν! (i+1) ) η Z' ( κ (i+1) ) Sx ( K (i+1) le_rfl hi ) ( hK.teachers (i+1) le_rfl hi ) ( program i hm hi ) Qa r₀ hi hL hA rfl hV Yq
     let K₀(d:ℕ) (h:i≤ d)(hp:d≤ b):= if hd : i=d then hd ▸ u else K d (show i+1≤d from by omega) hp
     have heq(d:ℕ)(h:i<d)(hv:d≤b): K₀ d h.le hv=K d h hv:= dif_neg h.ne; have hxg:K₀ i le_rfl hi.le=u:= by unfold K₀; rw [dif_pos rfl] -- rfl
     refine ⟨ K₀, ⟨hi.le,hm,(heq b hi le_rfl).trans hK.beginning,?_,?_⟩ ⟩;
     · intro i' h hi'; rcases lt_or_eq_of_le h with hp|rfl; · rw [heq i' hp hi']; exact hK.teachers _ hp hi'
       rw [hxg]; unfold Author; rw [pays_step R w Z' hi]; exact ht
     intro i' h hv; have hp:i < i'+1:=(by omega); rw [heq (i'+1) hp hv]; rcases lt_or_eq_of_le h with hp|rfl; · rw [heq i' hp hv.le]; exact hK.graduates i' hp hv
     rw [hxg]; exact ⟨_,hg⟩
-- launch existence distinct.Roll.State.Book.Progress` from any requested Author before m & b. choose one once initiating Mark Poll.Ph.Settings.Room.Customer`. Keep ALL steps.St.Metadata.Auth. Later activation.WeightLife`. program independent n. good.
end Academy
end Sycamore
end YM.QuadraticLocal.Advent
