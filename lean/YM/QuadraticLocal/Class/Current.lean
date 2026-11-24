import YM.QuadraticLocal.Class.Registration

/-! # Born with strong re-expression room for every marker load & repeat over close-charge intervals

 Still only the actual densities along the chosen path. In particular not assuming that a
sterile path at some later level can be restarted with a new Wilson coupling; there is only
one `R` here. `Alumni.unmarked_path` reselects no Run. Mark steps in `Diploma` also occur
on one chosen `Concourse` in this quantifier order, with inherited E on this
vacuum is quantitatively more accurate by raising the order. Does NOT
claim the qev contraction here (for arbitrary e nor for this one)! No full horizon compatibility inferred from using the same `Quarterly`.
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
variable (Qa: Mentor.Forecast D R.rolls Q φ Q0) (Yq:Oak.Tutoring.Quarterly R D Q C Q0 Qa)
variable (hw:Spill.Raffle.Warm G D R.alloy.delay φ)
variable (x₀ mH d₀:ℕ) (ε ℓ:ℝ)
include C g Yq hw
variable (hV:0<ε) (hE: ε ≤ 1/8) (hspan:0≤ℓ)
open PaceR
local notation "expect" m:max b:max=> PaceR.Close R mH ℓ m b


/-- Even if a campaign starts with JUST analytic data (and all missing flags), you can
pay and continue without stopping to reselect a vacuum or to assume that all the simulation
partners were inside some pre-step certificate. Keep the full unmasked density. -/
structure Alumni (b i:ℕ) :Prop where
   room : i≤b → (expect i b)→ Boot.need d₀ Z' ≤ R.alloy.B.a.clock.J b
   memory : i≤b → (expect i b) → Attends R Z' ε i b x₀
   unmarked_path : i ≤ b → (expect i b) → ∀ N ≥ b, ∃ (π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)(hk: Burn.horizon k+2 ≤ (R.alloy.B.a.clock.J i)) (A₀:∀ u:ℕ,∀ hh:i≤ u,u < b→ Lesson (N:=N) R hk D Q π Γ hh), Step.PlanV.Path D R.alloy Q (Burn.horizon k) N i π Γ ∧ ∀ n:ℕ,∃ Ψ:(u:ℕ)→RG.Rep G (R.family.side u n), Concourse R.alloy R.kit R.T π Γ i N n k Ψ∧ Topline ( Ψ N ) ( R.family.path.levels.clock.forcedAllowance N ) ∧
           ∀ (Θ:Type)[Fintype Θ][DecidableEq Θ] (R₀: Marker.Census Θ) (Y₀ξ:Θ→Type) [∀ u,AddCommGroup (Y₀ξ u)][∀ u, Module ℝ (Y₀ξ u)] (Actors:∀ u, Set (Y₀ξ u)) [Nonempty (Affinity.Wallet Actors)] (U: ∀ u,Submodule ℝ (Y₀ξ u)) (w:Θ→ℝ)(η:Θ→ℕ),
                (∀ ξb: Pupil (Ψ b) R₀ (Affinity.Wallet Actors), Attire (φ:=φ) R D Ψ Actors U w η Z' ( Sycamore.notice R b Z' ε ) 1 ξb → ∃ Κ, Eon.Diploma R hk D Q π Γ Ψ Q0 Actors U w η Z' Qa x₀ ε ξb A₀ Κ)
                  ∧ ∀ (ι:Type)[ Countable ι ](Ξ: Passport ( R.family.side b n ) Θ) (T:ι→ Row Ξ R₀ G ( Affinity.Wallet Actors )),
                   Scene.Armada T w η (Poetry.Agenda.seed D φ (Burn.horizon k) ( R.alloy.B.a.clock.J b )) 1 Z'.order Z'.pieces Z'.horizon → Tableau U Actors T → ∃ (V:Tint.Incoming Ξ (Ψ b) ( Affinity.Wallet Actors ) Empty R₀), Bare R D Ψ (φ:=φ) Actors U w η Z' T d₀ V ∧ ∃ Κ, Eon.Diploma R hk D Q π Γ Ψ Q0 Actors U w η Z' Qa x₀ ε (Boot.release R Ψ Actors T V) A₀ Κ
include hV hE hspan
lemma lectures : ∀ᶠ b:ℕ in atTop,∀ i:ℕ,Alumni R D Q Q0 Z' Qa x₀ mH d₀ ε ℓ b i:= by
 filter_upwards [learners R g hV hE Z' hspan mH x₀, PaceR.on_tail R g mH ℓ ( Boot.need d₀ Z' )] with b hb hK i
 have ht (hm:i≤b)(hC:PaceR.Close R mH ℓ i b): Boot.need d₀ Z' ≤ R.alloy.B.a.clock.J b:= (hK i hm hC).trans ((S).fits.mono hm)
 refine ⟨ht,hb i,fun hm h N hu=>?_⟩
 let K0:= ( hb i hm h ); let hx0:=( K0.clocksK i le_rfl ).1; let Xq:= Yq.employed;
 obtain ⟨π,Γ,hU,hH⟩:= tender_t D Q A F i k N g hx0 R.T R.tuning.receipts Xq.station Xq.bears Xq.warm (hm.trans hu)
 let A₀ (u:ℕ) (hv:i≤u)(hp:u<b) : Oak.Lesson (N:=N) R hx0 D Q π Γ hv := ( Oak.tale R hx0 D Q π Γ hv (lt_of_lt_of_le hp hu) hU ).some
 refine ⟨π,Γ,hx0,A₀,hU,fun n=>?_⟩
 obtain ⟨Ψ,V,hP⟩:= hH n
 refine ⟨Ψ,V,hP, fun Θ _ _ R₀ Y₀ξ _ _ Actors _ U w η=>?_⟩
 let ξr := Affinity.Wallet Actors
 have he (P: Pupil ( Ψ b ) R₀ ( Affinity.Wallet Actors )) (he: Attire (φ:=φ) R D Ψ Actors U w η Z' ( Sycamore.notice R b Z' ε ) 1 P) := Eon.certificates R g hx0 D Q π Γ Ψ V C Q0 Actors U w η Z' Qa x₀ ε P he Yq hm hu K0 A₀
 refine ⟨he, fun ι _ Ξ T hz ht₁=>?_⟩
 obtain ⟨U₁,hu₁⟩:= launching R hx0 D Q π Γ Ψ V C Q0 Xq hm hu Actors U w η Z' T hz ht₁ hw hP d₀ (ht hm h)
 refine ⟨U₁,hu₁,he _ ?_⟩; exact { hu₁.clothes with repair:= Lamps.loan_monotone _ hu₁.clothes.repair (Sycamore.behalf R Z'|>.le) }
omit hV hE hspan Yq hw
variable (θ0:ℝ)(hΘ:0<θ0) (hψ: MintClock.splits ≤ φ)
include hΘ hψ
-- arbitrary `C` gives additional LawScroll constraints on this Run beyond Year and Raffle.
theorem detention : ∃ (R:Run G), R.family.path.levels.clock.kernel.penalty= θ0∧∃ (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls)(Q0:Mentor.Offices.Books D R.rolls Q φ)(Qa:Mentor.Forecast D R.rolls Q φ Q0), Spill.Raffle.Warm G D R.alloy.delay φ∧ Tutoring.Quarterly R D Q C Q0 Qa:=by
 let P:= MintClock.both (ψ:=φ) G C (Spill.Raffle.scroll G φ)
 obtain ⟨R,hQ,D,Q,Q0,Qa,hP⟩:= Tutoring.funded g P θ0 hΘ hψ
 let Xq:=hP.employed;
 refine ⟨R,hQ,D,Q,Q0,Qa,Xq.obligation.2,?_,hP.monthly,hP.forecast,hP.year,hP.forms,hP.edges,hP.plan⟩; exact ⟨ Xq.station, Xq.bears,Xq.warm,Xq.crews,Xq.leased, Xq.orientation,Xq.sales,Xq.education,Xq.obligation.1⟩

-- cutoff & period chosen AFTER all surgery geometry and accounting installed. Alumni for every
-- fitting school: public Boot supersedes plain Year as also buying the optional initialization.
theorem first : ∃ (R:Run G), R.family.path.levels.clock.kernel.penalty= θ0∧∃ (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls)(Q0:Mentor.Offices.Books D R.rolls Q φ)(Qa:Mentor.Forecast D R.rolls Q φ Q0), Spill.Raffle.Warm G D R.alloy.delay φ∧ Tutoring.Quarterly R D Q C Q0 Qa∧∀ (k:ℕ)(U:School k)(ε:ℝ)(h:0< ε)(he: ε≤1/8)(ℓ:ℝ)(l a d:ℕ),0≤ℓ→∀ᶠ b:ℕ in atTop,∀ i:ℕ,Alumni R D Q Q0 U Qa a l d ε ℓ b i := by
 obtain ⟨R,hp,D,Q,Q0,Qa,hW,hH⟩:= detention g C θ0 hΘ hψ; exact ⟨R,hp,D,Q,Q0,Qa,hW,hH,fun _ Zs ε h he ℓ l a d hℓ=> lectures R g D Q C Q0 Zs Qa hH hW a l d ε ℓ h he hℓ⟩
end Boot
end YM.QuadraticLocal.Advent.Sycamore
