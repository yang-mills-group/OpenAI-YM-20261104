import YM.QuadraticLocal.Vacuum.Pack
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
open Shoot Coat

local notation "Λ"=> (Φ (i+1))
variable (hℓ:m≤ i) (hz: i<N)
local notation "hx"=> (show Burn.horizon k+2≤R.alloy.B.a.clock.J i from hk.trans ((S).fits.mono hℓ))
variable (V₁: Lesson (N:=N) R hk D Q π Γ hℓ)
local notation "Θ₁"=> V₁.entry
variable {U: RG.Rep G (R.family.side (i+1) n)}(x e:ℝ) (hu:U.beta=x)
    (hp:Lives (WheelP.neutral R.alloy).bake N (i+1) n U) (hw:x∈ band R.alloy.B.a (i+1))
local notation "Wp"=> R.alloy.B.a.budget (i+1)
local notation "WI"=> R.alloy.B.a.budget i
local notation "I_"=> R.alloy.B.a.clock.J i
local notation "s_"=> R.metals.p.profile I_
local notation "γ"=> R.kit.v (R.alloy.B.a.clock.J (i+1)) I
local notation "L_"=> R.rolls.L Y
-- use the chosen path, not choosing new model epochs after n
local notation "Wt"=> Burn.Seed U (WheelP.M0 k 0 Wp (π (i+1)) x)
variable (T₁: Burn.Seed U (WheelP.M0 k 0 (R.alloy.B.a.budget (i+1)) (π (i+1)) x))
variable (hT: Burn.Candor (R.alloy.B.a.budget (i+1)) U.activities (Set.range T₁.model) (Burn.silver ( R.alloy.B.a.clock.hatBeta (i+1))) e)
variable (K:Opera.Guide R.alloy.B R.kit.shape N i n U) (hc:Opera.Price R.alloy.B R.kit.shape N i n U K)
open Integration.LocalFormal Tree
variable (hP: Oak.Tutoring.Quarterly R D Q C Q0 Qa)(Ψp: WheelP.Certified R.alloy R.kit) (jJ:ℕ)(Hc μ:ℝ)(hD: DrawVac jJ k Hc μ (R.alloy.B.a.clock.hatBeta (i+1)))
-- ensure β-hat stage.E.
include hℓ hz hw hp hu
lemma hires : ∃ K:Opera.Guide R.alloy.B R.kit.shape N i n U, Opera.Price R.alloy.B R.kit.shape N i n U K := by -- no Lives hp? include!
    obtain ⟨It,hI⟩:= Opera.feature (neutral A) ( F ).shape hz ( F ).pledging.conducts.full ( F ).pledging.conducts.income hp (show U.beta ∈ band S _ from hu.symm ▸ hw)
    exact ⟨It,hI⟩
omit hℓ hz hw hp hu
-- combined existential for the cast. Avoid depending on proof irrelevance for data.
private lemma transport_appear (P:BudgetPoint)(U: RG.Rep G (R.family.side (i+1) n)){M N:Burn.Locale G} {x y e:ℝ} (h:M=N)(hs:x=y) (w : ∃ K: Burn.Seed U M, Burn.Candor P U.activities (Set.range K.model) (Burn.silver x) e) : ∃ K: Burn.Seed U N, Burn.Candor P U.activities (Set.range K.model) (Burn.silver y) e:= by rw [← h,← hs]; exact w
include hℓ hz hw hp hu
include hP Ψp g hc hk hD T₁ hT
local notation "Tω"=> ((2*Coat.gStep x)^(jJ+1))
local notation "✹"=> WheelP.coefficientLoss (s_) (γ) L_ Λ
set_option maxHeartbeats 800000 in
lemma sells (he: e ≤ Hc*( Coat.gStep x )^ ((jJ:ℝ)+1-μ) ) : ∃ (a:Collection.Listing G (R.family.side i n))(V: Collection.Source G (R.family.side i n))(ℓ₀:ℝ), Curfew D Q (A) (F) (hx) Θ₁ x K a V ℓ₀ (Tω+ ✹ * e) :=by
 obtain ⟨hF,h₀⟩:= hD x ( trial_in hw )
 have hh : ( WheelP.M0 k 0 Wp ( π (i+1) ) x ) = ( WheelP.M0 k 0 Wp V₁.entry.extra x ):= by rw [V₁.ticket]
 have hs:= PriceCompiler.beta_eq R.alloy.B.valid i
 obtain ⟨T', hvv⟩:= transport_appear R (Wp) U hh hs ⟨T₁,hT⟩
 have he₁ : e ≤ AllOrder.High.serving (betaF G (Φ i) L_):= by rw [← hs]; exact he.trans hF
 have he':= WheelP.before D Q (A) (F) hP.employed.station.pledge g hz (hx) Θ₁ V₁.studied x hw hu hp T' he₁ hvv K hc Ψp
 obtain ⟨U',s,ℓ,hE⟩:= he'
 obtain ⟨z',hv,hX⟩:=hE.paid.cheap
 refine ⟨U',s,ℓ,{ hE with paid:={hE.paid with cheap:=⟨z',hv,fun w=>budget_loosen (hX w) ?_⟩ }} ⟩
 unfold finalPrice; rw [← hs]; linarith only [h₀]

end Tracks
end YM.QuadraticLocal.Advent.Sycamore
namespace YM.QuadraticLocal.Advent.Sycamore.Tracks
open Function Filter Finset Lattice Wilson RG RG.Supply Pressure Input Org Precision
open Next.Scheduling Next.Scheduling.Clock AnalyticBridge VerifiedReset ConnectedActivityE6 PhysicalNext Repeat
open Progress.DirectedRecipe Payments Push AbsoluteSums PriceCompiler
open AllOrder AllOrder.Transit WheelP AllOrder.Floe AllOrder.Floe.Step PlanV Pane ThroughLaunch
open Roost Legato Graces Extra.Iteration Extra.Histories
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius Asymptotics
variable {G:Gauge}(R:Run G)(g:G.Simple) {k N m n:ℕ}
variable (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls)
variable {φ:ℕ→ℕ}(C:VowsR.LawScroll G φ)(Q0:Mentor.Offices.Books D R.rolls Q φ)
variable (Qa: Mentor.Forecast D R.rolls Q φ Q0)(hP: Oak.Tutoring.Quarterly R D Q C Q0 Qa)(Ψp: WheelP.Certified R.alloy R.kit)
open Shoot Coat Oak Tree Marker
variable (p:ℕ)(A ε:ℝ)
variable (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin)(Ψ:(i:ℕ)→RG.Rep G (R.family.side i n))
local notation "Ζ"=> R.alloy.B.a.clock
-- Demand at each Step must be met; fix one enrolment for all relevant proofs on that range.
structure LessonRental (i n:ℕ)(hi:m ≤ i)(hz:i<N) (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin)(Ψ:(i:ℕ)→RG.Rep G (R.family.side i n))
      (hk: Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m) (V: Lesson (N:=N) R hk D Q π Γ hi):Prop where
    price : let Hk:=(show Burn.horizon k+2≤R.alloy.B.a.clock.J i from hk.trans ( R.alloy.B.a.fits.mono hi )); let v:= R.kit.v ((Ζ).J (i+1)) ((Ζ).J i); let Γ:= R.alloy.B.a.clock.hatBeta (i+1); let δ:= WheelP.coefficientLoss ( R.metals.p.profile ((Ζ).J i) ) v (R.rolls.L ((Ζ).J (i+1))) Γ;
        DrawVac p k A ε Γ → δ ≤ Time.credit G ( R.metals.p.profile ((Ζ).J i) )/8 ∧
        ∀ (U:RG.Rep G (R.family.side (i+1) n)) (x e:ℝ), U.beta=x→ Lives (WheelP.neutral R.alloy).bake N (i+1) n U → x∈ band R.alloy.B.a (i+1) → ∀ (T:Burn.Seed U (WheelP.M0 k 0 (R.alloy.B.a.budget (i+1)) (π (i+1)) x)), Burn.Candor (R.alloy.B.a.budget (i+1)) U.activities (Set.range T.model) (Burn.silver Γ) e → e ≤ A*( Coat.gStep x )^ ((p:ℝ)+1-ε) → ∃ (K:Opera.Guide R.alloy.B R.kit.shape N i n U), Opera.Price R.alloy.B R.kit.shape N i n U K ∧ (∃ (a:Collection.Listing G (R.family.side i n))(V': Collection.Source G (R.family.side i n))(ℓ₀:ℝ), Curfew D Q R.alloy R.kit Hk V.entry x K a V' ℓ₀ (((2*Coat.gStep x)^(p+1))+ δ * e) )
    fg (T:Type) [Fintype T][DecidableEq T] (W:Census T)(U: Comparison.RG02.Bulk.Colors W G (R.family.side (i+1) n)) (F': Forest (R.family.path.levels.clock.op i n).ratio)
        (k₁:(R.family.path.levels.clock.op i n).Choices): Rector.Ledger R hk D Q π Γ Ψ hi hz V U F' k₁

include g hP Ψp
lemma rental (hk: Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)(i :ℕ)(hi:m ≤ i)(hz:i<N)(V: Lesson (N:=N) R hk D Q π Γ hi) (v:Concourse R.alloy R.kit R.T π Γ m N n k Ψ): LessonRental (k:=k) R D Q p A ε i n hi hz π Γ Ψ hk V:= by
 constructor; swap; · intros T _ _ W U F' k₁; have h₁:=hk.trans ( R.alloy.B.a.fits.mono hi ); let Pt : Mentor.Opportunity ((Ζ).J (i+1)) ((Ζ).J i):= ⟨0,1,step_paid R.alloy.B.a i,Nat.zero_le _,by omega,le_rfl⟩; exact Rector.trusted R g hk D Q π Γ Ψ v C Q0 hP.employed hi hz Pt V _ F' k₁ hP.year
 intro hP₀ v' Γt δ hD; refine ⟨?_,fun U x e he ha hs T h hv=>?_⟩
 · unfold δ Γt; rw [PriceCompiler.beta_eq R.alloy.B.valid i]; exact WheelP.supports (m:=i) R.alloy R.kit Ψp -- arg order
 obtain ⟨K,hV⟩:= Tracks.hires R hi hz x he ha hs; exact ⟨K,hV,Tracks.sells R g hk D Q π Γ C Q0 Qa hi hz V x e he ha hs T h K hV hP Ψp p A ε hD hv ⟩ -- arg order.
-- combine supplier lighthouse with arbitrarily many steps on THIS chosen path; iteration.Diploma.Here Mark. Consumer apply `Boot.Y.Year etc`. Need future documentation. Also warm handles explicit sharp. Provide ∀ᶠ m.
local notation "I"=> R.kit
variable (hy:p≤ Burn.horizon k+1)(h2:2≤p)(ha:0≤ A)(hr: ε < 1/2)
include hy h2 ha hr
lemma projection_rentals : ∀ᶠ m in atTop,
       ∀ N≥m, ∃ (π:ℕ→Layout G)(Γ:ℕ→ Pace.Coin)(hk:Burn.horizon k+2≤R.alloy.B.a.clock.J m)(Λ:∀ i:ℕ,∀ hi:m≤ i, i<N → Lesson R hk D Q π Γ hi (N:=N)),
       Step.PlanV.Path D R.alloy Q (Burn.horizon k) N m π Γ ∧ (∀ n,∃ Ψ:(i:ℕ)→RG.Rep G (R.family.side i n), Concourse R.alloy R.kit R.T π Γ m N n k Ψ ∧ (∀ i:ℕ,∀ hi:m ≤ i,∀ hv:i<N, DrawVac p k A ε (R.alloy.B.a.clock.hatBeta (i+1)) ∧ LessonRental R D Q p A ε i n hi hv π Γ Ψ hk (Λ i hi hv))) := by
 rw [eventually_atTop]; obtain ⟨d,hD⟩:= eventually_atTop.mp (requested R g p A ε hy h2 ha hr); obtain ⟨a,ha⟩:= eventually_atTop.mp ( R.alloy.B.a.fits.deep.eventually_ge_atTop ( Burn.horizon k+2 ) );
 refine ⟨max d a,fun m hm N h=>?_⟩; let he : ( Burn.horizon k+2 ) ≤ R.alloy.B.a.clock.J m:= ha m ((le_max_right ..).trans hm)
 obtain ⟨π,Γ,hX,V,hs⟩:= hP.plan m N h k he; refine ⟨π,Γ,he,V,hX,fun n=>?_⟩; obtain ⟨Ψ,s,hS⟩:= hs n; exact ⟨Ψ,s,fun i hi hr=> ⟨hD i ((le_max_left ..).trans (hm.trans hi)), rental R g D Q C Q0 Qa hP Ψp p A ε π Γ Ψ he i hi hr (V i hi hr) s ⟩ ⟩
end YM.QuadraticLocal.Advent.Sycamore.Tracks
