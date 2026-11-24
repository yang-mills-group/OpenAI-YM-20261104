import YM.QuadraticLocal.HaloMix.Lotus
import YM.QuadraticLocal.Neighborhood.Theory
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset Matrix
open Push Push.AbsoluteSums PriceCompiler PhysicalNext Repeat Further.PhysicalPeriodLimitF933
open ConnectedActivityE6 Push.Uniform Next.Scheduling Extra.Iteration
open ThroughLaunch Height Opera Boulevard Trio Slide Sienna Fare Lapis Coat
open Input Org Supply Roost Primitives.TwoWave.RealSlice
open AllOrder AllOrder.Burn AllOrder.Ink AllOrder.Ink.Money
open AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit AllOrder.Wheel
open AllOrder.Wheel.Ride AllOrder.Wheel.Ride.Pair AllOrder.Catch
open QuadraticLocal.Sunrise QuadraticLocal.Echo RemainderComparison
open Legato.VowsR
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
namespace MintClock.Pavilion.Quantity
variable {G:Gauge}
open Poetry.Agenda Earn QuadraticLocal.Mentor
variable {X : Metals G} (R:Roots (G:=G) X.p.profile X.K X.p.kernel)(D:Rolls X.p)(Q:R.Tab D)
open AnalyticBridge.VerifiedReset Mentor Offices
variable (Z:Targets X.p X.K) (ψ:ℕ→ℕ)(K0:Offices.Books R D Q ψ){P:Protection D} (V:Delays P)
/-!
 # Cost of reading the same receipts from root instead of site ledgers.

 Purchase post-L at either end of the actual step, even the initial i=b
 when not going until later. Use polynomial-in-ϖ ROOT transfer.BEFORE
 all periods.Setup.Stronger.C.Sizes.Result.C. Cap at ANY μ≤the actual
 stage level: recurrency on all typed roots(Teller even multiple clusters).
 An optional Sect.Position bill pitch for `Θ.Rooted and Halo_energy`.
-/
variable {x y:ℕ}
local notation "L"=> D.L x
local notation "Ω"=> Delay.fineMonitor G L
local notation "rB"=> radiusB
local notation "Bf"=> fun i:ℝ=> radiusB (betaF G i L)
local notation "pf"=> fun i:ℝ=> betaF G i L
open QuadraticLocal.Neighborhood QuadraticLocal.Neighborhood.Aperture
open Extra.Multi
-- Actual fee pre/post.Pilot selects pure Stage and occupancy, including hover.Support
abbrev parkK (p k u m:ℕ) := (m:ℝ) * siteFactor u
abbrev parkE (p k u m:ℕ) := ((((3*(4*u+2):ℝ))^(p*k) * ((p*k).factorial:ℝ)) * k.factorial) * parkK p k u m
def arena (p k u m:ℕ) :ℝ:= (1+parkK p k u m) + parkE p k u m
local notation "Sx"=> X.p.profile x
local notation "Sy"=> X.p.profile y
local notation "UB"=> fun t=> radiusB (betaF G t L)
-- gear not specifying Volume; all at normalized coupling width.Display.Currency.Program.Period.Actor.We.Scope`. cost measure monitor in THIS step.Local.
abbrev bill (P:Stage)(u q:ℕ) := arena P.power P.order u q
lemma seat (p:BudgetPoint) (μ:ℕ): arena p.power p.order p.B μ= (1+muQ p μ)+muE p μ:=rfl
lemma park_mono (p k u :ℕ){m n:ℕ}(hp:m≤n) : arena p k u m ≤ arena p k u n:= by
    have hW (m n :ℕ) (h:m ≤ n): parkK p k u m ≤ parkK p k u n:= mul_le_mul_of_nonneg_right (by exact_mod_cast h) (by unfold siteFactor; positivity)
    unfold arena; refine add_le_add (add_le_add_right (hW _ _ hp) 1) (mul_le_mul_of_nonneg_left (hW _ _ hp) (by positivity))
-- accept larger bills at that delay. Cost estimates.
lemma reserve (p k n:ℕ){U:ℝ→ℕ}(h:Reserve G L (fun t=>(U t:ℝ))): Reserve G L (fun t=>arena p k (U t) n):= by
   let s t:=(2*(16*(U t:ℝ)+9)); let g t:=3*(4*(U t:ℝ)+2)
   have hs:Reserve G L s:=(Reserve.const _).mul (((Reserve.const _).mul h).add (Reserve.const _))
   have hg:Reserve G L g:=(Reserve.const _).mul (((Reserve.const _).mul h).add (Reserve.const _))
   have h:Reserve G L (fun t=>parkK p k (U t) n):= (Reserve.const _).mul ((Reserve.const _).mul (hs.pow _))
   exact ((Reserve.const _).add h).add ((((hg.pow _).mul ( Reserve.const _ )).mul (Reserve.const _)).mul h)

structure Campus (v:ℕ)(x y:ℕ)(t:ℝ) :Prop where
    post : bill (X.p.profile y) (radiusB t) y ≤ (Delay.fineMonitor G (D.L x) t)^v
    pre : bill (X.p.profile x) (radiusB (betaF G t (D.L x))) x ≤ (Delay.fineMonitor G (D.L x) t)^v
    roof : (Delay.fineMonitor G (D.L x) t)^v ≤ Page.reward ( betaF G t (D.L x) ) (Beaming.grain y)
    both : (Delay.fineMonitor G (D.L x) t)^v ≤ min ((betaF G t (D.L x))^(1/3:ℝ)) (t^(1/3:ℝ))
    lease : 4 ≤ t ∧ 4 ≤ betaF G t (D.L x)
structure Park (V:Delays P) :Prop where
    permits (x y:ℕ)(hi:StepStages x y) : ∃ (k:ℕ), ∀ t, V.betaEntry x≤ t → Campus (X:=X) D k x y t
-- Issue both root headers.Same x.Surface. Delay for dyadic.Invoice.Member let.Callee.SpaceAssets
private lemma pos (p k u n:ℕ):1 ≤ arena p k u n:= by unfold arena; unfold parkE parkK siteFactor; apply le_add_of_le_of_nonneg (le_add_of_nonneg_right (by positivity)); positivity
lemma pick (hi:StepStages x y) : ∃ k:ℕ,∀ᶠ t:ℝ in atTop,Campus D k x y t:= by
   let t₁ t := bill (X.p.profile y) (rB t) y; let t₂ t:= bill (X.p.profile x) (Bf t) x
   have h₁: Reserve G L t₁:= reserve D _ _ _ Reserve.field
   have h₂: Reserve G L t₂:= reserve D _ _ _ Page.f_res
   obtain ⟨k,hk⟩:= h₁.add h₂; let Ωm t:=(Ω t)^k; have hv:Reserve G L Ωm:= Reserve.pow Reserve.monitoring _; refine ⟨k,?_⟩
   filter_upwards [hk,eventually_ge_atTop (4:ℝ),(Work.E09.betaF_growth G L).eventually_ge_atTop 4, Page.tender G L (by unfold Beaming.grain;positivity: 0< Beaming.grain y) Ωm hv,hv.rate (1/6) (by norm_num),eventually_ge_atTop (G.slopeConstant*Real.log ((L).val:ℝ))] with t ht hu hx hT h Hk
   have hp:0≤t₁ t:= zero_le_one.trans (pos _ _ _ _); have he:0≤t₂ t:= zero_le_one.trans (pos _ _ _ _); have hv:0≤ t:=by linarith
   let z:= pf t; have hw:1≤ z:=by linarith only [(show (4:ℝ) ≤ z from hx)]
   have hl: z ≤ t^2 := le_trans (b:=2*t) (?_) (by nlinarith [hu]); swap; · change t + _≤2*t; linarith
   refine ⟨?_, ?_, hT, ?_, hu, hx⟩
   · rw [abs_of_nonneg (show 0≤ t₁ t + t₂ t from add_nonneg hp he)] at ht; exact le_trans (le_add_of_nonneg_right he) ht
   · rw [abs_of_nonneg (show 0≤ t₁ t + t₂ t from add_nonneg hp he)] at ht; exact le_trans (le_add_of_nonneg_left hp) ht
   apply le_min;
   · exact le_trans ((le_abs_self _).trans h) (Real.rpow_le_rpow_of_exponent_le hw (by norm_num : (1/6:ℝ) ≤ 1/3))
   refine le_trans ((le_abs_self _).trans h) ((Real.rpow_le_rpow ( zero_le_one.trans hw ) hl (by norm_num: (0:ℝ)≤ 1/6)).trans_eq (?_))
   rw [← Real.rpow_natCast_mul hv]; norm_num
lemma builder : ∃ U:Delays P,DelayLe V U∧∀ v:Delays P,DelayLe U v→ Park D v := by
 choose k hk using fun x y (hi:StepStages x y)=>pick D hi
 let u x ξ:= ∀ y (r : StepStages x y), Campus D (k x y r) x y ξ
 obtain ⟨q,-,hq,hA⟩:= collect_upper V.betaEntry u (fun x=> (eventually_transitions x atTop _ (fun y he=> (hk x y he).mono (p:=fun t=>_) (q:=fun t=> ∀ (r:StepStages x y), Campus D (k x y r) x y t) (fun t h _=>h))).mono (fun z h y r=> h y r r)); refine ⟨{V with betaEntry:= q}, ⟨hq,le_rfl,le_rfl,le_rfl⟩,fun v hv=>⟨fun x y r=> ⟨_, fun t ht=> hA x t ((hv.beta x).trans ht) y r ⟩⟩⟩
def book (h:Park D V) (hi:StepStages x y):= (h.permits x y hi).choose
lemma fitted (h:Park D V) (hi:StepStages x y) (t:ℝ)(hp:V.betaEntry x≤ t): Campus D (Quantity.book D V h hi) x y t:= ( h.permits _ _ hi ).choose_spec _ hp

variable (G) 
open YM.Precision
set_option linter.unusedVariables false in
def renter : LawScroll G ψ where
    clause (E) D PP C R₀ q w Z Q₀ S R Y K' T' V:= Park (X:=E) D V
    permits := fun s Tq R C E' _=> ⟨0, fun l hL D w q Z Q' S' _ P T₀ Y Book _ V=>builder (X:=ThroughLaunch.currency s Tq l) D V⟩
end MintClock.Pavilion.Quantity
end YM.QuadraticLocal
