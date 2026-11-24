import YM.QuadraticLocal.Cycle.Bank
import YM.QuadraticLocal.Cycle.Beam
/-!
# Do pay with a moving-stage post-block pGeo
 Based directly on `Page.Hospital`, here ext with `Mentor.Forecast` QR uniform
power of `ϖ=Monitor` growth for the whole worksheet. BEAM calls are per-stage.
The power CAN GROW for later calls in this construction; so demand a genuine
subpower (& exp-poly of loglog) before purchasing any POWER as well as before
any sticker prices. The school restores K radii and tilt quotes using these;
if delivering for any FIXED finite Mark load (cover, count, field height, power,
root & derivative positions, etc), may use on all admitted tail cuts through
proof `Quark.Stature` from the strengthened chosen Run. Stage choices made before ν calls.
-/
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
namespace MintClock
variable {G:Gauge}
open Poetry.Agenda Earn QuadraticLocal.Mentor
variable {X : Metals G} (R:Roots (G:=G) X.p.profile X.K X.p.kernel)(D:Rolls X.p)(Q:R.Tab D)
open AnalyticBridge.VerifiedReset Mentor Offices
variable {Z:Targets X.p X.K} {E:Expenses Z}{p:Return.Wages}{z:ℕ→ℝ} (W: Repeat.Register D E p z) {M:ℕ→ℕ→Postage} (S: AnalyticBridge.VerifiedReset.Time.Scouts (F:=M))
variable (Z':Targets X.p X.K) (ψ:ℕ→ℕ) (K0:Offices.Books R D Q ψ)(Qa:Mentor.Forecast R D Q ψ K0) {x y a:ℕ} (r : Opportunity x y) (K:Epoch R D x y r)(k n:ℕ)
local notation "T"=> (Z' x y)
local notation "B"=> radiusB
local notation "ω"=> (fun i=> Qa.cost x y i)
local notation "Η"=> (K0.salary x y r)
local notation "κ"=> Burn.horizon K.vac
local notation "Φ"=> MintClock.ink R D Q Z' ψ K0 Qa r K k n
variable {P:Protection D}(V:Delays P)
-- true Ticket in calendar. All n order, grade+1≤, etc AND optional Cost growth expiry. If β invalid branches not allowed regardless radius x.

-- chosen power.B.Occ. page-specific Hµ. Enough support.Input.Equal.Work.Clock.
structure Regency :Prop where
   calendar (x y k n:ℕ)(r:Opportunity x y)(K:Epoch R D x y r): n≤y→ k+1≤r.stage → r.count≤ Burn.horizon K.vac+2 → ∃ (q: ℕ), ∀ ξ:ℝ,V.betaEntry x ≤ ξ → ( Page.beam G (D.L x) (MintClock.ink R D Q Z' ψ K0 Qa r K k n) (X.p.profile x) (X.p.profile y) ξ ≤ Delay.fineMonitor G (D.L x) ξ ^ q ) ∧ Delay.fineMonitor G (D.L x) ξ ^ q ≤ Page.reward (betaF G ξ (D.L x)) (Beaming.grain y)
lemma regents (h:∀ (x:ℕ), Employment R ψ x (D.L x)) : ∃ V':Delays P,DelayLe V V' ∧ ∀ x:Delays P, DelayLe V' x→ Regency R D Q Z' ψ K0 Qa x:=by
 let f x y k n (r:Opportunity x y) (K: Epoch R D x y r) (m:ℕ)(ξ:ℝ) := k+1 ≤ r.stage → r.count≤Burn.horizon K.vac+2 → ( Page.beam G (D.L x) (MintClock.ink R D Q Z' ψ K0 Qa r K k n) (X.p.profile x) (X.p.profile y) ξ ≤ Delay.fineMonitor G (D.L x) ξ ^ m ) ∧ Delay.fineMonitor G (D.L x) ξ ^ m ≤ Page.reward (betaF G ξ (D.L x)) (Beaming.grain y)
 have he (x y k n) (r:Opportunity x y) (K: Epoch R D x y r) : ∃ m:ℕ, ∀ᶠ ξ:ℝ in atTop,f x y k n r K m ξ:=by
    by_cases ha:k+1≤ r.stage∧r.count≤Burn.horizon K.vac+2; swap; · exact ⟨0,Eventually.of_forall fun _ hv hr=> (ha ⟨hv,hr⟩).elim⟩
    let T':= MintClock.ink R D Q Z' ψ K0 Qa r K k n; let Z₀:=(D.L x); have ht:Page.Eligible G Z₀ T' := Page.actual R D Q Z' ψ K0 Qa r K k n (h _) ha.1 ha.2
    obtain ⟨m,hm⟩:= Page.beam_res G Z₀ T' (X.p.profile x) (X.p.profile y) ht; let u ξ:= Delay.fineMonitor G Z₀ ξ; have hp₀ : Reserve G Z₀ (fun ξ=> (u ξ)^m):= Reserve.pow Reserve.monitoring _; refine ⟨m,?_⟩; filter_upwards [hm, ( Page.tender G Z₀ (by unfold Beaming.grain; positivity:0< Beaming.grain y) _ hp₀)] with ξ h₁ h₂; exact fun hv hh=> ⟨(le_abs_self _).trans h₁,h₂⟩
 choose m hm using he; let Pfl x y k n (r:Opportunity x y) K:= f x y k n r K (m x y k n r K)
 let g x ξ:= ∀ y k n (r : Opportunity x y) (K:Epoch R D x y r) (h : k≤ y) (hk:n≤ y), Pfl x y k n r K ξ
 have hp (x y:ℕ):∀ᶠ ξ in (atTop:Filter ℝ),∀ k∈Iic y,∀ n∈Iic y,∀ (r:Opportunity x y)(K: Epoch R D x y r), Pfl x y k n r K ξ:=
    (eventually_all_finset _).2 (fun k _=> (eventually_all_finset _).2 (fun n _=> eventually_all.mpr (fun r=> eventually_all.mpr (fun K=>hm x y k n r K))))
 obtain ⟨q,-,ht,hU⟩:= collect_upper V.betaEntry g (fun x=> (eventually_transitions x atTop _ (fun y _=> hp x y)).mono (fun z h y k n r K hk hn => h y r.meet k (mem_Iic.mpr hk) n (mem_Iic.mpr hn) r K)); refine ⟨{V with betaEntry:=q},⟨ht,le_rfl, le_rfl,le_rfl⟩,fun Y hy=>⟨fun x y k n r K hn hk hr=>⟨_,fun ξ hξ => hU x ξ ((hy.beta x).trans hξ) y k n r K ( k.le_succ.trans (hk.trans r.stageFits)) hn hk hr⟩⟩⟩

variable (G) (hψ:splits ≤ ψ)
open YM.Precision
-- apply at pre-law shape. expandable with `both`. Each returns a Forecast already tied to the true Education.Book.
include hψ in
def vineyard : LawScroll G ψ where
    clause (E) D PP C R₀ q w Z Q₀ S R Y K T' V:= ∃ Qa: Mentor.Forecast (X:=E) R D Y ψ K, Hospital R D Y C ψ K Qa V∧ Regency R D Y C ψ K Qa V
    permits := by
      intro S Tq R C Eq h; obtain ⟨φ₀,hφ⟩:= opens (G:=G) R ψ hψ
      refine ⟨φ₀,fun l hL D w q Z Q' S' _ P T₀ Y Book _ V=>?_⟩; obtain ⟨Qa⟩:= speculate («X»:=ThroughLaunch.currency S Tq l) R D Y ψ Book
      have hH (x:ℕ): Employment R ψ x (D.L x):= hφ x _ ((hL x).trans (D.large x).need)
      let C': Targets (ThroughLaunch.raise S l) (ThroughLaunch.bearing S Tq) := C; obtain ⟨V',hp,hT⟩:= hospitals («X»:=ThroughLaunch.currency S Tq l) R D Y C' ψ Book Qa V hH; obtain ⟨V'',hs,hE⟩:= regents («X»:=ThroughLaunch.currency S Tq l) R D Y C' ψ Book Qa V' hH; exact ⟨V'',DelayLe.trans hp hs,fun Y hy=>⟨Qa,hT _ (hs.trans hy),hE _ hy⟩⟩

end MintClock
end YM.QuadraticLocal
