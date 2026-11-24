import YM.QuadraticLocal.Cycle.Cap
import YM.QuadraticLocal.Campaign.Coin
import YM.QuadraticLocal.Found.Mastery
/-!
 # Root education. Horizon declared before ANY label choices, along the actual chronology.
 Funding includes
  * output widths through any registered stage, including move through older ↑ancestral
  connectors for every disjoint stamp request. Need sum mark grade through order, not
  all at once.
  * post-block cap equations ALL kernels on each short.actual.Op FY.Coupling frame.
 Heights & windows not universal load. Props on `MintClock.Page.Firm`.
  * incompatible customers at higher grades visit with separate curricula and budgets —
  don't apply simultaneously to claim growing order without includes. One Outcome trajectory
  fixed Run before choosing queries. Doesn't state resulting compatibility; orientation on
  term Market.Shape accounts pre-decisions. Must bind to this signed-comparison interface. 
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
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
namespace MintClock
variable {G:Gauge}
open Poetry.Agenda Earn QuadraticLocal.Mentor
/-- η future width chooses prior.Runtime clock from THIS Ledger. -/
def splits (k:ℕ):= 4*(k+2+3)
open YM.Precision
section pre
variable {P:ℕ→Stage}{S:KernelChoices}{K:MapPrices}
   (R:Roots (G:=G) P K S) (φ:ℕ→ℕ)(k κ x y:ℕ)
local notation "W"=> R.pre
abbrev Memo (n:Side) (k:ℕ):= ∀ c:ℕ,c≤ k+2 → Earn.Width.Memento c n (seed R φ k x) (seed R φ k y) (waist R k x)
variable (he:splits ≤ φ)(hh:StepStages x y)
include he hh
lemma relative :∀ᶠ i:ℕ in atTop,∀ (u:Side),i ≤ u.val → Memo R φ x y u k:=by
    let a:=waist R k x; let q:= seed R φ k x; let p:= seed R φ k y
    have hv:0<q:=stem ..; have hp:0<p:=stem ..; let N:=6*(k+2:ℕ)*Earn.Cable.links*p/q
    filter_upwards [(tendsto_natCast_atTop_atTop («R»:=ℝ)).eventually_ge_atTop N] with i h u hu ξ hξ
    refine ⟨hv,hp,belt_p ..,?_,?_⟩ -- syntax
    · have hx:N≤(u.val:ℝ):= h.trans (Nat.cast_le.mpr hu); unfold N at hx; rw [div_le_iff₀ hv] at hx; refine le_trans ?_ (hx.trans_eq (mul_comm ..)); gcongr
      try assumption
    apply le_trans (b:=p*(φ k+1:ℕ)) _ (rightWing R φ x y k hh); have he:4*(ξ+3) ≤ φ k+1:=by have ht : 4*(k+2+3)≤ φ k:= he k; omega
    rw [mul_comm p]; refine mul_le_mul_of_nonneg_right (by exact_mod_cast he) hp.le
omit hh
-- StepStages both neighbors possible. side.N preceding fonts.User.Buffer.Syntax.Frame.Progress
noncomputable def Employment (R:Roots (G:=G) P K S)(φ:ℕ→ℕ)(x:ℕ)(D:Side):Prop:=2*Earn.Cable.links ≤ D.val ∧∀ y:ℕ,StepStages x y→∀ k:ℕ,k+2≤ x → Memo R φ x y D k
lemma opens : ∃ κ: ℕ→ℕ,∀ x:ℕ,∀ D:Side,κ x ≤ D.val → Employment R φ x D:=by
 have hz (x:ℕ) : ∀ᶠ i:ℕ in atTop,∀ D:Side,i ≤D.val→ Employment R φ x D:=by
    let v i y:= ∀ (k:ℕ), k+2 ≤ x→ ∀ u:Side,i ≤ u.val → Memo R φ x y u k; have hv y (hh:StepStages x y): ∀ᶠ i in atTop,v i y:= ((eventually_all_finset (I:= Finset.Iic x)).mpr (fun k _=> relative R φ k x y he hh)).mono fun z hz k hk=> hz k (mem_Iic.mpr (by omega))
    filter_upwards [ Filter.eventually_ge_atTop (2*Earn.Cable.links), eventually_transitions x atTop (fun y i=>v i y) hv] with i hh h z hz; exact ⟨hh.trans hz,fun y he k h₁=> h y he k h₁ z hz⟩
 choose k hk using fun x=> (hz x).exists; exact ⟨k,hk⟩
end pre
-- opponent constructors
open Mentor Offices
variable {X : Metals G} (R:Roots (G:=G) X.p.profile X.K X.p.kernel)(D:Rolls X.p)(Q:R.Tab D)
open AnalyticBridge.VerifiedReset
variable {Z:Targets X.p X.K} {E:Expenses Z}{p:Return.Wages}{z:ℕ→ℝ} (W: Repeat.Register D E p z) {M:ℕ→ℕ→Postage} (S: AnalyticBridge.VerifiedReset.Time.Scouts (F:=M))
variable (Z':Targets X.p X.K) (ψ:ℕ→ℕ) (K0:Offices.Books R D Q ψ)(Qa:Mentor.Forecast R D Q ψ K0)
variable {x y a:ℕ}
variable (r : Opportunity x y) (K:Epoch R D x y r)(k n:ℕ)
local notation "T"=> (Z' x y)
local notation "B"=> radiusB
local notation "L"=> (D.L x)
local notation "ω"=> (fun i=> Qa.cost x y i)
local notation "Η"=> (K0.salary x y r)
local notation "κ"=> Burn.horizon K.vac
-- page linked to enrollment in true Er.Roll height and Payment A.B.Frame counts
abbrev ink : Page:= ⟨r.count,k,n,r.stage,(Z' x y).halo,seed R ψ κ x,seed R ψ κ y,waist R κ x,Tolerance y,(Qa.cost x y),fun i=> ((K0.salary x y r).enroll i)^r.count *(K0.salary x y r).price i,(K0.salary x y r).γ⟩
local notation "Φ"=> MintClock.ink R D Q Z' ψ K0 Qa r K k n -- order
namespace Page
variable (h : Employment R ψ x (D.L x))(hk:k+1≤ r.stage)(hr:r.count≤Burn.horizon K.vac+2)
include h hk hr
lemma actual : Eligible G L (MintClock.ink R D Q Z' ψ K0 Qa r K k n):=by
    refine ⟨?_,?_,hk,(Qa.reserve x y),(Qa.higher x y),((Η).hU.pow _).mul (Η).hV,(Η).hγ, h.2 y r.meet κ (K.paid.trans r.meet.1) r.count hr,h.1⟩
    · apply (show 0 < Tolerance y from by unfold Tolerance; positivity)
    change Mentor.Tolerance y ≤ (1:ℝ)/2; unfold Mentor.Tolerance; apply one_div_le_one_div_of_le zero_lt_two (show (2:ℝ)≤ (y+1:ℕ) from by exact_mod_cast (show 2≤y+1 from by have := r.pos.trans r.stageFits; omega))
end Page
end MintClock
end YM.QuadraticLocal
