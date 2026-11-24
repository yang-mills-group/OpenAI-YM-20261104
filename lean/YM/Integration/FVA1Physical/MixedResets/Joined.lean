import YM.Integration.FVA1Physical.MixedResets.Late
import YM.SectorNext.VACUUM_NORMALIZATION.Stripped
import YM.Push.SECTOR_MEASURE.Overlap
/-!
# Price and justify the **actual calibrated** step, through PLAN's coupling reset

`LiveStep` supplies both early & late, before AND after calibration, for ONE
full marked answer along the purchased chronology. (There is also the Early estimate
when pushing an arbitrary thermally authorized U of matching layout through the step.)

Do not integrate the signed discrepancy as the error goal. Use `Readout` only to
make sure that the norms proven are at the *right* field-dependent input & output
normalizations, with full integrability & identity on ALL orientations and fields.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.MixedResets
open Function Filter Finset Lattice RG RG.Supply Precision Wilson Marker
open AllOrder AllOrder.Transit WheelP AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Ker
open Push ConnectedActivityE6 Input Org PhysicalNext PhysicalNext.Repeat Legato
open Uniform Next.SectorChange ThroughLaunch Pane AbsoluteSums PriceCompiler
open Primitives.TwoWave Primitives.TwoWave.RealSlice
open Kinetic.Port Progress.ClassicalKin Progress.ClassicalKin.Tent
open Pressure Next.Scheduling Next.Scheduling.Clock AnalyticBridge VerifiedReset
open Roost Legato Graces Extra.Iteration Extra.Histories
open QuadraticLocal QuadraticLocal.Mentor QuadraticLocal.Sunrise QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Sycamore
open Comparison.RG02 Further.PhysicalPeriodLimitF933 Tree
open Oak
open scoped Topology BigOperators Classical

variable {G : Gauge} (R : Run G) {m n i k N : ℕ} (J : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ i, RG.Rep G (R.family.side i n))
  (conc : Concourse R.alloy R.kit R.T π Γ m N n k Ψ)
  {φ : ℕ → ℕ} (clock : Offices.Books D R.rolls Q φ) (ahead : Mentor.Forecast D R.rolls Q φ clock)
  (hi : m ≤ i) (cut : i<N) (L : Lesson (N:=N) R J D Q π Γ hi)
set_option quotPrecheck false
local notation "σ" => R.alloy.B.a
local notation "I" => R.alloy.B.a.clock.J i
local notation "I'" => R.alloy.B.a.clock.J (i+1)
attribute [local irreducible] Till.Tilt.sundry
local notation "C" => R.alloy.B.a.budget i
local notation "Fμ" => R.alloy.B.a.budget (i+1)
local notation "Uu" => (Ψ (i+1))
local notation "P'" => (Ψ i)
local notation "Gm" => (Coat.gStep ((Ψ i).beta))
local notation "Wc" => (Time.quoteHard (σ) i (R.kit.book) (Ψ (i+1)).beta)
local notation "τ" => R.family.path.levels.clock.op i n
local notation "µ" => (τ).ratio
local notation "p₀" => (Burn.horizon k+2)
local notation "g" => Coat.gStep (Ψ (i+1)).beta
local notation "κ" => LocalComparison.forcedDivisor R.family i

variable (cap : QuadraticLocal.Mentor.Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i))
  {Θ ι ιw : Type} [Fintype Θ] [DecidableEq Θ] {R₀ : Marker.Census Θ}
  (o : Earn.Passport (R.family.side (i+1) n) Θ) {X : Θ → Type} [∀ i, AddCommGroup (X i)] [∀ i, Module ℝ (X i)]
  (allow : ∀ i, Set (X i)) (kills : ∀ i, Submodule ℝ (X i))
  (t : Affinity.Wallet allow)
  (M : ι → Earn.Row o R₀ G (Affinity.Wallet allow)) (Z : Tint.Incoming o (Ψ (i+1)) (Affinity.Wallet allow) ιw R₀)
  (w : Θ → ℝ) (grades : Θ → ℕ) (p horizon : ℕ) (e_E funds ηz : ℝ) (s : ℕ)
local notation "Mnew" => (o.coarser ((τ).ratio))
local notation "u" => (Poetry.Agenda.seed D φ (Burn.horizon k) I')
local notation "v" => (Poetry.Agenda.seed D φ (Burn.horizon k) I)
local notation "r" => ((p:ℝ)+1-ηz)
local notation "Ω" => Oak.expenseReal R J D Q π Γ clock hi cap L ahead p horizon
local notation "Ωm" => Oak.figureReal R J D Q π Γ clock hi cap L ahead p horizon
local notation "due" => (8*Ω^(cap.count+1)*e_E + 16 * ((2:ℝ)^ r * (Coat.gStep (Ψ (i+1)).beta)^ r))
variable (F₁ : Tree.Forest (Route.step R i n).ratio)
  (young : Cruise.Voter M (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))) p cap.count cap.stage k (R.alloy.B.a.clock.J i))
  {J' : Type}
local notation "out" => Oak.student (n:=n) R J D Q π Γ clock hi cap L ahead allow M p young
variable (next : Tint.Incoming (o.coarser (R.family.path.levels.clock.op i n).ratio) (Ψ i) (Affinity.Wallet allow) J' R₀)
local notation "W" => (Tint.Patrol.report out next (Coat.gStep (Ψ (i+1)).beta))
local notation "Y" => ( Tint.Patrol.picture M Z )
local notation "spent" => (Ω * funds)
local notation "after" => (Ω^2 * funds)
open MeasureTheory
set_option maxHeartbeats 820000
open Buffered
open QuadraticLocal.Rebirth
local notation "dueCalibrated" => (8*Ω^(cap.count+1)*e_E + 17 * ((2:ℝ)^ r * (Coat.gStep (Ψ (i+1)).beta)^ r))
local notation "new" => ( Mutation.grow out (Γ i) (Oak.grade0 R J D Q π Γ hi L) p₀ p g Gm (Ψ i) next )
local notation "ym" => ( Buffered.born R J D Q π Γ clock hi cap L ahead allow M p young )
local notation "Z'" => ( Tint.Patrol.picture ym new )
local notation "ticket" => ( Oak.rebate R J D Q π Γ hi cap L )
local notation "B" => (Ψ i).p
local notation "A" => (Ψ (i+1)).p
local notation "predict" => Renderer out (π i) (Step.tape p₀) grades p
local notation "receipt" => Renderer ym (π i) (Step.tape p₀) grades p
local notation "preModel" => Route.wilson R N p₀ (π (i+1)) M p
local notation "formal" => Route.reexpress R N p₀ (π (i+1)) M p
local notation "Cal" => Route.calibrator R D Q J π Γ hi L
local notation "Dollars" P:max Lm:max b:max => QuadraticLocal.Lamps.Paid Lm w (P).B ((P).supportExponent+2) b


local notation "vac" => (R.family.path.rep N n i)
local notation "preVac" => (R.family.path.rep N n (i+1))
local notation "scalar" => (Burn.young (R.alloy.B.a.clock.hatBeta (i+1)) k)
local notation "live" => RG.Shoot.Lives (WheelP.neutral R.alloy).bake N (i+1) n (Ψ (i+1))

open SectorNext.Vacuum Push.SectorMeasure
lemma traveler : Nonempty (Route.step R i n).Choices := by
  obtain ⟨y,hy⟩ := exists_alive (R.family.path.levels.blocks i n).branches (1:Config G (R.family.side (i+1) n))
  exact ⟨y⟩

-- field-dependent shared denominator, exactly, including witnesses before/after  normalizing.
-- `actualRatio` recovers full interacting normalized V MARKS as needed. N comes only
-- through the path and initial β, no use of predicted formal reset as if it were true. Keep
-- normalized vacuum multiplication even at empty mode.
local notation "βin" => (Ψ (i+1)).beta
local notation "den" => ( (Route.step R i n).push (Ψ (i+1)).beta ((Ψ (i+1)).eval) )
local notation "ratio" => ( fun y x => ((den x)⁻¹) • (Route.step R i n).push (Ψ (i+1)).beta ( (Y).density y ) x )

structure Readout : Prop where
  hvac : ( P' ).eval=( vac ).eval ∧ ( Uu ).eval=( preVac ).eval ∧ ( P' ).eval=den
  notZero : (∀ x, 0 < (preVac).eval x) ∧ ∀ x, 0 < (den x)
  integ x : Integrable ((Y).density x) (prior G (R.family.side (i+1) n)) ∧
    Integrable ((Z').density x) (prior G (R.family.side i n)) ∧
    ∀ K : Config G (R.family.side i n), Integrable (fun y => (Route.step R i n).density βin y K • (Y).density x y)
      (prior G (R.family.side (i+1) n))
  match_ : ( Z' ).density=( W ).density
  actualRatio : ∀ x y, ( W ).density x y = den y • ratio x y ∧ ratio x y = ((Ψ i).eval y)⁻¹ • ( Z' ).density x y

set_option maxHeartbeats 710000
include conc cut
lemma Calibrated.consummates
    (h : Calibrated R J D Q π Γ Ψ clock ahead hi L cap o allow kills M Z w grades p horizon e_E funds ηz s young next) :
    Readout R J D Q π Γ Ψ clock ahead hi L cap o allow M Z p young next := by
  have hκ := h.kernel
  let hz := later R π Γ Ψ conc hi cut.le; let hx := later R π Γ Ψ conc (Nat.le_succ_of_le hi) cut
  have ha : ( P' ).eval=den := (conc.1.visit i hi cut).ident
  have hp (x : Config G (R.family.side i n)) : 0 < den x := by
    rw [← ha]
    have hσ : (Ψ i).eval=( vac ).eval:=hz.view
    rw [hσ]; exact SectorNext.Vacuum.strictly R.family.path R.T.choice N n i cut.le x
  refine ⟨⟨hz.view,hx.view,ha⟩,⟨fun x => SectorNext.Vacuum.strictly R.family.path R.T.choice N n (i+1) cut x,hp⟩,
    ?_,funext fun t => (h.actual t).2.2,?_⟩
  · intro x; obtain ⟨ha,hb,hc⟩ := h.actual x
    exact ⟨ha, hc.symm ▸ hb.symm ▸ StepData.push_integrable hκ _ ha,fun K => StepData.push_slice hκ K _ ha⟩
  intro x y
  obtain ⟨_,hb,hc⟩ := h.actual x
  refine ⟨?_, ?_⟩
  · rw [hb]; simp only [smul_smul,mul_inv_cancel₀ (hp y).ne',one_smul]
  · rw [ha,hc,hb]

/-- Local complete-case receipt. Intentional two presentations of the answer (and
keep the interim student too, see `.post`): by giving the second here ON THAT K,
we can both exhibit the gain on the unmarked singular E before its uncertainty got read off
and reuse the fully marked output WITH original trajectory β restored. Not claiming the
current-time prices on these configurations carry over to another epoch of the same schedule
without `Ribbon` etc. -/
structure LiveStep : Prop where
  post : Calibrated R J D Q π Γ Ψ clock ahead hi L cap o allow kills M Z w grades p horizon e_E funds ηz s young next
  identification : Readout R J D Q π Γ Ψ clock ahead hi L cap o allow M Z p young next
  coupling : VacuumStep (n:=n) (Ψ:=Ψ) R D Q J π Γ hi L
  canon : ∃ (pre : Locator.Calendar R J D Q π Γ hi L (U:=Ψ (i+1)) (Burn.young (R.alloy.B.a.clock.hatBeta (i+1)) k) F₁) (seed : Burn.Seed (Ψ (i+1)) (WheelP.M0 k 0 (R.alloy.B.a.budget (i+1)) (π (i+1)) (Ψ (i+1)).beta)) (J'':Type) (ht:Countable J'') (Mm : Tint.Incoming (o.coarser (R.family.path.levels.clock.op i n).ratio)
        (Locator.paneling R J D Q π Γ hi L pre.listing pre.source (Ψ (i+1)).beta pre.scalar) (Affinity.Wallet allow) J'' R₀ ),
    Burn.Candor (R.alloy.B.a.budget (i+1)) ((Ψ (i+1)).activities) (Set.range seed.model) (Burn.silver ( R.alloy.B.a.clock.hatBeta (i+1))) scalar ∧
    Locator.Elementary.Newhall R J D Q π Γ Ψ clock ahead hi cut L scalar seed p F₁ pre cap allow kills M Z w grades horizon young e_E funds ηz s Mm Set.univ ∧
    Early R J D Q π Γ clock ahead hi L (Ψ (i+1)) cap scalar o allow kills M Z w grades p horizon e_E funds ηz s F₁ young pre Mm ∧
    (Tint.Patrol.report out Mm g).density = ( Z' ).density ∧
    (Locator.paneling R J D Q π Γ hi L pre.listing pre.source (Ψ (i+1)).beta pre.scalar).eval= ( Ψ i ).eval
  ringing : ∀ (F' : Tree.Forest ((Route.step R i n).ratio)) tag q t, PinnedSeam R D Q J π Γ hi L cut clock cap allow M (p:=p) grades w F' tag funds q t

local notation "bill" pre:max seed:max Mm:max => Locator.Elementary.Newhall R J D Q π Γ Ψ clock ahead hi cut L scalar seed p F₁ pre cap allow kills M Z w grades horizon young e_E funds ηz s Mm Set.univ

variable [Countable J'] [Countable ι] [Countable ιw] [Nonempty (Affinity.Wallet allow)]
set_option maxHeartbeats 790000
lemma joined
    (post : Calibrated R J D Q π Γ Ψ clock ahead hi L cap o allow kills M Z w grades p horizon e_E funds ηz s young next)
    (pre : Locator.Calendar R J D Q π Γ hi L (U:=Ψ (i+1)) (Burn.young (R.alloy.B.a.clock.hatBeta (i+1)) k) F₁) (seed : Burn.Seed (Ψ (i+1)) (WheelP.M0 k 0 (R.alloy.B.a.budget (i+1)) (π (i+1)) (Ψ (i+1)).beta)) (J'':Type) [ht:Countable J''] (Mm : Tint.Incoming (o.coarser (R.family.path.levels.clock.op i n).ratio)
        (Locator.paneling R J D Q π Γ hi L pre.listing pre.source (Ψ (i+1)).beta pre.scalar) (Affinity.Wallet allow) J'' R₀ )
    (vacPaid : Burn.Candor (R.alloy.B.a.budget (i+1)) ((Ψ (i+1)).activities) (Set.range seed.model) (Burn.silver ( R.alloy.B.a.clock.hatBeta (i+1))) scalar)
    (hall : bill pre seed Mm)
    (earned : Earn.Scene.Armada M w grades u funds p cap.count horizon)
    (old : Z.old.Paid w (A).B (A).supportExponent e_E) (full : Z.hard.Paid w (A).B (A).supportExponent 1) :
    LiveStep R J D Q π Γ Ψ clock ahead hi cut L cap o allow kills M Z w grades p horizon e_E funds ηz s F₁ young next := by
  let f := later R π Γ Ψ conc (Nat.le_succ_of_le hi) cut
  have h : live := ⟨f.truep.path.trans (congr_fun (congr_fun R.alloy.B.bases N) _), f.truep.point,f.truep.clip,f.truep.valid,trivial⟩
  have E := pre_price (n:=n) R J D Q π Γ conc clock ahead hi cut L (Ψ (i+1)) cap h scalar seed o allow kills M Z w grades p horizon e_E funds ηz s F₁ young pre Mm hall earned old full
  let r₀ := post.consummates R J D Q π Γ Ψ conc clock ahead hi cut L cap o allow kills M Z w grades p horizon e_E funds ηz s young next
  let y₀ := Classical.arbitrary ( Affinity.Wallet allow ); let t₀ := Classical.choice (traveler R (i:=i) (n:=n))
  refine ⟨post,r₀,?_,⟨pre,seed,J'',ht,Mm,vacPaid,hall,E,funext (fun y => ?_), E.vacancy.actual.trans r₀.hvac.2.2.symm⟩,
    fun F' t' q x => ?_ ⟩
  · exact vacuum_step R D Q J π Γ hi L conc cut _ F₁ t₀ (hall.coherence F₁ t₀ y₀).2
  · exact (E.actual y).2.symm.trans (((post.actual y).2.2.trans (post.actual y).2.1).symm)
  exact also_seam R D Q J π Γ hi L conc cut clock cap allow M young ahead grades F' t' w q x ((hall.coherence F' t' x).1 q) post.mean
end YM.Integration.FVA1Physical.MixedResets
