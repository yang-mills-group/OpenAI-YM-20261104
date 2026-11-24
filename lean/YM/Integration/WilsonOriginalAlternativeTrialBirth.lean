import YM.Integration.WilsonOriginalAlternativeQuietPost
import YM.Integration.WilsonOriginalAlternativeTrialWallet
import YM.Integration.WilsonOriginalAlternativeTrialSource

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeTrialBirth
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6

variable {G : Gauge} (R : Run G) {m N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V : Type} [Fintype V] [DecidableEq V]
  (grades : V → ℕ)
  (order shelf seats i : ℕ) (floor : m ≤ i)
  (physical : Wallet (WilsonOriginalAlternativeFiniteSource.disks (V:=V)) → Config G (R.family.side (i+1) per) → Poly (Stock.census V))


local notation "D_" => (WilsonOriginalAlternativeFiniteSource.disks (V:=V))
local notation "K_" => (WilsonOriginalAlternativeFiniteSource.sectors (V:=V))
open WilsonOriginalReceivedChain WilsonOriginalAlternativeNames WilsonOriginalAlternativePurse
open WilsonOriginalAlternativeExtraction
open scoped Classical BigOperators
variable (P : Post (N:=N) R hk D Q π Γ Ψ books ahead (WilsonOriginalAlternativeFiniteSource.disks (V:=V)) (WilsonOriginalAlternativeFiniteSource.sectors (V:=V)) grades order shelf seats i floor physical)
local notation "J_" => Stock.census V
local notation "A_" => Tint.Patrol.picture P.model P.input
local notation "W_" => Ψ (i+1)
local notation "α_" => (W_).p.supportExponent
local notation "κ_" => LocalComparison.forcedDivisor R.family (i+1)



variable (upper:i+1 ≤ N) (ref:∀ j, R.family.ref (grades j) ≤ i+1)
  (o:V→Site (R.family.side (i+1) per)) (v:∀j,R.family.label (grades j)) (z:V→ℂ)
local notation "tuned_" => (fun j=>z j • v j)
local notation "top_" => WilsonOriginalAlternativeTrialSource.source R grades N per (i+1) o v z
local notation "O_" => Passport.point o

include upper ref in
/-- A finite K-born programme of the original guarded rows, with separate
engineering coefficient in each slot and freely specified original sites.
There is no cost from the old entrance aperture in the new weight. -/
theorem original (simple:G.Simple) (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (scroll:VowsR.LawScroll G φ) (chamber:VowsR.Chamber scroll R.kit D Q books)
    (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (load:seats≤Burn.horizon k+2) (narrow:shelf≤R.alloy.B.a.clock.J i)
    {τ:ℝ} (pos:0<τ) (small:τ≤1):
    let w:=WilsonOriginalAlternativeTrialWallet.radius R grades N per (i+1) o tuned_ (α_+1+1) τ
    ∃U:Post (N:=N) R hk D Q π Γ Ψ books ahead D_ K_ grades order shelf seats i floor (top_),
      Countable U.inputIndex ∧ U.w=w ∧ U.rent=τ ∧ U.cost=0 ∧ U.passport=O_ ∧ U.op=P.op ∧ U.lesson=P.lesson ∧
      ∀x a W,(U.input.hard.hard x a W)=Poly.bead J_ (((W_).activities.K a W:ℝ):ℂ):=by
  intro w
  have budget:(R.family.path.rep N per (i+1)).p=(W_).p:=
    (WilsonMeasuredCourseQuietSlots.selected R π Γ Ψ course (floor.trans (Nat.le_succ i)) upper).1
  have visible:(W_).eval=(R.family.path.rep N per (i+1)).eval:=
    (later R π Γ Ψ course (floor.trans (Nat.le_succ i)) upper).view
  let L:=WilsonOriginalAlternativeSelectedPage.paper R N per (i+1) upper J_ o grades ref tuned_
    (fun _=>1) (W_).p budget
  have wp:=WilsonOriginalAlternativeTrialWallet.positive R grades N per (i+1) o tuned_ (α_+1+1) τ pos
  have initial:=WilsonOriginalAlternativeSelectedPage.price R N per (i+1) upper J_ o grades ref tuned_
    (fun _=>1) (W_).p budget w wp (α_+1+1)
  have money:=WilsonOriginalAlternativeTrialWallet.paid R grades N per (i+1) o tuned_ (α_+1+1) τ pos
  have housing(j:V):(O_).support j⊆(R.family.localSection (grades j)).footprint (o j):=by
    apply Finset.singleton_subset_iff.mpr
    exact Finset.mem_image.mpr ⟨0,(R.makes.sections _).anchored,by simp⟩
  have honest:=WilsonOriginalAlternativeSelectedPage.lawful R N per (i+1) upper J_ o grades ref tuned_
    (fun _=>1) (W_).p budget (O_).support housing
  obtain ⟨H,count,hw,rent,cost,sites,op,lesson,keys⟩:=WilsonOriginalAlternativeQuietPost.original
    R hk D Q π Γ Ψ books ahead D_ K_ grades order shelf seats i floor physical P o L simple course
    scroll chamber hospital upper load narrow WilsonOriginalAlternativeFiniteSource.fired w wp pos small
    (L.loan_monotone initial money) honest
  have formula(x:Wallet D_)(U:Config G (R.family.side (i+1) per)):
      ((W_).eval U:ℂ) • Poly.pass (L.log x U)=top_ x U := by
    rw [WilsonOriginalAlternativeSelectedPage.printed,visible]
    apply congrArg (fun t:Poly J_=>(((R.family.path.rep N per (i+1)).eval U:ℝ):ℂ) • t)
    apply congrArg (word J_)
    funext j
    change WilsonOriginalAlternativeExtraction.entry _ (j,1) = (x j).val*WilsonOriginalAlternativeTrialSource.arm R grades N per (i+1) o v z j U
    simp only [WilsonOriginalAlternativeExtraction.entry,one_ne_zero,if_false,if_true]
    have eq:=WilsonOriginalAlternativeHosted.primary R N per (i+1) o grades tuned_
      (fun (x:Wallet D_) (a:V)=>(x a).val) (R.family.path.rep N per (i+1)) rfl x U j
    change (x j).val*WilsonOriginalStarPrimaryCatalog.primary R N per (i+1) (grades j) o j (z j • v j) U=_ at eq
    rw [eq,LinearMap.map_smul,smul_eq_mul]
    rfl
  let U:Post (N:=N) R hk D Q π Γ Ψ books ahead D_ K_ grades order shelf seats i floor (top_):=
    {H with represented:=fun x=>(H.represented x).trans (funext (formula x))}
  exact ⟨U,count,hw,rent,cost,sites,op,lesson,keys⟩

end YM.Integration.WilsonOriginalAlternativeTrialBirth
