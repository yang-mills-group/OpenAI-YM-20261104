import YM.Integration.WilsonReceivedCenteredMoment

/-! Four hearings on one original post produce its normalized ordinary pair minus a counterterm. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCenteredFaces
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6
open Laurent Stationary Comparison.RG02 Comparison.RG02.Order Exterior Filter
open scoped Classical BigOperators Topology

variable {G : Gauge} (R : Run G) {m N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V : Type} [Fintype V] [DecidableEq V] {X : V → Type}
  [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats i : ℕ) (floor : m ≤ i)
  (physical : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V))

local notation "g" => Coat.gStep (R.family.path.rep N per (i+1)).beta
variable (simple : G.Simple)
  (paid : ∀ x k : ℕ, k ≤ x → ∀ b : ℝ, R.alloy.delay.betaEntry x ≤ b →
    Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) x)⁻¹ ^ 2) ≤ b)
  (q : ℕ) (deep : 2*(q+1)+8 ≤ order) (aged : q+4 ≤ 3*k+2) {ε : ℝ} (ep : 0<ε)

def Mature (i : ℕ) : Prop := ∀ (s : (Stock.census V).Mode) (v : V) (hv : v∈s.val),
  (eventually_atTop.mp (WilsonReceivedIdentityField.original R simple D φ paid grades s v hv q order shelf k seats
    deep aged ep)).choose ≤ i

theorem eventually_mature : ∀ᶠ i : ℕ in atTop, Mature R D grades order shelf seats simple paid q deep aged ep i := by
  change ∀ᶠ i : ℕ in atTop, ∀ (s : (Stock.census V).Mode) (v : V) (hv : v∈s.val), _
  apply Filter.eventually_all.mpr
  intro s
  apply Filter.eventually_all.mpr
  intro v
  by_cases live : v∈s.val
  · filter_upwards [eventually_ge_atTop ((eventually_atTop.mp
      (WilsonReceivedIdentityField.original R simple D φ paid grades s v live q order shelf k seats deep aged ep)).choose)]
      with i hi
    exact fun _ => hi
  · exact Filter.Eventually.of_forall (fun _ hv => (live hv).elim)

theorem original (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (law : VowsR.LawScroll G φ) (enrolled : VowsR.Chamber law R.kit D Q books)
    (fund : Volume.Fund D R.rolls Q φ books R.alloy.delay) (live : i<N) (fit : k≤R.alloy.B.a.clock.J i)
    (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i floor physical)
    (late : Mature R D grades order shelf seats simple paid q deep aged ep i)
    (a b c : V) (s : (Stock.census V).Mode) (distant : a≠b) (pair : s.val={a,b})
    (x : Wallet actors) (F : Forest (R.family.path.levels.clock.op i per).ratio)
    (tag : (R.family.path.levels.clock.op i per).Choices) :
    let Y := (((Ψ i).eval 1:ℂ)⁻¹) • LocalComparison.actualPush R.family N per i (physical x) 1
    let bank := Air.craft P.model (fun j => (P.model j).paint x) grades (π (i+1)) (AllOrder.Floe.Step.tape (Burn.horizon k+2))
    let program := (RunFormalChain.fromRun R).step N i per live
    let T := Order.value (g:ℂ) (Order.logMarked (Bulk.Fk program F tag bank 0 order))
    let cost := fun t => ((8*(budgetR R i)^seats)*P.rent+ε*g^q)/(Poly.toll P.w t)
    let axis := (Stock.census V).fire
    ‖(Y.part s - Y.part (axis c)) -
      (T.part s - T.part (axis c) + T.part (axis a)*T.part (axis b))‖ ≤
      cost s + cost (axis c) + cost (axis a)*‖Y.part (axis b)‖ +
        ‖T.part (axis a)‖*cost (axis b) := by
  intro Y bank program T cost axis
  letI := P.modelCount
  let vacuum := (((Ψ i).eval 1:ℂ)⁻¹)
  have normed : Y.part (Stock.census V).quiet=1 := by
    have onField := congrFun (WilsonOriginalReceivedChain.report R hk D Q π Γ Ψ books ahead actors pieces grades
      order shelf seats i floor physical P x) 1
    exact (congrArg (fun U => (vacuum • U).part (Stock.census V).quiet) onField).trans
      (WilsonReceivedCenteredMoment.gallery_quiet _ x)
  apply WilsonReceivedCenteredMoment.priced Y T normed a b c s distant pair cost
  intro t ht
  have occupied : ∃ v : V, v ∈ t.val := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact ⟨a, by rw [pair]; simp⟩
    · exact ⟨c, Finset.mem_singleton_self _⟩
    · exact ⟨a, Finset.mem_singleton_self _⟩
    · exact ⟨b, Finset.mem_singleton_self _⟩
  obtain ⟨v,hv⟩ := occupied
  have bought := (eventually_atTop.mp (WilsonReceivedIdentityField.original R simple D φ paid grades t v hv
    q order shelf k seats deep aged ep)).choose_spec i (late t v hv) hk fit Q π Γ Ψ course books law enrolled
    fund floor live P.op P.capacity P.lesson ahead actors P.model P.w P.voter P.cost P.salary x F tag
    pieces P.input P.rent P.output P.issued P.affordable
  let called := Order.logTo (Fintype.card V) (vacuum •
    LocalComparison.actualPush R.family N per i ((Tint.Patrol.picture P.model P.input).density x) 1)
  let charge := Oak.expenseReal R hk D Q π Γ books floor P.op P.lesson ahead order shelf
  change Poly.toll P.w t * ‖(called-T).part t‖ ≤ 8*charge^P.op.count*P.rent+ε*g^q at bought
  have same : called=Order.logTo (Fintype.card V) Y := congrArg (fun d => Order.logTo (Fintype.card V)
    (vacuum • LocalComparison.actualPush R.family N per i d 1)) (P.represented x)
  rw [same] at bought
  have charge₀ : 0≤charge := (by norm_num : (0:ℝ)≤4).trans P.issued.Waffle.strong
  have cp : charge^P.op.count ≤ (budgetR R i)^seats := by
    rw [P.capacity]
    exact pow_le_pow_left₀ charge₀ P.issued.Beamwork _
  apply (le_div_iff₀ (Poly.worth P.salary.positive t)).mpr
  rw [mul_comm]
  exact bought.trans (add_le_add (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left cp (by norm_num)) P.active.le) le_rfl)

end YM.Integration.WilsonReceivedCenteredFaces
