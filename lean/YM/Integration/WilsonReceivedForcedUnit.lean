import YM.Integration.WilsonThermometerFullLogReturn
import YM.Integration.WilsonThermometerEarlierHearing

/-! The complete difference of the regular output on two original paid hard galleries.
The unit hard budget permits an authentic source error to be scaled before re-entry. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedForcedUnit
open FVA1 Finset Function MeasureTheory Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6
open Laurent Stationary Comparison.RG02 Comparison.RG02.Order Exterior Filter OriginalForcedAddresses
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource WilsonThermometerCourseIntake
open scoped Classical BigOperators Topology
open WilsonThermometerCourseHearing
variable {G : Gauge} (R : Run G) {m i N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V : Type} [Fintype V] [DecidableEq V] {X : V → Type}
  [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats : ℕ)


variable (floor : m ≤ i)
  (physical : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V))
  (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades
    order shelf seats i floor physical)
open Progress.DirectedRecipe QuadraticLocal.Tint
local instance : Countable P.modelIndex := P.modelCount
local notation "upper" => Ψ (i+1)
local notation "lower" => Ψ i
local notation "schedule" => Oak.Calendar (N:=N) R hk D Q π Γ Ψ floor P.lesson
local notation "hardSlot" => Hard (Wallet actors) (upper).p (upper).activities.forced
  (upper).activities.K P.passport.origin (Stock.census V)
local notation "withHard" A => ({ P.input with hard := A })
local notation "gallery" A => (Tint.Patrol.picture P.model (withHard A))
variable [Countable P.inputIndex]
private theorem sealed (K : hardSlot) (budget : K.Paid P.w (upper).p.B (upper).p.supportExponent 1) :
    Nonempty (Travel.Seal (gallery K) P.w 2 1) := by
  have pos := Push.AbsoluteSums.budget_nonneg (P.salary.suggests 0)
  have paid := P.issued.Waffle.converted pos P.affordable
  have old := Lamps.tenure _ P.w P.salary.positive P.regular (show
    (upper).p.supportExponent ≤ (upper).p.supportExponent+1+1 from by linarith)
  obtain ⟨B,_⟩ := Tint.Campus.Investor.pays P.model (withHard K) P.w P.salary.positive grades P.salary
    paid.breeze (show _ ≤ 2-P.rent from paid.fits.trans (by linarith [P.small]))
    ((mul_le_of_le_one_left (by positivity) paid.fits).trans paid.past) old budget
  exact ⟨B⟩


/-- Signed complete regular output including the actual earlier Wilson posterior and any
integrable correlated spectator. Both controlling galleries use the original certificate. -/
theorem original (live : i<N) (K₀ K₁ : hardSlot)
    (bound₀ : K₀.Paid P.w (upper).p.B (upper).p.supportExponent 1)
    (bound₁ : K₁.Paid P.w (upper).p.B (upper).p.supportExponent 1)
    (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (pass : AllOrder.Transit.Pass D Q R.alloy R.kit)
    (training : Mentor.Educated D R.rolls Q R.kit.shape R.kit.scout φ books R.alloy.delay)
    (q : ℕ) (enrolled : q ≤ P.op.stage) :
    ∃ (W : schedule) (T : Travel.Seal (WilsonReceivedCompulsoryPairing.gallery (Tint.Patrol.picture P.model P.input).E K₀ K₁) P.w 2 (1+1))
      (a : HasSlots (upper).p (upper).activities), ∀ (t : Wallet actors) (θ : ℝ), 0 ≤ θ →
      ∀ (s : (Stock.census V).Mode) (v : V), v ∈ s.val →
        let field := fun (x : Bool × Wallet actors) (F : Config G (R.family.side i per)) =>
          (WilsonReceivedCompulsoryFullLog.fullLog (k:=P.op.count) (P':=(lower))
            W.clock (WilsonReceivedCompulsoryPairing.gallery (Tint.Patrol.picture P.model P.input).E K₀ K₁) P.w T P.salary.positive a (false,t) x F).part s
        let debt := fun F => Poly.toll P.w s • ((θ:ℂ) * (field (true,t) F-field (false,t) F))
        WilsonThermometerCompulsoryReturn.Heard R (top:=N) debt (θ*(2*(Coat.gStep (upper).beta)^q)) := by
  let W := Classical.choice (Oak.agrees R hk D Q π Γ Ψ course floor live P.lesson)
  have top := QuadraticLocal.Advent.later R π Γ Ψ course (floor.trans (Nat.le_succ i)) live
  have base := QuadraticLocal.Advent.later R π Γ Ψ course floor live.le
  have band : (upper).beta ∈ Shoot.band R.alloy.B.a (i+1) := by
    rw [top.beta]
    exact (R.T.sticks N per |>.prices _ (Nat.zero_le _) live).2
  obtain ⟨staff⟩ := Mentor.crew D R.rolls Q R.alloy R.kit φ books pass training P.op
    (R.alloy.B.a.S.oneStep i per).exact_size (upper).beta band live lower base.truep.point top.truep.point rfl W.clock
  obtain ⟨T₀⟩ := sealed R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats floor physical P K₀ bound₀
  obtain ⟨T₁⟩ := sealed R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats floor physical P K₁ bound₁
  obtain ⟨T⟩ := WilsonReceivedCompulsoryPairing.sealed (Tint.Patrol.picture P.model P.input).E
    K₀ K₁ P.w P.salary.positive T₀ T₁
  have slots := QuadraticLocal.Advent.spare R π Γ Ψ course (floor.trans (Nat.le_succ i)) live
  have room : 2*(2+(1+(1:ℝ))) ≤ Mentor.capDay := by norm_num [Mentor.capDay]
  have width : 0 ≤ (lower).p.supportExponent+1+1 := by linarith [(lower).p.exponent_pos]
  refine ⟨W,T,slots,fun t θ hθ s v hv => ?_⟩
  let A := WilsonReceivedCompulsoryPairing.gallery (Tint.Patrol.picture P.model P.input).E K₀ K₁
  have priced := WilsonReceivedCompulsoryRate.through (k:=P.op.count) (P':=lower)
    W.clock staff.real A P.w T P.salary.positive slots room (false,t)
    (enrolled.trans_eq staff.paid.1.symm) P.issued.Waffle.breeze.2.1
  have measured := WilsonReceivedCompulsoryMeasurable.original W.clock A P.w T P.salary.positive
    slots (false,t) priced P.voter.room width
  have heard := WilsonReceivedCompulsoryFaces.difference W.clock A P.w T P.salary.positive slots (false,t)
    priced P.voter.room width (false,t) (true,t)
  have agree := WilsonReceivedCompulsoryFullLog.original (k:=P.op.count) W.clock staff.real (WilsonReceivedCompulsoryPairing.gallery (Tint.Patrol.picture P.model P.input).E K₀ K₁) P.w T
    P.salary.positive slots room (false,t) (false,t) (true,t)
    (WilsonReceivedCompulsoryPairing.regular (Tint.Patrol.picture P.model P.input).E K₀ K₁
      P.w P.salary.positive T slots t) P.voter.room
  have faces (F : Config G (R.family.side i per)) :
      (WilsonReceivedCompulsoryFullLog.fullLog (k:=P.op.count) (P':=(lower)) W.clock (WilsonReceivedCompulsoryPairing.gallery (Tint.Patrol.picture P.model P.input).E K₀ K₁) P.w T
        P.salary.positive slots (false,t) (true,t) F).part s -
        (WilsonReceivedCompulsoryFullLog.fullLog (k:=P.op.count) (P':=(lower)) W.clock (WilsonReceivedCompulsoryPairing.gallery (Tint.Patrol.picture P.model P.input).E K₀ K₁) P.w T
        P.salary.positive slots (false,t) (false,t) F).part s =
      (WilsonReceivedCompulsoryFaces.markedLog (k:=P.op.count) (P':=(lower)) W.clock (WilsonReceivedCompulsoryPairing.gallery (Tint.Patrol.picture P.model P.input).E K₀ K₁) P.w T
        P.salary.positive slots (false,t) (true,t) F).part s -
        (WilsonReceivedCompulsoryFaces.markedLog (k:=P.op.count) (P':=(lower)) W.clock (WilsonReceivedCompulsoryPairing.gallery (Tint.Patrol.picture P.model P.input).E K₀ K₁) P.w T
        P.salary.positive slots (false,t) (false,t) F).part s :=
    congrArg (fun b : Poly (Stock.census V) => b.part s) (agree F)
  dsimp only
  simp only [faces]
  apply WilsonThermometerEarlierHearing.original R live.le
  · exact (measurable_const (a:=Poly.toll P.w s)).smul ((measurable_const (a:=(θ:ℂ))).mul
      ((measured (true,t) s v hv).sub (measured (false,t) s v hv)))
  · intro F
    rw [norm_smul,Real.norm_of_nonneg (Poly.worth P.salary.positive s).le]
    exact heard F s v hv θ hθ


end YM.Integration.WilsonReceivedForcedUnit
end
