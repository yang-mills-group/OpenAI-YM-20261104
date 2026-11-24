import YM.Integration.WilsonReceivedPaidCourse

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReceivedIdentityField
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open Laurent Stationary Exterior Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open scoped Classical BigOperators Topology

private theorem flag_free (G : Gauge) (n : Side) (P : RG.Rep G n) :
    flags P.p.threshold (1 : Config G n) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a flagged
  obtain ⟨p,_,hot⟩ := (flags_spec _ _ _).mp flagged
  have cold : G.chord (faceValue (1 : Config G n) p) ≤ P.p.threshold := by
    simp [faceValue,Lattice.square,P.p.threshold_pos.le]
  exact (not_lt_of_ge cold) hot

private theorem sample_zero (G : Gauge) (n : Side) (g : ℝ) :
    Integral.sample g (0 : fieldDir G n 1) = 1 := by
  unfold Integral.sample
  rw [smul_zero]
  funext e
  change G.lieExp 0 * 1 = 1
  rw [G.mat_lieExp_zero,one_mul]

theorem original {G : Gauge} (R : Run G) (simple : G.Simple)
    (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (φ : ℕ → ℕ)
    (paid : ∀ x k : ℕ, k ≤ x → ∀ b : ℝ, R.alloy.delay.betaEntry x ≤ b →
      Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) x)⁻¹ ^ 2) ≤ b)
    {V : Type} [Fintype V] [DecidableEq V] {marks : Census V} (grades : V → ℕ)
    (s : marks.Mode) (v : V) (hv : v ∈ s.val) (q order shelf k slots : ℕ) (deep : 2*(q+1)+8 ≤ order)
    (aged : q+4 ≤ 3*k+2) {ε : ℝ} (pos : 0 < ε) :
    ∀ᶠ i : ℕ in atTop,
    ∀ {m N per : ℕ} (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
      (_fit : k ≤ R.alloy.B.a.clock.J i) (Q : D.Tab R.rolls)
      (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
      (_course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
      (books : Mentor.Offices.Books D R.rolls Q φ) (law : VowsR.LawScroll G φ)
      (_enrolled : VowsR.Chamber law R.kit D Q books) (_fund : Volume.Fund D R.rolls Q φ books R.alloy.delay)
      (hi : m ≤ i) (cut : i < N)
      (op : Mentor.Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i))
      (_capCount : op.count=slots) (lesson : Lesson (N:=N) R hk D Q π Γ hi)
      (ahead : Mentor.Forecast D R.rolls Q φ books)
      {ι : Type} {X : V → Type} [∀ u, AddCommGroup (X u)] [∀ u, Module ℝ (X u)]
      {passport : Earn.Passport (R.family.side (i+1) per) V}
      (actors : ∀ u, Set (X u)) (M : ι → Row passport marks G (Affinity.Wallet actors))
      (w : V → ℝ)
      (voter : Mentor.Cruise.Voter M (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1)))
        order op.count op.stage k (R.alloy.B.a.clock.J i)) (cost : ℝ)
      (_incoming : Scene.Armada M w grades (Poetry.Agenda.seed D φ (Burn.horizon k)
        (R.alloy.B.a.clock.J (i+1))) cost order op.count shelf)
      (x : Affinity.Wallet actors) (F : Forest (R.family.path.levels.clock.op i per).ratio)
      (tag : (R.family.path.levels.clock.op i per).Choices) 
      {old next : Type} (pieces : ∀ u, Submodule ℝ (X u))
      (Z : Tint.Incoming passport (Ψ (i+1)) (Affinity.Wallet actors) old marks)
      (rent : ℝ) (Y : Tint.Incoming (passport.coarser (R.family.path.levels.clock.op i per).ratio)
        (Ψ i) (Affinity.Wallet actors) next marks)
      (_returned : Oak.Buffered.SuccessStory R hk D Q π Γ Ψ books hi op lesson ahead
        actors pieces M Z w grades order shelf voter rent cost Y)
      (_entrance : cost ≤ (Oak.expenseReal R hk D Q π Γ books hi op lesson ahead order shelf)⁻¹),
      let g := Coat.gStep (R.family.path.rep N per (i+1)).beta
      let Ω := Oak.expenseReal R hk D Q π Γ books hi op lesson ahead order shelf
      let read := Order.logTo (Fintype.card V) ((((Ψ i).eval 1:ℂ)⁻¹) •
           LocalComparison.actualPush R.family N per i ((Tint.Patrol.picture M Z).density x) 1)
      let issued := Air.craft M (fun a => (M a).paint x) grades (π (i+1)) (AllOrder.Floe.Step.tape (Burn.horizon k+2))
      let step := (RunFormalChain.fromRun R).step N i per cut
      let point := Order.value (g:ℂ) (Order.logMarked (Bulk.Fk step F tag issued 0 order))
      Poly.toll w s*‖(read-point).part s‖ ≤ (8*Ω^op.count)*rent+ε*g^q := by
  filter_upwards [WilsonReceivedPaidCourse.original R simple D φ paid grades s v hv q 0 order shelf k slots
    deep aged 0 0 (by norm_num) pos] with i purchase
  intro m N per hk fit Q π Γ Ψ course books law enrolled fund hi cut op capCount lesson ahead ι X _ _ passport
    actors M w voter cost incoming x F tag old next pieces Z rent Y returned entrance g Ω read issued step point
  have sample := sample_zero G (R.family.side i per) g
  have flat := flag_free G (R.family.side i per) (Ψ i)
  have bought := purchase hk fit Q π Γ Ψ course books law enrolled fund hi cut op capCount lesson ahead actors M w voter
    cost incoming x F tag 0 pieces Z rent Y returned entrance 0 (by simp) (by simp [Exterior.collect])
  let angle := Stationary.arm G (R.family.side i per) 1 (0 : Stationary.Link G (R.family.side i per))
  have angleZero : angle = 0 := map_zero _
  have fieldZero : Integral.sample g angle = 1 := (congrArg (Integral.sample g) angleZero).trans sample
  have clean : flags (Ψ i).p.threshold (Integral.sample g angle) = ∅ :=
    Eq.mpr (congrArg (fun U => flags (Ψ i).p.threshold U = ∅) fieldZero) flat
  let compare := fun (T : fieldDir G (R.family.side i per) 1) (U : Config G (R.family.side i per)) =>
    Poly.toll w s * ‖(Order.logTo (Fintype.card V) ((((Ψ i).eval U:ℂ)⁻¹) •
        LocalComparison.actualPush R.family N per i ((Tint.Patrol.picture M Z).density x) U) -
      Order.value (g:ℂ) (Order.logMarked (Bulk.Fk step F tag issued T order))).part s‖ ≤
      8*Ω^op.count*rent+ε*g^q
  change compare 0 1
  exact Eq.mp (congrArg₂ compare angleZero fieldZero) (bought clean)

end YM.Integration.WilsonReceivedIdentityField
