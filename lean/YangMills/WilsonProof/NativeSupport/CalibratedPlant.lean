import YM.RGGapR2.Rough

/-! Start the purchased marked corridor with an unmasked bounded physical
packet at each anchor. Flagged packets enter the original forced family. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.InletSusceptibility
open Function Finset MeasureTheory Lattice RG Wilson Marker
open MergeProof MergeProof.Accent Extra.Multi Extra.Trajectories Push.GridApprox.Nil
open RGGapR2
open scoped Classical BigOperators

variable {V : Type} [Fintype V] [DecidableEq V] {G : Gauge} {n : Side}

private def packetPart (good : Bool) (t : ℝ) (X : Support n)
    (F : Config G n → ℂ) : Config G n → ℂ :=
  if good then masked t X F else F - masked t X F

private lemma part_eq (good : Bool) {t : ℝ} {X : Support n}
    {F : Config G n → ℂ} {U : Config G n} :
    packetPart good t X F U =
      if (Healthy t X U ↔ good = true) then F U else 0 := by
  classical
  cases good <;> by_cases h : Healthy t X U <;> simp [packetPart, h]

private lemma packet_borne (B : Census V) (good : Bool) {o : V → Site n}
    {i : V} {X : Support n} {t : ℝ} {F : Config G n → ℂ}
    (hx : o i ∈ X) (loc : LocalOn X F) (symm : GaugeInvariant F) (meas : Measurable F) :
    Borne o X (fun U => Poly.send (B.fire i) (packetPart good t X F U)) t := by
  classical
  refine ⟨fun U U' ha hf => congrArg (Poly.send _) ?_,
    fun a U => congrArg (Poly.send _) ?_, fun j => ?_, fun U => ?_⟩
  · have h : Healthy t X U ↔ Healthy t X U' := by
      simp only [Healthy, disjoint_iff_inter_eq_empty, hf]
    rw [part_eq, part_eq, h, loc U U' ha]
  · rw [part_eq, part_eq, show Healthy t X (gauge a U) ↔ Healthy t X U by
      simp only [Healthy, gauge_flags], symm a U]
  · simp only [Poly.part_send]
    by_cases hj : j = B.fire i
    · simp only [if_pos hj]
      cases good
      · exact meas.sub (masked_measurable t X F meas)
      · exact masked_measurable t X F meas
    · simpa only [if_neg hj] using (measurable_const (a := (0 : ℂ)))
  · apply scope_send
    intro j hj
    exact (Finset.mem_singleton.mp hj).symm ▸ hx

private lemma packet_towed (B : Census V) {X : V → Support n} {o : V → Site n}
    {w : V → ℝ} {M r : ℕ} {e t u : ℝ} {F : V → Config G n → ℂ}
    (good : Bool) (home : ∀ i, o i ∈ X i) (occ : Occupancy o r)
    (hw : ∀ i, 0 < w i) (hu : 0 ≤ u) (unit : ∀ i U, ‖F i U‖ ≤ 1)
    (bill : ∀ i, Real.exp ((e+1)*coverNumber M (X i))*w i ≤ u) :
    Towed w X (fun i U => Poly.send (B.fire i) (packetPart good t (X i) (F i) U))
      M e (r*siteFactor M*u) := by
  classical
  have hr : Rooted (fun i : V => {i}) X M (e+1) w u := by
    intro i
    apply Budget.certify
    · intro j
      split
      · exact mul_nonneg (Real.exp_pos _).le (hw j).le
      · rfl
    · intro A
      simp only [Finset.mem_singleton, eq_comm (a := i), sum_ite_eq']
      split
      · exact bill i
      · exact hu
  refine ⟨w, Summable.of_finite,
    root_hit occ (fun i => (hw i).le) hu (fun i _ => ⟨i, mem_singleton_self _, home i⟩) hr,
    fun i => ?_⟩
  simpa only [Poly.solo_toll, mul_one] using
    satin (w := w) (packetPart good t (X i) (F i)) (B.fire i) 1 zero_le_one
      (fun U => by rw [part_eq]; split; exact unit i U; simp)

/-- The numerical premises are the ones in `Moonlit.endow`. The packet
radius can be taken to be `u * exp (-(a+1) * largestCover)`. -/
theorem plant (R : Rep G n) (B : Census V) (F : V → Config G n → ℂ)
    (X : V → Support n) (o : V → Site n) (w : V → ℝ) {r : ℕ} {b c u : ℝ}
    (vac : R.activities.Valid R.p b c) (home : ∀ i, o i ∈ X i)
    (loc : ∀ i, LocalOn (X i) (F i)) (symm : ∀ i, GaugeInvariant (F i))
    (meas : ∀ i, Measurable (F i)) (unit : ∀ i U, ‖F i U‖ ≤ 1)
    (occ : Occupancy o r) (hw : ∀ i, 0 < w i) (hu : 0 ≤ u)
    (bill : ∀ i, Real.exp ((R.p.supportExponent+1)*coverNumber R.p.B (X i))*w i ≤ u)
    (exp_ok : 0 ≤ R.p.supportExponent-3)
    (reserve : ((R.p.B+R.p.B+1 : ℕ) : ℝ)^4 * (c+r*siteFactor R.p.B*u) ≤ 3)
    (small : Real.exp (c+r*siteFactor R.p.B*u)-1 ≤ 1) :
    Rough.Freight R B (birth B R F) o w (R.p.supportExponent-3) 1 := by
  classical
  let P (good : Bool) (i : V) (U : Config G n) :=
    Poly.send (B.fire i) (packetPart good R.p.threshold (X i) (F i) U)
  let K := exclaim R.activities B
  let C := Accent.closure K (P false) X R.p.threshold
  let H := tally X (P true)
  have bore good i : Borne o (X i) (P good i) R.p.threshold :=
    packet_borne B good (home i) (loc i) (symm i) (meas i)
  have silent good i U : (P good i U).part B.quiet = 0 := by
    simp only [P, Poly.part_send, if_neg (B.fire_hot i).symm]
  have hot i U : P false i U ≠ 0 → ¬ Healthy R.p.threshold (X i) U := by
    intro h hh
    exact h (by simp [P, packetPart, hh])
  have burn i : Burns o (X i) (P true i) R.p.threshold := by
    refine ⟨bore true i, fun U h => ?_, silent true i⟩
    by_contra hn
    exact h (by simp [P, packetPart, hn])
  have Hburn x : Burns o x (H x) R.p.threshold :=
    transitE X (r := id) burn (fun _ => Summable.of_finite) x
  have raw good : Towed w X (P good) R.p.B R.p.supportExponent (r*siteFactor R.p.B*u) :=
    packet_towed B good home occ hw hu unit bill
  have kflow x : Flow o x (K x) R.p.threshold := granular R.activities R.p B vac x
  have cflow x : Flow o x (C x) R.p.threshold :=
    threshed K (P false) X R.p.threshold kflow (bore false) x
  have priceK := vacant R.activities R.p B vac w hw
  have ht : R.p.supportExponent-3+3 = R.p.supportExponent := by ring
  have hc : Towed w Prod.fst C R.p.B (R.p.supportExponent-3)
      (Real.exp (c+r*siteFactor R.p.B*u)-1) :=
    branch K (P false) X _ w (ht.symm ▸ priceK) (ht.symm ▸ raw false) hw exp_ok reserve
  have sumK : exclaim R.activities B + (fun x U => Rough.purge B (C x U)) = C := by
    funext x U
    ext j
    change (Poly.send B.quiet _).part j + (if j = B.quiet then 0 else _) = _
    rw [Poly.part_send]
    split_ifs with hj
    · subst j
      rw [add_zero]
      symm
      exact (wine K (P false) X _ U x (fun p => (kflow p).permits U) (fun i => silent false i U)).trans
        ((Poly.part_send B.quiet B.quiet _).trans (if_pos rfl))
    · exact zero_add _
  have deposit : 0 ≤ c := (tsum_nonneg (priceK.choose_spec.2.1 0).1).trans
    (priceK.choose_spec.2.1 0).2.2
  have funded : (r:ℝ)*siteFactor R.p.B*u ≤ 1 := by
    have hh := Real.add_one_le_exp (c+r*siteFactor R.p.B*u)
    linarith
  refine ⟨H, fun x U => Rough.purge B (C x U),
    ⟨Hburn, fun x => ⟨Rough.Flow.purge (cflow x), fun U => by
      change (if B.quiet = B.quiet then (0 : ℂ) else (C x U).part B.quiet) = 0
      exact if_pos rfl⟩⟩,
    (towing X (P true) (r := id) (raw true) hw).shrink (by linarith) funded hw,
    (Rough.Towed.purge (R := R) hc).shrink le_rfl small hw, ?_⟩
  rw [sumK, starting B R F vac]
  funext U
  have sumH : (∑ x, H x U) = ∑ i, P true i U := by
    simpa only [H, tally, tsum_fintype] using
      (border (p := fun i => P true i U) X Summable.of_finite).tsum_eq
  have pieces : (Mach B fun i => F i U) = (∑ i, P true i U) + ∑ i, P false i U := by
    rw [Mach, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    ext j
    change (Poly.send _ _).part j = (Poly.send _ _).part j + (Poly.send _ _).part j
    simp only [Poly.part_send]
    split <;> simp [packetPart]
  have q0 good : (∑ i, P good i U).part B.quiet = 0 := by simp [Poly.part_sum, silent]
  have joined := allclosed K (P false) X R.p.threshold U (fun x hx => ((kflow x).permits U hx).2) (fun i => hot i U)
  have fact := pass_sum (R := B) univ (fun i : V => B.fire i) (fun i _ => singleton_nonempty _)
    (fun i => packetPart false R.p.threshold (X i) (F i) U)
  change field (fun j => C j U) _ = field (fun j => K j U) _ * ∏ i, (1 + P false i U) at joined
  change Poly.pass (∑ i, P false i U) = ∏ i, (1 + P false i U) at fact
  change (Real.exp (R.exponent U) : ℂ) •
      (Poly.pass (Mach B (fun i => F i U)) * field (fun j => K j U) _) =
    _ • (Poly.pass (∑ i, H i U) * field (fun j => C j U) _)
  rw [pieces, sumH, pass_add (q0 true) (q0 false), joined, ←fact]
  congr 1
  ring

end YM.Integration.InletSusceptibility
