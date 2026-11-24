import YangMills.WilsonProof.NativeSupport.CalibratedPlant

/-! The actual calibrated graded push of the unmasked planting. Distinct
terminal anchors give occupancy at all earlier integrations. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.InletSusceptibility
open Function Finset MeasureTheory Lattice RG Wilson Marker
open MergeProof MergeProof.Accent Extra.Multi Extra.Trajectories Push.GridApprox.Nil
open RGGapR2
open scoped Classical BigOperators

def corridorRadius (δ : ℕ → ℝ) (k N : ℕ) (a : ℝ) : ℝ :=
  (∏ j ∈ Ico k N, δ j) * a

private lemma radius_step (δ : ℕ → ℝ) {k N : ℕ} (hk : k < N) (a : ℝ) :
    corridorRadius δ k N a = δ k * corridorRadius δ (k+1) N a := by
  unfold corridorRadius
  rw [prod_eq_prod_Ico_succ_bot hk δ]
  ring

variable {V : Type} [Fintype V] [DecidableEq V] {G : Gauge}

theorem calibrated_corridor (A : History G) (r : ℕ → ℕ) (δ u : ℕ → ℝ)
    (D : ∀ N p j : ℕ, j < N → GaugeDoor (A.rep N p (j+1)) (A.rep N p j))
    (selected : A.Selected) (marked : Moonlit A r δ u D) (back : ∀ j, 1 ≤ r j)
    (N p k : ℕ) (hk : k < N) (B : Census V)
    (F : V → Config G (A.S.side N p) → ℂ) (X : V → Support (A.S.side N p))
    (o : (j : ℕ) → V → Site (A.S.side j p)) (distinct : Injective (o k))
    (parent : ∀ j, k ≤ j → j < N → (A.levels.clock.op j p).ratio.parent ∘ o (j+1) = o j)
    (home : ∀ i, o N i ∈ X i) (loc : ∀ i, LocalOn (X i) (F i))
    (symm : ∀ i, GaugeInvariant (F i)) (meas : ∀ i, Measurable (F i))
    (unit : ∀ i U, ‖F i U‖ ≤ 1) (w : V → ℝ) (hw : ∀ i, 0 < w i)
    (bill : ∀ i, Real.exp (((A.levels.budget N).supportExponent+1)*
        coverNumber (A.levels.budget N).B (X i))*w i ≤ u N) :
    Rough.Freight (A.rep N p k) B
      (gust A N p N (birth B (A.rep N p N) F) k hk.le)
      (o k) (fun i => corridorRadius δ k N (w i)) (A.levels.budget k).supportExponent 1 := by
  classical
  have inj (j : ℕ) (hj : k ≤ j) (jh : j ≤ N) : Injective (o j) := by
    induction hj with
    | refl => exact distinct
    | @step j hj ih =>
      intro x y h
      apply ih (Nat.le_trans j.le_succ jh)
      rw [← parent j hj jh]
      exact congrArg (A.levels.clock.op j p).ratio.parent h
  have occ (j : ℕ) (hj : k ≤ j) (jh : j ≤ N) : Occupancy (o j) (r j) :=
    fun y => (Occupancy.of_injective (inj j hj jh) y).trans (back j)
  have rad (j : ℕ) (jh : j ≤ N) (i : V) : 0 < corridorRadius δ j N (w i) :=
    mul_pos (Finset.prod_pos fun l hl => by
      obtain ⟨_, _, _, q⟩ := marked.days N p l (mem_Ico.mp hl).2
      exact q.hats.1) (hw i)
  let price (j : ℕ) := (A.levels.budget j).supportExponent - if j = N then 3 else 0
  let seed := birth B (A.rep N p N) F
  have run (j : ℕ) (hj : k ≤ j) (hn : j ≤ N) :
      Rough.Freight (A.rep N p j) B (gust A N p N seed j hn)
        (o j) (fun i => corridorRadius δ j N (w i)) (price j) 1 := by
    induction hn using Nat.decreasingInduction with
    | self =>
      obtain ⟨hu, he, hs, hv⟩ := marked.endow N
      have top := selected.represents N p N le_rfl
      have start := plant (A.rep N p N) B F X (o N) w top.good.labels home loc symm meas unit
        (occ N hj le_rfl) hw hu (top.vac.symm ▸ bill) (top.vac.symm ▸ he)
        (top.vac.symm ▸ hs) (top.vac.symm ▸ hv)
      simpa only [gust_base, seed, corridorRadius, Ico_self, prod_empty, one_mul, price,
        if_pos rfl, if_true, top.vac] using start
    | of_succ j hn ih =>
      let p1 := A.levels.budget (j+1)
      have enough : p1.supportExponent-4 ≤ price (j+1) := by
        dsimp only [p1, price]
        split <;> linarith
      obtain ⟨_, _, H, Q⟩ := marked.days N p j hn
      have step := Rough.reducedStep A r N j p selected hn Q H (rad (j+1) hn) (rad j hn.le)
        (ih (hj.trans j.le_succ)) enough ((parent j hj hn).symm ▸ occ j hj hn.le)
        (fun i => (radius_step δ hn (w i)).le)
      rw [gust_step A N p N seed hn]
      simpa only [price, if_neg hn.ne, sub_zero, parent j hj hn] using step
  simpa only [price, if_neg hk.ne, sub_zero] using run k le_rfl hk.le

end YM.Integration.InletSusceptibility
