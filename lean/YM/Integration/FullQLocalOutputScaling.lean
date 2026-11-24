import YM.Integration.FullQLocalProducedOutput
import YM.Integration.LocalComparisonSignedLinearity

/-!
Fixed formal-variable scaling of one complete selected output. Selection is
performed before this construction. The scalar vacuum, path, clipping, roots,
packet layout and all completion terms are retained. The resulting output is
for the correspondingly scaled input; it is not a claim of invariance of an
arbitrarily selected model. Uniform admissibility of a normalized input is a
separate application duty.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.FullQLocal.VariableScaling
open Function Finset MeasureTheory Lattice Wilson RG Marker LocalComparison
open Comparison.Density.RenderM Comparison.RG02 RG3.Held
open RG3.Script.Picnic
open scoped Classical BigOperators

variable {G : Gauge} {V : Type} [DecidableEq V]
    {D : V → ComparisonDensity.Address.Orbit} {R : Census V}

/-- All scales are fixed before the independent test arguments. Zero scales
are allowed here; only the inverse-radius payment requires nonzero scales. -/
def tests (c : V → ℂ) (x : TestSpace D) : TestSpace D := fun v => c v • x v

private theorem letter_scale {s : Finset V} {f : TestSpace D → ℂ}
    (h : Letter ℂ (fun v => (D v).Mood) s f)
    (c : V → ℂ) (x : TestSpace D) :
    f (tests c x) = (∏ v ∈ s, c v) * f x := by
  let y (t : Finset V) : TestSpace D :=
    fun v => if v ∈ t then c v • x v else x v
  have hy (t : Finset V) : t ⊆ s →
      f (y t) = (∏ v ∈ t, c v) * f x := by
    induction t using Finset.induction_on with
    | empty =>
      intro _
      simp [y]
    | @insert i t hi ih =>
      intro hts
      have his : i ∈ s := hts (mem_insert_self i t)
      have hfun : y (insert i t) = update (y t) i (c i • x i) := by
        funext v
        by_cases hv : v = i
        · subst v
          simp [y]
        simp [y, hv, update_of_ne]
      have hbase : update (y t) i (x i) = y t := by
        have hv : y t i = x i := by simp [y, hi]
        rw [← hv]
        exact update_eq_self i (y t)
      rw [hfun, h.scale _ i his, hbase,
        ih (insert_subset_iff.mp hts).2, prod_insert hi]
      simp only [smul_eq_mul]
      ring
  calc
    f (tests c x) = f (y s) := h.stay _ _ (fun v hv => by simp [tests, y, hv])
    _ = (∏ v ∈ s, c v) * f x := hy s (Subset.refl s)

/-- Every mode inherits exactly its own original variable factors. -/
theorem published_part (F : TestSpace D → Poly R)
    (h : Published (K := ℂ) (fun v => (D v).Mood) F)
    (c : V → ℂ) (x : TestSpace D) (q : R.Mode) :
    (F (tests c x)).part q = (∏ v ∈ q.val, c v) * (F x).part q :=
  letter_scale (h q) c x

/-- The whole polynomial price transforms with the same radii, including
all higher completion modes. This identity also permits zero scales. -/
theorem published_price (F : TestSpace D → Poly R)
    (h : Published (K := ℂ) (fun v => (D v).Mood) F)
    (c : V → ℂ) (w : V → ℝ) (x : TestSpace D) :
    Poly.price w (F (tests c x)) =
      Poly.price (fun v => w v * ‖c v‖) (F x) := by
  unfold Poly.price
  apply sum_congr rfl
  intro q _
  rw [published_part F h c x q, norm_mul, norm_prod]
  unfold Poly.toll
  rw [prod_mul_distrib]
  ring

omit [DecidableEq V] in
private theorem toll_cancel (c : V → ℂ) (hc : ∀ v, c v ≠ 0)
    (w : V → ℝ) (s : Finset V) :
    (∏ v ∈ s, w v / ‖c v‖) * (∏ v ∈ s, ‖c v‖) = ∏ v ∈ s, w v := by
  rw [← prod_mul_distrib]
  apply prod_congr rfl
  intro v _
  exact div_mul_cancel₀ (w v) (norm_ne_zero_iff.mpr (hc v))

/-- Nonzero scaling preserves the original full price at reciprocal radii. -/
theorem published_price_inverse (F : TestSpace D → Poly R)
    (h : Published (K := ℂ) (fun v => (D v).Mood) F)
    (c : V → ℂ) (hc : ∀ v, c v ≠ 0) (w : V → ℝ) (x : TestSpace D) :
    Poly.price (fun v => w v / ‖c v‖) (F (tests c x)) = Poly.price w (F x) := by
  rw [published_price F h]
  congr 1
  funext v
  exact div_mul_cancel₀ (w v) (norm_ne_zero_iff.mpr (hc v))

omit [DecidableEq V] in
/-- Exact recovery of every test, including zero tests, from inverse scales. -/
theorem tests_inverse (c : V → ℂ) (hc : ∀ v, c v ≠ 0) (x : TestSpace D) :
    tests (fun v => (c v)⁻¹) (tests c x) = x := by
  funext v
  exact (smul_smul ((c v)⁻¹) (c v) (x v)).trans
    (by rw [inv_mul_cancel₀ (hc v), one_smul])

/-- Pulling a normalized input back recovers the complete original Taste. -/
theorem input_inverse {n : Side} {P : Rep G n} {o : V → Site n}
    (c : V → ℂ) (hc : ∀ v, c v ≠ 0) (I : Taste (TestSpace D) o P R) :
    LocalComparison.pullback (tests c)
      (LocalComparison.pullback (tests (fun v => (c v)⁻¹)) I) = I := by
  have he : (fun x : TestSpace D => tests (fun v => (c v)⁻¹) (tests c x)) = id :=
    funext (tests_inverse c hc)
  change LocalComparison.pullback
    (fun x : TestSpace D => tests (fun v => (c v)⁻¹) (tests c x)) I = I
  rw [he]
  rfl

/-- The original token geometry is unchanged. Its exact coefficient payment
is enlarged by the product of the scale norms in its own marked mode. -/
def token {n : Side} {rank : ℕ} (c : V → ℂ) (s : Finset V)
    (T : Token G n (fun v => (D v).Mood) rank) :
    Token G n (fun v => (D v).Mood) rank :=
  { T with gem := fun j x => T.gem j (tests c x)
           coin := T.coin * ∏ v ∈ s, ‖c v‖ }

/-- A genuine packet family, including all completion entries. -/
def packets {n : Side} (c : V → ℂ) (P : MarkedPackets D G n R) :
    MarkedPackets D G n R where
  mode := P.mode
  rank := P.rank
  power := P.power
  packet i := (P.packet i).map (token c (P.mode i).val)
  marked i T h := by
    cases hi : P.packet i with
    | none => simp [hi] at h
    | some T₀ => exact P.marked i T₀ hi
  rankCap := P.rankCap
  powerCap := P.powerCap
  rank_bounded i T h := by
    cases hi : P.packet i with
    | none => simp [hi] at h
    | some T₀ => exact P.rank_bounded i T₀ hi
  power_bounded i T h := by
    cases hi : P.packet i with
    | none => simp [hi] at h
    | some T₀ => exact P.power_bounded i T₀ hi
  nonnegative_grade i T h := by
    cases hi : P.packet i with
    | none => simp [hi] at h
    | some T₀ => exact P.nonnegative_grade i T₀ hi

private theorem packet_some {n : Side} (c : V → ℂ)
    (P : MarkedPackets D G n R) (i : ℕ) (T)
    (h : (packets c P).packet i = some T) :
    ∃ T₀, P.packet i = some T₀ ∧ T = token c (P.mode i).val T₀ := by
  cases hi : P.packet i with
  | none => simp [packets, hi] at h
  | some T₀ =>
    refine ⟨T₀, rfl, ?_⟩
    simpa only [packets, hi, Option.map_some, Option.some.injEq] using h.symm

/-- Exact value before the infinite packet sum. -/
theorem term {n : Side} (c : V → ℂ) (P : MarkedPackets D G n R)
    (x : TestSpace D) (g : ℝ) (U : Config G n) (i : ℕ) :
    (packets c P).term x g U i = P.term (tests c x) g U i := by
  cases hi : P.packet i <;> simp only [MarkedPackets.term, packets, hi, Option.map]
  rfl

/-- The entire completed packet value is pulled back, not just its jets. -/
theorem read [Fintype V] {n : Side} (c : V → ℂ) (P : MarkedPackets D G n R)
    (x : TestSpace D) (g : ℝ) (U : Config G n) :
    (packets c P).read x g U = P.read (tests c x) g U := by
  unfold MarkedPackets.read
  apply tsum_congr
  intro i
  rw [term]
  rfl

/-- The same Paid receipt transports with reciprocal variable radii.
No uniform bound on the normalized source is asserted by this theorem. -/
theorem paid {n : Side} (c : V → ℂ) (hc : ∀ v, c v ≠ 0)
    (P : MarkedPackets D G n R)
    {p : BudgetPoint} {address : V → Support n}
    {region : Comparison.Density.Testing.Region (fun v => (D v).Mood) n}
    {w : V → ℝ} {g width budget : ℝ} {coverOffset coverSlope : ℕ}
    (hP : P.Paid p address region w g width budget coverOffset coverSlope) :
    (packets c P).Paid p address region (fun v => w v / ‖c v‖)
      g width budget coverOffset coverSlope where
  width_pos := hP.width_pos
  positive v := div_pos (hP.positive v) (norm_pos_iff.mpr (hc v))
  coefficient i T h := by
    obtain ⟨T₀, hT, rfl⟩ := packet_some c P i T h
    refine ⟨mul_nonneg (hP.coefficient i T₀ hT).1 (prod_nonneg fun _ _ => norm_nonneg _), ?_⟩
    intro x
    change (∑ j, ‖T₀.gem j (tests c (testInclusion D x))‖) ≤
      T₀.coin * ∏ v ∈ (P.mode i).val, ‖c v‖
    simp_rw [letter_scale (hP.multilinear i T₀ hT _), norm_mul, norm_prod]
    rw [← mul_sum]
    exact (mul_le_mul_of_nonneg_left ((hP.coefficient i T₀ hT).2 x)
      (prod_nonneg fun _ _ => norm_nonneg _)).trans_eq (mul_comm _ _)
  paths i T h := by
    obtain ⟨T₀, hT, rfl⟩ := packet_some c P i T h
    intro x
    exact hP.paths i T₀ hT (tests c x)
  addresses i T h := by
    obtain ⟨T₀, hT, rfl⟩ := packet_some c P i T h
    exact hP.addresses i T₀ hT
  symmetry i T h := by
    obtain ⟨T₀, hT, rfl⟩ := packet_some c P i T h
    intro x U k
    exact hP.symmetry i T₀ hT (tests c x) U k
  reads i T h := by
    obtain ⟨T₀, hT, rfl⟩ := packet_some c P i T h
    intro j x y hxy
    change T₀.gem j (tests c x) = T₀.gem j (tests c y)
    rw [letter_scale (hP.multilinear i T₀ hT j),
      letter_scale (hP.multilinear i T₀ hT j), hP.reads i T₀ hT j x y hxy]
  multilinear i T h := by
    obtain ⟨T₀, hT, rfl⟩ := packet_some c P i T h
    intro j
    have he : (token c (P.mode i).val T₀).gem j =
        fun x => (∏ v ∈ (P.mode i).val, c v) * T₀.gem j x := by
      funext x
      exact letter_scale (hP.multilinear i T₀ hT j) c x
    rw [he]
    exact (hP.multilinear i T₀ hT j).cmul _
  roots v := by
    convert hP.roots v using 1
    funext i
    by_cases hv : v ∈ (P.mode i).val
    · simp only [packets, if_pos hv]
      cases hi : P.packet i with
      | none => simp
      | some T =>
        simp only [Option.map_some, token]
        change Poly.toll (fun v => w v / ‖c v‖) (P.mode i) *
            ‖(g : ℂ) ^ P.power i‖ * (T.coin * ∏ u ∈ (P.mode i).val, ‖c u‖) *
            Real.exp (width * T.fall) =
          Poly.toll w (P.mode i) * ‖(g : ℂ) ^ P.power i‖ * T.coin * Real.exp (width * T.fall)
        calc
          _ = (Poly.toll (fun v => w v / ‖c v‖) (P.mode i) *
                ∏ u ∈ (P.mode i).val, ‖c u‖) *
              ‖(g : ℂ) ^ P.power i‖ * T.coin * Real.exp (width * T.fall) := by ring
          _ = _ := by rw [show Poly.toll (fun v => w v / ‖c v‖) (P.mode i) *
              (∏ u ∈ (P.mode i).val, ‖c u‖) = Poly.toll w (P.mode i) from
                toll_cancel c hc w (P.mode i).val]
    · simp [packets, hv]
  cover i T h := by
    obtain ⟨T₀, hT, rfl⟩ := packet_some c P i T h
    exact hP.cover i T₀ hT
  width_reserved := hP.width_reserved

variable [Fintype V] {C : Family G}

/-- The finite formal prescription is transported on exactly the same
full packet value and datum, with the input colors pulled back as well. -/
def prescribed (c : V → ℂ) {Y : Bulk.Chain C.path} {datum : LocalFormal.Datum C R}
    {inputColors : TestSpace D → Bulk.Colors R G (C.side (datum.level + 1) datum.period)}
    {P : MarkedPackets D G (C.side datum.level datum.period) R} {order : ℕ}
    (h : PrescribedPackets Y datum inputColors P order) :
    PrescribedPackets Y datum (fun x => inputColors (tests c x)) (packets c P) order where
  summable x g hg U := by
    change Summable (fun i => Poly.send (P.mode i) ((packets c P).term x g U i))
    simpa only [term] using h.summable (tests c x) g hg U
  extension x := h.extension (tests c x)
  value x g hg A := by
    rw [read]
    exact h.value (tests c x) g hg A
  smooth x A := h.smooth (tests c x) A
  coefficients x A k hk := h.coefficients (tests c x) A k hk

variable {N p m : ℕ} {Q : PhysicalCarrier C N p (m + 1)}
    {o : V → Site (C.side (m + 1) p)} {o' : V → Site (C.side m p)}
    {input : Taste (TestSpace D) o Q.rep R}

/-- Construct a complete selected output for the pulled-back input.
All three complete Deck families use the original chosen carrier. -/
def output (c : V → ℂ) (O : ProducedOutput D Q o o' input) :
    ProducedOutput D Q o o' (LocalComparison.pullback (tests c) input) where
  carrier := O.carrier
  model := packets c O.model
  output := LocalComparison.pullback (tests c) O.output
  residual := LocalComparison.pullback (tests c) O.residual
  formalAligned := LocalComparison.pullback (tests c) O.formalAligned
  roots := O.roots
  vacuum := O.vacuum
  density x := O.density (tests c x)
  full x U := by
    change (O.output.leaf (tests c x)).density U =
      Poly.pass ((packets c O.model).read x
        (Pert.Asymptotics.regulatorRun C N p (m + 1)) U) *
      (O.residual.leaf (tests c x)).density U
    simpa only [read] using O.full (tests c x) U
  formal_full x U := by
    change (O.formalAligned.leaf (tests c x)).density U = O.carrier.rep.eval U •
      Poly.pass ((packets c O.model).read x
        (Pert.Asymptotics.regulatorRun C N p (m + 1)) U)
    simpa only [read] using O.formal_full (tests c x) U
  regular_log x U := O.regular_log (tests c x) U

theorem modelValue (c : V → ℂ) (O : ProducedOutput D Q o o' input)
    (x : TestSpace D) (U : Config G (C.side m p)) :
    (output c O).modelValue x U = O.modelValue (tests c x) U := by
  exact congrArg Poly.pass (read c O.model x _ U)

theorem residualError (c : V → ℂ) (O : ProducedOutput D Q o o' input)
    (x : TestSpace D) (U : Config G (C.side m p)) :
    (output c O).residualError x U = O.residualError (tests c x) U := rfl

/-- Full model times residual, with its exact original coarse denominator. -/
theorem defect (c : V → ℂ) (O : ProducedOutput D Q o o' input)
    (x : TestSpace D) (U : Config G (C.side m p)) :
    (output c O).modelValue x U * (output c O).residualError x U =
      O.modelValue (tests c x) U * O.residualError (tests c x) U := by
  rw [modelValue, residualError]

/-- Exact transport back to the original input type. The selected model and
all output rows are those just constructed by the same fixed pullback. -/
def restore (c : V → ℂ) (hc : ∀ v, c v ≠ 0)
    (O : ProducedOutput D Q o o'
      (LocalComparison.pullback (tests (fun v => (c v)⁻¹)) input)) :
    ProducedOutput D Q o o' input :=
  (input_inverse c hc input) ▸ output c O

/-- This algebraic identity uses the original trajectory denominator and
keeps the complete model multiplier. -/
theorem raw_defect (O : ProducedOutput D Q o o' input)
    (x : TestSpace D) (U : Config G (C.side m p)) :
    ((C.path.rep N p m).eval U)⁻¹ • (O.output.leaf x).density U - O.modelValue x U =
      O.modelValue x U * O.residualError x U := by
  simp only [ProducedOutput.residualError, O.full, ProducedOutput.modelValue,
    mul_sub, mul_one, mul_smul_comm]

/-- The full additive defect is multilinear by the actual input push and
already-required model receipts. No invariance of a free selected model is
postulated. Its complete summability is supplied by PrescribedPackets. -/
theorem defect_published (O : ProducedOutput D Q o o' input)
    (hInput : ∀ W, Published (K := ℂ) (fun v => (D v).Mood)
      (fun x => (input.leaf x).density W))
    (hI : ∀ x, Integrable ((input.leaf x).density)
      (prior G (C.side (m + 1) p)))
    {point : BudgetPoint} {address : V → Support (C.side m p)}
    {region : Comparison.Density.Testing.Region (fun v => (D v).Mood) (C.side m p)}
    {w : V → ℝ} {width budget : ℝ} {coverOffset coverSlope : ℕ}
    (hP : O.model.Paid point address region w
      (Pert.Asymptotics.regulatorRun C N p (m + 1)) width budget coverOffset coverSlope)
    (hSum : ∀ x U, Summable (fun i => Poly.send (O.model.mode i)
      (O.model.term x (Pert.Asymptotics.regulatorRun C N p (m + 1)) U i)))
    (U : Config G (C.side m p)) :
    Published (K := ℂ) (fun v => (D v).Mood)
      (fun x => O.modelValue x U * O.residualError x U) := by
  have hp := actualPush_published N p m (fun x => (input.leaf x).density) hInput hI U
  have ho : Published (K := ℂ) (fun v => (D v).Mood)
      (fun x => (O.output.leaf x).density U) := by
    simpa only [O.density] using hp
  have hm : Published (K := ℂ) (fun v => (D v).Mood) (fun x => O.modelValue x U) :=
    (hP.read_published U (fun x => hSum x U)).pass
  have hd : Published (K := ℂ) (fun v => (D v).Mood)
      (fun x => ((C.path.rep N p m).eval U)⁻¹ • (O.output.leaf x).density U -
        O.modelValue x U) := by
    simpa only [Published, Pi.add_apply, Pi.smul_apply, Complex.coe_smul,
      neg_one_smul, Pi.neg_apply, sub_eq_add_neg] using
      (ho.smul ((((C.path.rep N p m).eval U)⁻¹ : ℝ) : ℂ)).sum (hm.smul (-1))
  simpa only [raw_defect] using hd

/-- Every scaled error coefficient inherits its engineering factors from
this constructed output, including all higher completion terms. -/
theorem defect_part (O : ProducedOutput D Q o o' input)
    (hInput : ∀ W, Published (K := ℂ) (fun v => (D v).Mood)
      (fun x => (input.leaf x).density W))
    (hI : ∀ x, Integrable ((input.leaf x).density)
      (prior G (C.side (m + 1) p)))
    {point : BudgetPoint} {address : V → Support (C.side m p)}
    {region : Comparison.Density.Testing.Region (fun v => (D v).Mood) (C.side m p)}
    {w : V → ℝ} {width budget : ℝ} {coverOffset coverSlope : ℕ}
    (hP : O.model.Paid point address region w
      (Pert.Asymptotics.regulatorRun C N p (m + 1)) width budget coverOffset coverSlope)
    (hSum : ∀ x U, Summable (fun i => Poly.send (O.model.mode i)
      (O.model.term x (Pert.Asymptotics.regulatorRun C N p (m + 1)) U i)))
    (c : V → ℂ) (x : TestSpace D) (U : Config G (C.side m p)) (q : R.Mode) :
    ((output c O).modelValue x U * (output c O).residualError x U).part q =
      (∏ v ∈ q.val, c v) * (O.modelValue x U * O.residualError x U).part q := by
  rw [defect]
  exact published_part _ (defect_published O hInput hI hP hSum U) c x q

end YM.Integration.FullQLocal.VariableScaling
end
