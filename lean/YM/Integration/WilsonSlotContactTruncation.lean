import YM.Integration.WilsonWalkTruncationMoment

/-! Ordered contacts on the entire original finite product of scalar slots.
Each untouched trailing slot reads the common sampled field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSlotContactTruncation

open RG Lattice Wilson MeasureTheory Filter
open PhysicalNext.Repeat.Legato Pert.Asymptotics
open FullQLocal.RenderedStep MatchingLedger.Compass.Income
open WilsonKernelCoupling WilsonWalkMatrixSecant WilsonWalkTruncation
open scoped Classical Topology BigOperators Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side}

theorem debit_nonneg {α : Type*} (r : α → ℝ) (hr : ∀ a, 0 ≤ r a) (l : List α) (k : ℕ) :
    0 ≤ debit r l k := by
  apply List.sum_nonneg
  intro t ht
  obtain ⟨s,_,rfl⟩ := List.mem_map.mp ht
  apply List.prod_nonneg
  intro v hv
  obtain ⟨a,_,rfl⟩ := List.mem_map.mp hv
  exact hr a

/-- Splitting an ordered list at a slot boundary gives the convolution of its
two exact elementary occurrence sums. -/
theorem debit_append {α : Type*} (r : α → ℝ) (l t : List α) (n : ℕ) :
    debit r (l++t) n = ∑ i ∈ Finset.range (n+1), debit r l i * debit r t (n-i) := by
  induction l generalizing n with
  | nil =>
    rw [List.nil_append,Finset.sum_range_succ']
    simp [debit]
  | cons e l ih =>
    cases n with
    | zero => simp
    | succ n =>
      have shift (a : List α) :
          (∑ i ∈ Finset.range (n+1+1), debit r a i * debit r t (n+1-i)) =
            (∑ i ∈ Finset.range (n+1), debit r a (i+1) * debit r t (n-i)) + debit r t (n+1) := by
        rw [Finset.sum_range_succ']
        simp
      rw [List.cons_append,debit_cons,ih,ih,shift l,shift (e::l)]
      simp only [debit_cons,add_mul,Finset.sum_add_distrib,mul_assoc,←Finset.mul_sum]
      ring

abbrev Letter (G : Gauge) := Slot × G.ColorIndex

def coord (U : Config G c) (x : Site c) (a : Letter G) : ℂ := ((a.1.atSite U x a.2 : ℝ) : ℂ)

def coeff (U Q : Config G c) (x : Site c) (a : Letter G) (n : ℕ) : ℂ :=
  Comparison.Stencils.decode a.2 (layer U Q x (Comparison.Stencils.closes a.1) n)

def word (U : Config G c) (x : Site c) (l : List (Letter G)) : ℂ := (l.map (coord U x)).prod

def contacts (x : Site c) : List (Letter G) → List (Edge (Site c))
  | [] => []
  | a::l => occurrences x (Comparison.Stencils.closes a.1) ++ contacts x l

theorem length_contacts (x : Site c) (l : List (Letter G)) :
    (contacts x l).length = (l.map (fun a => a.1.length + a.1.walk.length)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [contacts,List.length_append,length_occurrences,Comparison.Stencils.cost_path,
      List.map_cons,List.sum_cons,ih]

/-- Each positive degree used at a head slot leaves the reduced global degree
budget for every remaining slot on the same actual sample. -/
def series (U Q : Config G c) (x : Site c) : List (Letter G) → ℕ → ℂ
  | [], _ => 1
  | a::l, n => ∑ k ∈ Finset.range (n+1), coeff U Q x a k * series U Q x l (n-k)

def error (U Q : Config G c) (x : Site c) (l : List (Letter G)) (n : ℕ) : ℂ :=
  word U x l - series U Q x l n

@[simp] theorem coeff_zero (U Q : Config G c) (x : Site c) (a : Letter G) :
    coeff U Q x a 0 = coord Q x a := by
  rw [coeff,layer_zero,coord,WilsonWalkEndpointBias.atSite_reads]
  rfl

@[simp] theorem series_zero (U Q : Config G c) (x : Site c) (l : List (Letter G)) :
    series U Q x l 0 = word Q x l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change (∑ k ∈ Finset.range 1, coeff U Q x a k * series U Q x l (0-k)) =
      coord Q x a * word Q x l
    rw [Finset.sum_range_one,coeff_zero]
    exact congrArg (fun z => coord Q x a * z) ih

/-- The retained first-order polynomial has one marked contribution at a
slot and samples all its other zero-degree factors at the true prediction. -/
theorem series_one_cons (U Q : Config G c) (x : Site c) (a : Letter G) (l : List (Letter G)) :
    series U Q x (a::l) 1 = coord Q x a * series U Q x l 1 +
      coeff U Q x a 1 * word Q x l := by
  change (∑ k ∈ Finset.range 2, coeff U Q x a k * series U Q x l (1-k)) = _
  rw [Finset.sum_range_succ,Finset.sum_range_one,coeff_zero]
  exact congrArg (fun z => coord Q x a * series U Q x l 1 + coeff U Q x a 1 * z)
    (series_zero U Q x l)

theorem word_bound (U : Config G c) (x : Site c) (l : List (Letter G)) : ‖word U x l‖ ≤ 1 := by
  induction l with
  | nil => simp [word]
  | cons a l ih =>
    change ‖coord U x a * word U x l‖ ≤ 1
    rw [norm_mul]
    have h : ‖coord U x a‖ ≤ 1 := by
      simpa only [coord,Complex.norm_real,Real.norm_eq_abs] using
        WilsonWalkTruncationMoment.slot_unit U x a.1 a.2
    exact (mul_le_mul h ih (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

private theorem scale_le_one (G : Gauge) : 1/G.colorScale ≤ 1 := by
  apply (div_le_one G.colorScale_pos).2
  have h : (1:ℝ) ≤ G.repDim := by exact_mod_cast G.dimPos
  exact Real.one_le_sqrt.mpr h

theorem coeff_bound (g Q : Config G c) (x : Site c) (a : Letter G) (k : ℕ) :
    ‖coeff (g*Q) Q x a k‖ ≤ debit (fun e => ‖G.mat (g e)-1‖)
      (occurrences x (Comparison.Stencils.closes a.1)) k := by
  cases k with
  | zero =>
    rw [coeff_zero,debit_zero]
    simpa only [coord,Complex.norm_real,Real.norm_eq_abs] using
      WilsonWalkTruncationMoment.slot_unit Q x a.1 a.2
  | succ k =>
    exact (WilsonWalkTruncationMoment.slot_layer g Q x a.1 a.2 k).trans
      ((mul_le_mul_of_nonneg_right (scale_le_one G) (debit_nonneg _ (fun _ => norm_nonneg _) _ _)).trans_eq
        (one_mul _))

/-- The first omitted contribution at the current slot multiplies every
subsequent original slot in its fully sampled form. -/
theorem stopping (U Q : Config G c) (x : Site c) (a : Letter G) (l : List (Letter G)) (n : ℕ) :
    error U Q x (a::l) n =
      WilsonWalkTruncationMoment.slotError U Q x a.1 a.2 n * word U x l +
      ∑ k ∈ Finset.range (n+1), coeff U Q x a k * error U Q x l (n-k) := by
  have h : WilsonWalkTruncationMoment.slotError U Q x a.1 a.2 n =
      coord U x a - ∑ k ∈ Finset.range (n+1), coeff U Q x a k := by
    rw [WilsonWalkTruncationMoment.slotError,jet_eq_sum,map_sum]
    rfl
  rw [h]
  change coord U x a * word U x l -
      (∑ k ∈ Finset.range (n+1), coeff U Q x a k * series U Q x l (n-k)) = _
  simp only [error,mul_sub,sub_mul,Finset.sum_mul,Finset.sum_sub_distrib]
  abel

/-- Stopping at the first omitted contact across all slots costs the one
concatenated list of genuine sampled link displacements. -/
theorem pointwise (g Q : Config G c) (x : Site c) (l : List (Letter G)) (n : ℕ) :
    ‖error (g*Q) Q x l n‖ ≤ debit (fun e => ‖G.mat (g e)-1‖) (contacts x l) (n+1) := by
  let r (e : Edge (Site c)) := ‖G.mat (g e)-1‖
  have hr (e : Edge (Site c)) : 0 ≤ r e := norm_nonneg _
  induction l generalizing n with
  | nil => simp [error,word,series,contacts,debit]
  | cons a l ih =>
    let h := occurrences x (Comparison.Stencils.closes a.1)
    let t := contacts x l
    have ha : ‖WilsonWalkTruncationMoment.slotError (g*Q) Q x a.1 a.2 n‖ ≤ debit r h (n+1) :=
      (WilsonWalkTruncationMoment.slot_pointwise g Q x a.1 a.2 n).trans
        ((mul_le_mul_of_nonneg_right (scale_le_one G) (debit_nonneg r hr h _)).trans_eq (one_mul _))
    rw [stopping]
    change _ ≤ debit r (h++t) (n+1)
    calc
      _ ≤ debit r h (n+1) + ∑ k ∈ Finset.range (n+1), debit r h k * debit r t (n-k+1) := by
        refine (norm_add_le ..).trans (add_le_add ?_ ?_)
        · rw [norm_mul]
          exact (mul_le_mul ha (word_bound (g*Q) x l) (norm_nonneg _) (debit_nonneg r hr h _)).trans_eq
            (mul_one _)
        · refine (norm_sum_le ..).trans (Finset.sum_le_sum ?_)
          intro k _
          rw [norm_mul]
          exact mul_le_mul (coeff_bound g Q x a k) (ih (n-k)) (norm_nonneg _) (debit_nonneg r hr h k)
      _ = _ := by
        symm
        rw [debit_append,Finset.sum_range_succ]
        simp only [Nat.sub_self,debit_zero,mul_one]
        conv_lhs => rw [add_comm]
        apply congrArg (fun z => debit r h (n+1)+z)
        apply Finset.sum_congr rfl
        intro k hk
        have hk' := Finset.mem_range.mp hk
        rw [show n+1-k=n-k+1 by omega]

theorem exact_of_length_le (g Q : Config G c) (x : Site c) (l : List (Letter G)) (n : ℕ)
    (h : (contacts x l).length ≤ n) : series (g*Q) Q x l n = word (g*Q) x l := by
  have H := pointwise g Q x l n
  rw [debit,List.sublistsLen_of_length_lt (by omega : (contacts x l).length < n+1),
    List.map_nil,List.sum_nil,norm_le_zero_iff,error,sub_eq_zero] at H
  exact H.symm

variable (S : StepData c f)

/-- Any original signed outgoing test may multiply the entire scalar product
remainder on its common field. -/
theorem conditional (b : ℝ) (Q : Config G c) (x : Site c) (l : List (Letter G)) (n : ℕ)
    (ζ : Config G c → ℂ) (B : ℝ) (hB : 0 ≤ B) (hζ : ∀ V, ‖ζ V‖ ≤ B) (M : ℝ) (hM : 0 ≤ M)
    (hm : ∀ e, (∫ V, S.noise b Q V * WilsonLinkDisplacement.amplitude G (n+1)
      (V e*(Q e)⁻¹) ∂prior G c) ≤ M) :
    ‖∫ V, S.noise b Q V • (ζ V * error V Q x l n) ∂prior G c‖ ≤
      B*((contacts x l).length:ℝ)^(n+1)*M := by
  apply WilsonWalkTruncationMoment.consume_debit S b Q (contacts x l) n
    (fun V => ζ V * error V Q x l n) B hB _ M hM hm
  intro V
  rw [norm_mul]
  have H : ‖error V Q x l n‖ ≤ debit (WilsonWalkTruncationMoment.distance Q V)
      (contacts x l) (n+1) := by
    change ‖error V Q x l n‖ ≤ debit (fun e => ‖G.mat (V e*(Q e)⁻¹)-1‖) (contacts x l) (n+1)
    simpa only [inv_mul_cancel_right,Pi.mul_apply,Pi.inv_apply] using pointwise (V*Q⁻¹) Q x l n
  exact mul_le_mul (hζ V) H (norm_nonneg _) hB

/-- The genuine tag mixture of the stopped full slot product retains the
entire measured sample in every factor and in its signed outgoing weight. -/
def tagged (b : ℝ) (U : Config G f) (x : Site c) (l : List (Letter G)) (n : ℕ)
    (ζ : S.Choices → Config G c → ℂ) : ℂ :=
  ∑ z, S.likelihood U z •
    ∫ V, S.noise b (S.prediction U z) V • (ζ z V * error V (S.prediction U z) x l n) ∂prior G c

theorem mixture (b : ℝ) (h : S.patch.Branches S.kernel G) (U : Config G f)
    (x : Site c) (l : List (Letter G)) (n : ℕ) (ζ : S.Choices → Config G c → ℂ)
    (B : ℝ) (hB : 0 ≤ B) (hζ : ∀ z V, ‖ζ z V‖ ≤ B) (M : ℝ) (hM : 0 ≤ M)
    (hm : ∀ z e, let Q := S.prediction U z
      (∫ V, S.noise b Q V * WilsonLinkDisplacement.amplitude G (n+1)
        (V e*(Q e)⁻¹) ∂prior G c) ≤ M) :
    ‖tagged S b U x l n ζ‖ ≤ B*((contacts x l).length:ℝ)^(n+1)*M := by
  unfold tagged
  refine (norm_sum_le ..).trans ?_
  calc
    _ ≤ ∑ z, S.likelihood U z * (B*((contacts x l).length:ℝ)^(n+1)*M) := by
      apply Finset.sum_le_sum
      intro z _
      rw [norm_smul,Real.norm_of_nonneg (S.likelihood_pos U z)]
      exact mul_le_mul_of_nonneg_left (conditional S b _ x l n _ B hB (hζ z) M hM (hm z))
        (S.likelihood_pos U z)
    _ = _ := by rw [←Finset.sum_mul,S.chosen h U,one_mul]

theorem selected (R : Run G) (hG : G.Simple) :
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧ ∀ᶠ m : ℕ in atTop, ∀ N p : ℕ, m < N →
      ∀ (n : ℕ) (x : Site (R.family.side m p)) (l : List (Letter G)) (U : Config G (R.family.side (m+1) p)),
      let S := R.family.path.levels.clock.op m p
      let b := R.family.path.β N p (m+1)
      ∀ (ζ : S.Choices → Config G (R.family.side m p) → ℂ) (B : ℝ), 0 ≤ B →
        (∀ z V, ‖ζ z V‖ ≤ B) →
      ‖tagged S b U x l n ζ‖ ≤
        B*((contacts x l).length:ℝ)^(n+1)*C (n+1)*(regulatorRun R.family N p (m+1))^(n+1) := by
  obtain ⟨C,hC,H⟩ := WilsonLinkDisplacement.calendar R.family.path.levels.clock
  refine ⟨C,hC,?_⟩
  filter_upwards [WilsonPhysicalKernelClock.transport R hG H] with m hm N p hN n x l U
  dsimp only
  intro ζ B hB hζ
  let t := regulatorRun R.family N p (m+1)
  have ht : 0 ≤ t := (Weather.runs_pos R.family R.makes (Nat.succ_le_of_lt hN) p).le
  have htime := hm N p hN (n+1) m p
  rw [WilsonPhysicalKernelClock.temperature R N p (m+1) (Nat.succ_le_of_lt hN)] at htime
  have hmeasure := mixture (R.family.path.levels.clock.op m p) (R.family.path.β N p (m+1))
    (R.family.path.levels.blocks m p).branches U x l n ζ B hB hζ (C (n+1)*t^(n+1))
    (mul_nonneg (hC _) (pow_nonneg ht _)) (fun z e => htime e _)
  exact hmeasure.trans_eq (by dsimp only [t]; ring)

end YM.Integration.WilsonSlotContactTruncation
end
