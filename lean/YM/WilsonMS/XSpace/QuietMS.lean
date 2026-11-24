import YM.WilsonMS.XSpace.BreezeCost
/-!
# The MS continuum reports in this comparison

Define via `MS.Dial.tour` in physical units; `$\eta=-log a+...$` payments
are not part of the definition. Basis-expansion only on genuine physical
fields. Expose both multilinear and kernel aspects since `Prediction` was
defined by tests. Include shape bounds & C1 error estimates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.VisitH
open Function Filter Set MeasureTheory Real Finset Asymptotics
open XSpace XSpace.Normalize Maxwell Maxwell.Free Maxwell.Wick TestBudget Expense Cirrus
open MS MS.Plane MS.Menus MS.Theater MS.Land MS.Tide MS.Dial MS.Local.Physical
open Fiscal BMenu Rider
open scoped BigOperators Topology Classical
variable {G : Gauge} {d n : ℕ}
local notation "PΞ" => Ensure.deck G
local notation "𝕄" => XSpace.Mesh
section reports
variable {M : Booked (Ensure.deck G)} (F : MS_Data G M) (μ : ℝ) (j : ℕ)

abbrev stamps (G : Gauge) (d n : ℕ) :=
  (Fin n → Glyph (Ensure.deck G) d)

private def woven (i : Fin n → Glyph PΞ d) :=
  (MultilinearMap.mkPiAlgebra ℂ (Fin n) ℂ).compLinearMap
    (fun j : Fin n => (Daylight PΞ d).coord (i j))

lemma fromHeight {E : Type} [AddCommMonoid E] [Module ℂ E]
    (F : MultilinearMap ℂ (fun _ : Fin n => Sec G d) E) (p : Fin n → Sec G d) :
    F p = ∑ i : Fin n → Glyph PΞ d, woven i p • F (glow ∘ i) := by
  let A := Daylight PΞ d
  have hx := F.map_sum (fun i j => A.repr (p i) j • A j)
  simp only [A.sum_repr] at hx
  rw [hx]
  refine Finset.sum_congr rfl fun i hi => Eq.trans (F.map_smul_univ _ _) ?_
  unfold A
  simp_rw [Fiscal.shines]
  rfl

def lowKernel (d : ℕ) (x : Points n) :=
  ∑ i : Fin n → Glyph PΞ d, answers i F μ j x • woven i

lemma lowK (x : Points n) (f : Fin n → Glyph PΞ d) :
    lowKernel F μ j d x (glow ∘ f) = answers f F μ j x := by
  let A := Daylight PΞ d
  have ht (i : Fin n → Glyph PΞ d) : woven i (glow ∘ f) = ∏ j, if f j = i j then (1 : ℂ) else 0 := by
    change ∏ j, A.coord (i j) (glow (f j)) = _
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← Fiscal.shines]
    simp [A, Finsupp.single_apply]
  unfold lowKernel
  simp only [_root_.sum_apply, smul_apply, smul_eq_mul, ht]
  rw [Finset.sum_eq_single_of_mem f (Finset.mem_univ _)]
  simp
  intro i _ hi
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hi
  rw [Finset.prod_eq_zero (Finset.mem_univ j) (if_neg (Ne.symm hj)), mul_zero]

lemma smooth_read (p : Fin n → Sec G d) : ContinuousOn (fun x => lowKernel F μ j d x p) (conf n) := by
  unfold lowKernel
  simp_rw [_root_.sum_apply, smul_apply, smul_eq_mul]
  exact continuousOn_finsetSum _ (fun i _ => (shape_cont i F μ j).mul continuousOn_const)

private def bookPoly (d : ℕ) (x : Test n) : MultilinearMap ℂ (fun _ : Fin n => Sec G d) ℂ := by
  refine MultilinearMap.mk' (fun v => x.applyTo (fun p => lowKernel F μ j d p v)) ?_ ?_
  · intro v i a b
    unfold Test.applyTo
    simp_rw [MultilinearMap.map_update_add, mul_add]
    rw [integral_add (x.smearing (smooth_read _ _ _ _)) (x.smearing (smooth_read _ _ _ _))]
  intro v i a b
  unfold Test.applyTo
  simp_rw [MultilinearMap.map_update_smul, smul_eq_mul, ← mul_assoc, mul_comm (x _) a, mul_assoc a,
    integral_const_mul]

def Continuum (d : ℕ) : Prediction G d := fun n =>
  { toFun t := bookPoly F μ j d t
    map_add' v w := by
      ext1 y
      change (v + w).applyTo _ = v.applyTo _ + w.applyTo _
      unfold Test.applyTo
      simp_rw [add_apply, add_mul]
      rw [integral_add (v.smearing (smooth_read F μ j y)) (w.smearing (smooth_read F μ j y))]
    map_smul' t v := by
      ext1 y
      change (t • v).applyTo _ = t * v.applyTo _
      unfold Test.applyTo
      simp_rw [smul_apply, smul_eq_mul, mul_assoc]
      rw [integral_const_mul] }

lemma continues (t : Test n) (p : Fin n → Sec G d) :
    Continuum F μ j d n t p = t.applyTo (fun x => lowKernel F μ j d x p) :=
  rfl

lemma leadingPoint {x : Points n} (hx : x ∈ conf n) (p : Fin n → Sec G d) :
    lowKernel F μ 0 d x p = scene x d p := by
  rw [fromHeight, fromHeight (scene x d)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [lowK]
  unfold answers
  exact congr_arg _ (highest_zero F μ x (profileK k) hx)

lemma free_match (d : ℕ) : Continuum F μ 0 d = reference G d := by
  ext n t p
  rw [continues, reflects]
  exact Test.apply_eq _ (fun x hx => leadingPoint F μ hx p)
end reports

structure HoldT (K : Set (Points n)) (g : 𝕄 → Test n → ℂ) (v : Test n → ℂ) : Prop where
  bill : ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : Test n), tsupport t ⊆ K → ∀ b, TestBudget.Bound t b → ‖v t‖ ≤ b * C
  pass :
    ∃ a : ℝ,
      0 < a ∧
        ∃ D : ℝ,
          0 ≤ D ∧
            ∀ᶠ i in Front,
              ∀ t : Test n,
                tsupport t ⊆ K → ∀ b, TestBudget.Bound t b → ‖g i t - v t‖ ≤ b * D * FareP a i
namespace HoldT
variable {K : Set (Points n)} {g g' : 𝕄 → Test n → ℂ} {v v' : Test n → ℂ}

theorem sumTwo (h : HoldT K g v) (ht : HoldT K g' v') :
    HoldT K (fun i t => g i t + g' i t) (fun t => v t + v' t) := by
  obtain ⟨⟨A, hA, hx⟩, a, ha, C, hC, H⟩ := h
  obtain ⟨⟨B, hB, hh⟩, d, hd, D, hD, h⟩ := ht
  refine
    ⟨⟨A + B, by positivity, fun t hs b hr => ?_⟩, min a d, lt_min ha hd, C + D, by positivity, ?_⟩
  · exact (norm_add_le ..).trans ((add_le_add (hx t hs b hr) (hh t hs b hr)).trans_eq (by ring))
  let s := min a d
  filter_upwards [h, H, fare_lower a s (min_le_left ..), fare_lower d s (min_le_right ..)] with i hh
    hm he hv t hs b hx
  have hU := TestBudget.bound_nonneg t hx
  rw [add_sub_add_comm]
  exact
    (norm_add_le ..).trans
      ((add_le_add (le_trans (hm _ hs _ hx) (mul_le_mul_of_nonneg_left he (by positivity)))
            (le_trans (hh _ hs _ hx) (mul_le_mul_of_nonneg_left hv (by positivity)))).trans_eq
        (by
          unfold s
          ring))

theorem zero : HoldT K (fun _ _ => 0) (fun _ => 0) :=
  ⟨⟨0, le_rfl, fun t hx b hh => by simp⟩, 1, zero_lt_one, 0, le_rfl,
    Eventually.of_forall (fun _ _ _ _ _ => by simp)⟩

theorem sum {E : Type*} (s : Finset E) {g : E → 𝕄 → Test n → ℂ} {v : E → Test n → ℂ}
    (h : ∀ i ∈ s, HoldT K (g i) (v i)) :
    HoldT K (fun i t => ∑ j ∈ s, g j i t) (fun t => ∑ j ∈ s, v j t) := by
  induction s using Finset.induction with
  | empty =>
    simp_rw [Finset.sum_empty]
    exact zero
  | insert i s hi ih =>
    simp_rw [Finset.sum_insert hi]
    exact (h i (by simp)).sumTwo (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem both {c : 𝕄 → ℂ} {p : ℂ} (h : Fast c p) (hx : HoldT K g v) :
    HoldT K (fun i t => c i * g i t) (fun t => p * v t) := by
  have hK := h.limit.norm.eventually (ge_mem_nhds (lt_add_one ‖p‖))
  obtain ⟨b, hb, hh⟩ := h
  obtain ⟨R, hR, H⟩ := (show _ =O[Front] _ from hh).exists_pos
  obtain ⟨⟨A, hA, hv⟩, a, ha, C, hC, hX⟩ := hx
  refine
    ⟨⟨‖p‖ * A, by positivity, fun t hs x hx => ?_⟩, min a b, lt_min ha hb, (‖p‖ + 1) * C + R * A, by
      positivity, ?_⟩
  · exact
      (norm_mul_le ..).trans
        ((mul_le_mul_of_nonneg_left (hv t hs _ hx) (norm_nonneg p)).trans_eq (by ring))
  let s := min a b
  filter_upwards [hX, H.bound, hK, fare_lower a s (min_le_left ..),
    fare_lower b s (min_le_right ..)] with i hu hi h hU ht t hq x hb
  change ‖c i‖ ≤ ‖p‖ + 1 at h
  change ‖c i - p‖ ≤ R * ‖FareP b i‖ at hi
  rw [Real.norm_of_nonneg (exp_pos _).le] at hi
  have hp := bound_nonneg t hb
  have hs := exp_pos (-s * height i)
  rw [show c i * g i t - p * v t = c i * (g i t - v t) + (c i - p) * v t from (by ring)]
  exact
    (norm_add_le ..).trans
      ((add_le_add
            ((norm_mul_le ..).trans
              (mul_le_mul h (le_trans (hu t hq _ hb) (mul_le_mul_of_nonneg_left hU (by positivity)))
                (norm_nonneg _) (by positivity)))
            ((norm_mul_le ..).trans
              (mul_le_mul (le_trans hi (mul_le_mul_of_nonneg_left ht hR.le)) (hv t hq _ hb)
                (norm_nonneg _) (mul_nonneg hR.le hs.le)))).trans_eq
        (by
          unfold s
          ring))

lemma value (h : HoldT K g v) (x : Test n) (hx : tsupport x ⊆ K) : Fast (fun i => g i x) (v x) := by
  obtain ⟨a, ha, C, hC, h⟩ := h.pass
  obtain ⟨b, hb, hb'⟩ := bound_fin x
  exact Fast.fed ha (h.mono fun i hi => hi x hx b hb')
end HoldT

def NShape (F : 𝕄 → Normalize.Prediction G d) (P : Prediction G d) :=
  ∀ (n : ℕ) (p : Fin n → Sec G d) (K : Set (Points n)),
    IsCompact K → K ⊆ conf n → HoldT K (fun i t => F i n t p) (fun t => P n t p)

lemma NShape.eval {F : 𝕄 → Prediction G d} {P} (hs : NShape F P) (p : Fin n → Sec G d) (t : Test n) :
    Fast (fun i => F i n t p) (P n t p) :=
  (hs n p (tsupport t) t.hasCompactSupport t.tsupport_subset).value t (Subset.refl _)
variable {A : Prescription (Ensure.deck G)} {V : Initialize G} {M : Booked (Ensure.deck G)}
  {F : MS_Data G M}

lemma order_rates (hG : G.Simple) (H : Installed V F A) (μ : ℝ) (d j : ℕ) :
    NShape (fun i => amended V μ A i d j) (Continuum F μ j d) := by
  intro n p K hK hc
  simp_rw [fromHeight (amended V μ A _ d j n _) p, fromHeight (Continuum F μ j d n _) p, smul_eq_mul]
  apply HoldT.sum
  intro i _
  simp_rw [continues, lowK]
  apply HoldT.both (Fast.const _)
  exact ⟨reference_bound i F μ j hK hc, layPoint i F μ j hK hc hG V A H⟩
end YM.WilsonMS.VisitH
