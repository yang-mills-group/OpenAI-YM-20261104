import YM.WilsonMS.XSpace.GramReady
/-!
# Leading component before position-stamping

Triangular rather than assume the veil of all bare change coefficients
is harmless. We prove power-rate closeness of the *constant term only*,
on the real-H physical frame. Higher coefficients needn't stay bounded!
Quantifiers: any fixed field horizon accepted. So the branch-selection of a
normalized, position-dual solve with a fixed number of columns is unchanged
at sufficiently fine resolution; no branch assumption with moving horizon.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Reservoir
open Function Set Filter MeasureTheory Real Finset
open XSpace XSpace.Normalize XSpace.Expense XSpace.Cirrus
open Maxwell Maxwell.Free Maxwell.Wick
open MS MS.Plane MS.Landau MS.Landau.Detect MS.Land MS.Menus MS.Theater
open Fiscal BMenu VisitH
open scoped BigOperators Topology Classical
variable {G : Gauge} {d n j k : ℕ}
local notation "BΨ" => Ensure.deck G
local notation "𝕄" => XSpace.Mesh
variable (A : Prescription (Ensure.deck G)) (μ : ℝ)

abbrev knot (d : ℕ) (p : XSpace.Mesh) : FieldEnd G d :=
  debt A (μ - height p) (height p) d 0

lemma lowerHead (p : 𝕄) (i : Glyph BΨ d) : knot A μ d p (glow i) - glow i ∈ lowerLand G d i.grade := by
  obtain ⟨a, s⟩ := i
  let j : Plaid BΨ a.val := s
  let L (q : Glyph BΨ a.val) : Glyph BΨ d :=
    ⟨⟨q.1.val,
        Nat.lt_succ_of_le (Nat.le_trans (Nat.le_of_lt_succ q.1.isLt) (Nat.le_of_lt_succ a.isLt))⟩,
      q.2⟩
  let Y := Land.read j
  let U (i : Glyph BΨ a.val) := dues A (μ - height p) (height p) j 0 i
  rw [knot, specials, horizon_c]
  change (∑ i, U i • glow (L i)) - glow (L Y) ∈ _
  have hx : U Y = 1 := by
    unfold U
    rw [sign0 _ _ _ _ _ (le_refl _), if_pos rfl]
  rw [← Finset.add_sum_erase _ (fun i => U i • glow (L i)) (mem_univ Y), hx, one_smul,
    add_sub_cancel_left]
  refine Submodule.sum_mem _ fun i hi => ?_
  by_cases ht : i.grade < Y.grade
  · exact Submodule.smul_mem _ _ (low_letter _ ht)
  unfold U
  rw [sign0 _ _ _ j i (le_of_not_gt ht), if_neg (show i ≠ Y from Finset.mem_erase.mp hi |>.1),
    zero_smul]
  exact Submodule.zero_mem _

lemma at_lead (V) (d : ℕ) (p : 𝕄) : amended V μ A p d 0 = recruit (knot A μ d p) (batch V p d 0) := by
  unfold amended
  rw [Normalize.rest, Book.Program.pay0, Fiscal.bets, PowerSeries.coeff_mk]

variable {A} {F : FieldEnd G d}

/-- Coordinate fast convergence; field end entries will be arbitrary Sec,
so use *no* normed ring chosen on these algebraic spaces. -/
abbrev Follows (φ : 𝕄 → Sec G d) (v : Sec G d) :=
  Fast (fun i => (Daylight BΨ d).equivFun (φ i)) ((Daylight BΨ d).equivFun v)

abbrev Fell (φ : 𝕄 → FieldEnd G d) (F : FieldEnd G d) :=
  ∀ p, Follows (fun i => φ i p) (F p)

section trace
variable {v u : 𝕄 → Sec G d} {p x : Sec G d}

lemma Follows.run (h : Follows v p) (c : Glyph BΨ d) :
    Fast (fun i => (Daylight BΨ d).coord c (v i)) ((Daylight BΨ d).coord c p) := by
  let L : (Glyph BΨ d → ℂ) →L[ℝ] ℂ := ContinuousLinearMap.proj c
  exact h.map L

lemma tracks
    (h :
      ∀ c : Glyph BΨ d, Fast (fun i => (Daylight BΨ d).coord c (v i)) ((Daylight BΨ d).coord c p)) :
    Follows v p :=
  fast_pi h

lemma crow (h : Follows v p) (hv : Follows u x) : Follows (v + u) (p + x) :=
  tracks fun c => by
    simp only [map_add, Pi.add_apply]
    exact (Follows.run h c).add (Follows.run hv c)

lemma chances {c : 𝕄 → ℂ} {a : ℂ} (h : Fast c a) (hv : Follows v p) :
    Follows (fun i => c i • v i) (a • p) :=
  tracks fun j => by
    simp_rw [map_smul, smul_eq_mul]
    exact h.mul (Follows.run hv j)

lemma finals {U : Type} (J : Finset U) {φ : U → 𝕄 → Sec G d} {p : U → Sec G d}
    (h : ∀ i ∈ J, Follows (φ i) (p i)) : Follows (fun k => ∑ i ∈ J, φ i k) (∑ i ∈ J, p i) :=
  tracks fun c => by
    simp_rw [map_sum]
    exact Fast.p_sum J fun i hi => Follows.run (h i hi) _

lemma warm {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (h : Follows v p)
    (L : Sec G d →ₗ[ℝ] E) : Fast (fun i => L (v i)) (L p) := by
  let A := (Daylight BΨ d).equivFun
  let T := LinearMap.toContinuousLinearMap (L.comp (A.symm.toLinearMap.restrictScalars ℝ))
  have he (v : Sec G d) : L v = T (A v) := by
    change L v = L (A.symm (A v))
    rw [LinearEquiv.symm_apply_apply]
  simp_rw [he]
  exact h.map T

lemma curfew (v : Sec G d) : Follows (fun _ => v) v :=
  Fast.const _

lemma lineUp (hp : Follows v p) (V : Initialize G) (f : Test 2) (q : Sec G d) :
    Fast (fun i => reading (v i) f (batch V i d 0) q) (reading p f (reference G d) q) := by
  let A := Daylight BΨ d
  have he (P : Prediction G d) (v : Sec G d) :
    reading v f P q = ∑ i : Glyph BΨ d, A.coord i v * reading (glow i) f P q := by
    let U := (P 2 f).toLinearMap ![v, q] 0
    have he (x : Sec G d) : reading x f P q = U x := by
      rw [reads]
      unfold U
      rw [MultilinearMap.toLinearMap_apply]
      congr 1
      ext1 i
      fin_cases i <;> simp
    simp_rw [he]
    nth_rw 1 [← A.sum_repr v]
    rw [map_sum]
    exact
      Finset.sum_congr rfl fun i _ =>
        (map_smul U _ _).trans (congr_arg (A.repr v i • U ·) (Fiscal.shines i))
  rw [he]
  conv_lhs => intro i; rw [he]
  refine Fast.p_sum _ fun i hi => Fast.mul (Follows.run hp i) ?_
  simp_rw [reads]
  exact Fast.one (cost_window V frontier f ![glow i, q])
end trace
variable {V : Initialize G} {M : Booked (Ensure.deck G)} {F : MS_Data G M}

lemma free_lead (hc : G.Simple) (h : Installed V F A) (d : ℕ) :
    Fell (knot A μ d) (1 : FieldEnd G d) := by
  let Z := knot A μ d
  have ht (p : Glyph BΨ d) : Follows (fun i => Z i (glow p)) (glow p) := by
    induction hx : p.grade using Nat.strong_induction_on generalizing p with
    | h j hi =>
      let v : Sec G d := glow p
      have hx' (t : 𝕄) : Z t v - v ∈ lowerLand G d j := hx ▸ lowerHead A μ t p
      let w (t : 𝕄) : RowKey G d j → ℂ := (hx' t).choose
      have hv (i : 𝕄) : enroll G d j (w i) = Z i v - v := (hx' i).choose_spec
      obtain ⟨S, hQ⟩ := test_full G d j
      let P i := atlas S (Z i) (batch V i d 0)
      let K := atlas S 1 (reference G d)
      have he (t : Sec G d) (s : S) :
        let a := glow s.val.1.val;
        let L := s.val.2
        Fast (fun i => reading (Z i a) L (batch V i d 0) t) (reading a L (reference G d) t) := by
        intro a L
        exact lineUp (hi s.val.1.val.grade s.val.1.property _ rfl) _ _ _
      have hh : Fast w 0 := by
        apply decoderA (K := P) (M := K) (fun p n => he _ _) hQ
        intro i
        let a := glow i.val.1.val
        let L := i.val.2
        change Fast (fun x => reading (Z x a) L _ (enroll G d j (w x))) _
        have hB := he v i
        have hp (t) : reading (Z t a) L (batch V t d 0) (Z t v) = amended V μ A t d 0 2 L ![a, v] := by
          rw [at_lead, reads, recruits]
          congr 1
          ext1 i
          fin_cases i <;> rfl
        simp_rw [hv, map_sub, hp]
        have h0 := ((order_rates hc h μ d 0).eval ![a, v] L)
        rw [free_match] at h0
        replace hB :
          Fast (fun t => reading (Z t a) L (batch V t d 0) v) (reading a L (reference G d) v) := hB
        rw [reads a v] at hB
        obtain hh := h0.sub hB
        rw [sub_self] at hh
        exact hh
      have hu : Follows (fun i => enroll G d j (w i)) 0 := by
        let T :=
          LinearMap.toContinuousLinearMap ((Daylight BΨ d).equivFun.toLinearMap ∘ₗ enroll G d j)
        unfold Follows
        rw [map_zero]
        have hh := hh.map (T.restrictScalars ℝ)
        rw [map_zero] at hh
        exact hh
      have he := crow hu (curfew v)
      rw [zero_add] at he
      convert he using 1
      funext i
      rw [Pi.add_apply, hv, sub_add_cancel]
  intro p
  let A := Daylight BΨ d
  change Follows (fun i => Z i p) p
  rw [← A.sum_repr p]
  conv_lhs => intro i; rw [map_sum]
  unfold A
  simp_rw [map_smul, Fiscal.shines]
  exact finals _ fun i hi => chances (Fast.const _) (ht i)
end YM.WilsonMS.Reservoir
