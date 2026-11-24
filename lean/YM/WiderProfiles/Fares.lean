import YM.WiderProfiles.Assembly
import YM.WiderProfiles.Bond
/-!
# Pricing the assembly outputs

The charge at **this** (noncompact) profile. First both fares, then the
ordinaryization step. A separate lemma *identifies* (doesn't price) the
continuum fare at literal lifted positions of any one sample/Trial index.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.WiderProfiles
open Function Filter Set Finset Metric MeasureTheory Real
open MS MS.Koszul MS.Plane MS.Tone MS.High MS.Rake MS.Rake.Geo
open MS.Local.Physical MS.Land MS.Tide MS.Fleet MS.Orbit MS.Vista MS.Vane MS.Dial
open MS.Book MS.Book.Convolve MS.Puff MS.Puff.Engine MS.Puff.SplitP MS.Puff.Actors MS.Puff.Mom
open scoped Topology ContDiff BigOperators

variable {I J W : Type} [LinearOrder W] {P : Geo I} {G : Gauge}
variable {Z : Terrify W I} {X : Rake.Dance G I W} {w : W → ℕ} {l : Filter I}
variable {μ : ℝ} {V : Visa I} {L : I → Lattice.Side} {s : Finset W} {k : ℕ}
variable {c : Berth (W:=W) (I:=I)}

omit [LinearOrder W] in
lemma fare_slow (hp : NearPlan l P V L μ)
    (h : Vane.Verdict P (Vane.charge w s) 0 (X s k)) :
    Slow l P.θ (fare w P (Fleet.toZ X) s k) := by
  obtain ⟨C, hC, j, hj⟩ := h.2.2 -- title on blade
  refine ⟨C * (1+|μ|)^(2*j), by positivity, 2*j, Eventually.of_forall fun i => ?_⟩
  let d := Vane.charge w s
  change ‖Tide.higher P d i * Vane.blade (X s k) i‖ ≤ _
  rw [norm_mul, Tide.high_nn]
  have ht := P.room i
  apply le_trans (mul_le_mul_of_nonneg_left (hj i) (exp_pos ((d:ℝ)*P.θ i)).le)
  simp only [neg_zero, zero_mul, Real.exp_zero, mul_one]
  change exp ((d:ℝ)*P.θ i) * (C * (tarB P i ^ j * exp ((-(d:ℝ) - 0)*P.θ i))) ≤ _
  have h1 : 1 + |μ| + P.θ i ≤ (1 + |μ|)*(1 + P.θ i) := by nlinarith [abs_nonneg μ]
  have hx := pow_le_pow_left₀ (by positivity : 0 ≤ 1+|μ|+P.θ i) h1 (2*j)
  calc
    _ = C * tarB P i^j := by
      rw [sub_zero, neg_mul, Real.exp_neg]; field_simp
    _ ≤ C * ((1+|μ|+P.θ i)^2)^j := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (zero_le_one.trans (atmoP i)) (hp.exlog i) j) hC.le
    _ ≤ _ := by rw [← pow_mul]; rw [mul_pow] at hx
                rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hx hC.le

lemma price_peak {r : ℝ} {x : I → ℂ} (h : PeakT l P r x) : Price l P.θ r x := by
  obtain ⟨C, hC, hx⟩ := h; exact ⟨C, hC, 0, by simpa only [pow_zero, mul_one] using hx⟩

lemma fare_bond (hp : NearPlan l P V L μ) (hj : Judge P c V Z (Fleet.toZ X) L l w)
    (hver : s.Nonempty → Vane.Verdict P (Vane.charge w s) 0 (X s k)) :
    Bond l P.θ mildG (fare w P Z s k) (fare w P (Fleet.toZ X) s k) := by
  have he : Price l P.θ mildG (fare w P Z s k - fare w P (Fleet.toZ X) s k) :=
    price_peak (dealP c hj hp)
  refine Bond.of_right P.room he ?_ mild_p.le
  rcases s.eq_empty_or_nonempty with h0|hs
  · unfold fare; rw [h0, hj.blanks.2, Pi.zero_apply, mul_zero]; exact Price.zero ..
  exact fare_slow hp (hver hs)

-- Compare `Tide.Rank`, lift through the *same*, finite ordinary-moment operation.
section poly
variable {A B Y H : I → J → T ℂ}

abbrev Bonds (l : Filter I) (P : Geo I) (A B : I → J → T ℂ) : Prop :=
  ∀ a k, Bond l P.θ mildG (fun i => A i a k) (fun i => B i a k)

lemma bonds_mul (S : SplitP J) (h : Bonds l P A B) (h' : Bonds l P Y H) :
    Bonds l P (fun i => S.Lift Trunk.core (A i) (Y i))
      (fun i => S.Lift Trunk.core (B i) (H i)) := by
  intro a n; simp_rw [S.loan, Finset.sum_apply]; apply Bond.sum P.room
  intro i _; exact Bond.sum P.room _ _ (antidiagonal n) (fun k _ =>
    Bond.mul P.room (h i.1 k.1) (h' i.2 k.2))

lemma bonds_power (S : SplitP J) (h : Bonds l P A B) (n : ℕ) :
    let K := Trunk.stack S
    Bonds l P (fun i => K.power (A i) n) (fun i => K.power (B i) n) := by
  induction n with
  | zero => intro K i k; exact Bond.const ..
  | succ k ih => exact bonds_mul S h ih

lemma bonds_Cheer (S : SplitP J) (h : Bonds l P A B) (v : J) (n : ℕ) :
    Bond l P.θ mildG (fun i => Cheer Trunk S (A i) v n) (fun i => Cheer Trunk S (B i) v n) := by
  unfold Cheer cheers; simp_rw [Finset.sum_apply]; exact Bond.sum P.room _ _ _ (fun i _ =>
    Bond.mul P.room (Bond.const l _ _ (Actors.phase i)) (bonds_power S h i v n))

end poly
open PeakT (ordZ)
lemma bond_ordZ {H : Terrify W I} (h : ∀ s k, Bond l P.θ mildG (Z s k) (H s k))
    (s : Finset W) (k : ℕ) : Bond l P.θ mildG (ordZ Z s k) (ordZ H s k) :=
  bonds_Cheer (A:=fun i s k => Z s k i) (B:=fun i s k => H s k i) (marked W) h s k

section shape
variable {B : Local.Physical.Deck G} (u : W → Label B) {O : Booked B} {A : MS_Data G O}

lemma fare_book (hu : DOrd O P A u (info c) X) (i : I) (hi : P.η i = μ-P.θ i)
    (hx : Injective (fun w => lifted P c w i)) :
    fare (Label.h ∘ u) P (Fleet.toZ X) s k i =
      MS.Dial.book A u μ (fun w => lifted P c w i) s k := by
  let y (w : W) := lifted P c w i; let Y := spine A u μ y; let a (_ : Unit) := i
  let Q : Geo Unit := ⟨fun _ => P.θ i, fun _ => P.η i, fun _ => P.room i⟩
  let F := frameF Unit μ; let z (w : W) (_ : Unit) := y w
  let c' (w : W) (_ : Unit) := c w i
  have hc : DOrd O Q A u (Port.moved Q.θ z) (Dial.copy a X) := by
    change DOrd O Q A u (Port.moved Q.θ (lifted Q c')) _
    rw [← re_n]; exact valid_copy u hu a (fun _ => rfl)
  have hy : DOrd O F A u z Y := Dial.pin A u μ hx
  have hm : Rake.Mesh F z := by
    intro w v hw; have h0 : 0 < ‖y w-y v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hx.ne hw))
    refine ⟨⟨_, h0, fun j => ?_⟩, ⟨_, h0, fun j => ?_⟩⟩ <;> simp [F, z, Geo.roots]
  have h : fare (Label.h ∘ u) Q (Fleet.toZ (Dial.copy a X)) = Fleet.toZ Y :=
    clockShape Q z u (fun _ => hi) hy hc (fun s hs n => (Dial.reports u hm hy hs n).1)
  change fare (Label.h ∘ u) Q (Fleet.toZ (Dial.copy a X)) s k () = Fleet.toZ Y s k ()
  rw [h]
end shape
end YM.FVA2.WiderProfiles
