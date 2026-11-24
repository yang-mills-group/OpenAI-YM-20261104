import YM.Integration.WilsonFarShell
import Mathlib.LinearAlgebra.Multilinear.Curry

/-! The signed Wilson OPE remainder when both groups of insertions shrink, each in
its own measured frame. Both logarithmic lengths are measured against the same clock. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingFarShell
open Filter Function Set Spec OPE OPE.Orbits PhysMS Trace.Pilot
open scoped Topology Classical BigOperators

def length (b L : ℝ) := Real.exp (-b*L)

private theorem clock (b L : ℝ) : LogV (length b L) = b*L := by
  rw [LogV, length, Real.log_inv, Real.log_exp]
  ring

private theorem shrinks {K : Type*} {l : Filter K} {A : K → ℝ}
    (hA : Tendsto A l atTop) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun i => length b (A i)) l trail := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_,Eventually.of_forall (fun i => Real.exp_pos _)⟩
  exact Real.tendsto_exp_atBot.comp (Tendsto.const_mul_atTop_of_neg (neg_neg_of_pos hb) hA)

private theorem change_clock {K V : Type*} [Norm V] {l : Filter K} {A : K → ℝ}
    {f : K → V} {a b : ℝ} (hb : 0 < b) :
    RateLE l (LogV ∘ fun i => length b (A i)) f a ↔ RateLE l A f (b*a) := by
  constructor
  · intro h u hu
    have h' := h (u/b) ((lt_div_iff₀ hb).mpr (by simpa only [mul_comm] using hu))
    filter_upwards [h'] with i hi
    simpa only [comp_apply, clock, ← mul_assoc, div_mul_cancel₀ _ hb.ne'] using hi
  · intro h u hu
    have h' := h (b*u) (mul_lt_mul_of_pos_left hu hb)
    filter_upwards [h'] with i hi
    simpa only [comp_apply, clock, ← mul_assoc, mul_comm b u] using hi

variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (H : Leading F J) (services : Services C f S)
    {I E K : Type} [Fintype I] [Fintype E] {d : I → ℕ} {e : E → ℕ}
    {l : Filter K} [l.NeBot] {A : K → ℝ} (hA : Tendsto A l atTop)
    {x : K → I → E4} {y : K → E → E4} {o : K → E4} {b : ℝ}
    (hb : 0 < b) (hb' : b < 1)
    (hx : enveloped l A 1 x o) (hk : Kept l A 1 x)
    (hy : Intervals l A b (fun i => sole (o i)) y) (hs : Kept l A b y)
    (p : K → Viewers F) (h : ℕ)
    (v : (j : I) → (Climb.Bel C.book).Field (d j))

include H services hA hb hb' hx hk hy hs in
private theorem inner (w : Labels S e) : RateLE l A
    (fun i => formula F R (x i) (o i) (Frame.born J (length 1 (A i)) v) (y i) w h (p i))
    (-((h:ℝ)+1)*(1-b)+weight e*b) := by
  let α := -((h:ℝ)+1)*(1-b)+weight e*b
  let P (i : K) (k : I → ℕ) := Levy.invoice F R (d := k) (o i) w (p i) h (x i) (y i)
  have held := (clearance_both hA hx hk hy hs hb' (le_refl b)).2
  have report := Frame.total F R J H (shrinks hA zero_lt_one) v α P
    (fun k hkv => held.mono fun i hi z => Frame.matchInvoice F R hkv h (o i) z w (p i) hi)
    (fun k _ z => by
      have raw := (all_rate F R services z w hA hx hk zero_lt_one hy hs hb.le le_rfl hb' p h).congr
        (Eventually.of_forall fun i => Frame.phase_invoice F R h (x i) (y i) (o i) z w (p i))
      apply (change_clock zero_lt_one).mpr
      simpa only [one_mul, mul_one, α, sub_eq_add_neg, neg_mul, add_assoc] using raw)
  have paid := (change_clock zero_lt_one).mp report
  rw [one_mul] at paid
  exact paid.congr (Eventually.of_forall fun i => (Frame.phase_invoice F R h (x i) (y i) (o i)
    (Frame.born J (length 1 (A i)) v) w (p i)).symm)

private def outerForm (T : Table C.book) (x : I → E4) (u : Labels S d) (y : E → E4) :
    MultilinearMap ℂ (fun j => S.Field (e j)) ℂ :=
  (moment (S := S) (d := Sum.elim d e) T (beside x y)).currySum u

private theorem outerForm_value (T : Table C.book) (x : I → E4) (u : Labels S d)
    (y : E → E4) (w : Labels S e) : outerForm T x u y w = whole T x u y w :=
  (MultilinearMap.currySum_apply (moment (S := S) (d := Sum.elim d e) T (beside x y)) u w).trans
    (congrArg (moment (S := S) (d := Sum.elim d e) T (beside x y))
      (funext fun i => by cases i <;> rfl))

include R in
private theorem rises {g : E → ℕ} (hge : e ≤ g) (p : Viewers F) (x : I → E4)
    (u : Labels S d) (y : E → E4) (w : Labels S e) (hx : Injective (beside x y)) :
    whole (spectator F p) x u y w =
      whole (spectator F p) x u y (fun i => F.sector.derivatives.rise (hge i) (w i)) := by
  let a := Orbits.stages u w
  let a' := Orbits.stages u (fun i => F.sector.derivatives.rise (hge i) (w i))
  have le : Sum.elim d e ≤ Sum.elim d g := fun i => by cases i; exact le_rfl; apply hge
  have eq (i) : F.sector.derivatives.rise (le i) (a i) = a' i := by
    cases i with
    | inr i => rfl
    | inl i => exact F.sector.derivatives.arrival R.continuum.laws.toSymmetric R.lifts _
  exact (Levy.inclusionMoment F _ _ le a _ p hx).trans
    (congrArg (moment (spectator F p) _) (funext eq))

include H services hA hb hb' hx hk hy hs in
/-- Every exterior field also uses its own measured frame. In particular the full product
and every removed rank use exactly the same characters, union of sites, and cutoff. -/
theorem normalized (w : (j : E) → (Climb.Bel C.book).Field (e j)) :
    RateLE l A (fun i => formula F R (x i) (o i)
      (Frame.born J (length 1 (A i)) v) (y i) (Frame.born J (length b (A i)) w) h (p i))
      (-((h:ℝ)+1)*(1-b)) := by
  let c := -((h:ℝ)+1)*(1-b)
  let u i := Frame.born J (length 1 (A i)) v
  let z i := R.packet h (x i) (u i) (o i)
  let T i := spectator F (p i)
  let P (i : K) (k : E → ℕ) : MultilinearMap ℂ (fun j => S.Field (k j)) ℂ :=
    outerForm (T i) (x i) (u i) (y i) -
      outerForm (T i) (sole (o i)) (sole (z i) : Labels S (fun _ : Unit => h)) (y i)
  obtain ⟨held,full⟩ := clearance_both hA hx hk hy hs hb' (le_refl b)
  have value (k : E → ℕ) : ∀ᶠ i in l, ∀ a : Labels S k, P i k a =
      formula F R (x i) (o i) (u i) (y i) a h (p i) := by
    filter_upwards [held] with i hi a
    dsimp only [P]
    rw [sub_apply,outerForm_value,outerForm_value,formula,
      ← packet_read F R (x i) (o i) (u i) (y i) a (p i) h hi]
    rfl
  have rate := Frame.total F R J H (shrinks hA hb) w (c/b) P (fun k hke => by
    filter_upwards [held,full] with i hi hf a
    dsimp only [P]
    rw [sub_apply, sub_apply, outerForm_value,
      outerForm_value,outerForm_value,outerForm_value]
    exact congrArg₂ (·-·) (rises F R hke (p i) (x i) (u i) (y i) a hf)
      (rises F R hke (p i) (sole (o i)) (sole (z i) : Labels S (fun _ : Unit => h)) (y i) a hi))
    (fun k _ a => by
      apply (change_clock hb).mpr
      rw [show b*(weight k+c/b) = c+weight k*b by field_simp; ring]
      exact (inner F R J H services hA hb hb' hx hk hy hs p h v a).congr
        ((value k).mono fun i hi => (hi a).symm))
  have far := (change_clock hb).mp rate
  rw [show b*(c/b)=c by field_simp] at far
  exact far.congr ((value e).mono fun i hi => hi (Frame.born J (length b (A i)) w))

include H services hA hb hb' hx hk hy hs in
/-- On each power-separated moving window, with arbitrary `0 < b < 1`, the
signed numerical shell costs `(inner/outer)^(h+ζ)` for every `ζ<1`. -/
theorem separated (w : (j : E) → (Climb.Bel C.book).Field (e j)) {ζ : ℝ} (hζ : ζ < 1) :
    ∀ᶠ i in l, ‖formula F R (x i) (o i) (Frame.born J (length 1 (A i)) v)
      (y i) (Frame.born J (length b (A i)) w) h (p i)‖ ≤
        (length 1 (A i) / length b (A i))^((h : ℝ)+ζ) := by
  have bound := normalized F R J H services hA hb hb' hx hk hy hs p h v w
    (-((h:ℝ)+ζ)*(1-b)) (by nlinarith only [mul_pos (sub_pos.mpr hζ) (sub_pos.mpr hb')])
  filter_upwards [bound] with i hi
  rw [length,length,← Real.exp_sub,Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
  exact hi.trans_eq (congrArg Real.exp (by ring))


end YM.Integration.WilsonMovingFarShell
