import YM.GradedFar.Logged.RootRoom

/-!
# Bookkeeping on (r,s) terrace, using (logs r) allowance
Given an arbitrary lease and the BOOK shape maps, these are uniform estimates
(not tied to fixed s etc). Package physical lease prices later. Small extends only
r>0; we need t arbitrary coarser depending along lease.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Logged.Deck
open Finset Filter Function Set Spec Table Extraction OPE.Log Asymptotics Orbits MeasureTheory
open scoped Topology Classical BigOperators ContDiff
open Seats Stroke Fork
open Economy (Paint)
variable {I J L:Type} [Fintype I][Fintype J]

structure Pitch (L:Type) extends Economy.Small L where
    s: L→ℝ
    running: Tendsto s p (𝓝[>](0:ℝ))
    cost : ∀ᶠ i in p,r i≤ s i
variable (D : Pitch L)
def Pitch.outer (D:Pitch L): Economy.Small L:= ⟨D.p,D.s,D.running⟩
lemma Pitch.same : D.toSmall.r = D.r := rfl
-- defeq
variable (x:L→I→E4)(y:L→J→E4)(o:L→E4) (M δ:ℝ)
  (hm:0 ≤ M)(hd:0<δ) (hx:∀ᶠ i in D.p, Landed (D.r i) (D.s i) M δ (x i) (y i))

local notation "r"=> D.r
local notation "t"=> D.s
abbrev inlay (i:L) := Seats.homing (D.r i) (o i) (x i)
abbrev outlay (i:L) := Seats.homing (D.s i) (o i) (y i)
local notation "X"=>inlay D x o
local notation "Y"=>outlay D y o
-- clearance for both uses
include hm hd hx
lemma whole_room : ∀ᶠ i in D.p, WithinRoom (r i) M δ (X i) (o i) := hx.mono fun i h=> by
  constructor
  · intro j; unfold inlay homing; rw [add_sub_cancel_left,norm_smul,Real.norm_of_nonneg h.fresh.le,mul_comm]; exact mul_le_mul_of_nonneg_right (h.pays j) h.fresh.le
  intro j k hj; unfold inlay homing; rw [add_sub_add_left_eq_sub,← smul_sub,norm_smul,Real.norm_of_nonneg h.fresh.le,mul_comm]; exact mul_le_mul_of_nonneg_left (h.xnot j k hj) h.fresh.le
lemma middle_room : ∀ᶠ i in D.p, WithinRoom (t i) M δ (beside (sole (o i)) (Y i)) (o i) := hx.mono fun i h=> by
  let W:=t i; have he:0<W:=h.fresh.trans_le h.posed
  have hg j:δ*(t i) ≤ ‖Y i j - o i‖ := by unfold outlay homing; rw [add_sub_cancel_left,norm_smul,Real.norm_of_nonneg he.le,mul_comm]; exact mul_le_mul_of_nonneg_left (by linarith [h.apart j]) he.le
  constructor
  · intro j; rcases j with ⟨⟩|j; · change ‖o i-o i‖≤M*W; simpa using mul_nonneg hm he.le
    change ‖o i + (t i) • _ -o i‖ ≤ _; rw [add_sub_cancel_left,norm_smul,Real.norm_of_nonneg he.le,mul_comm]; exact mul_le_mul_of_nonneg_right (h.outer j) he.le
  rintro (⟨⟩|j) (⟨⟩|k) hk
  · exact (hk rfl).elim
  · change _ ≤ ‖o i-Y i k‖; rw [norm_sub_rev]; exact hg k
  · exact hg j
  change _ ≤ ‖o i + (t i) • y i j - (o i + (t i) • y i k)‖
  rw [add_sub_add_left_eq_sub,← smul_sub,norm_smul,Real.norm_of_nonneg he.le,mul_comm]; exact mul_le_mul_of_nonneg_left (h.ynot j k (fun h=> hk (congrArg Sum.inr h))) he.le

variable {G:Gauge}{C:Family G}{f:Order}{S:Table C.book}(F:Final C f S)(R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    {d:I→ℕ}{e:J→ℕ} (v:Labels S d)(w:Labels S e) (u:L→Viewers F) (P:LogTrace F R.port) (simple:G.Simple) (h:ℕ)

abbrev Rnow (D:Pitch L)(x:I→ℕ)(y:J→ℕ)(i:L):ℝ:= (D.r i)^(∑ j,x j)*(D.s i)^(∑ j,y j)
abbrev frameCost (e:J→ℕ)(q:ℝ)(h:ℕ) := q⁻¹^(h+∑ i,e i)
abbrev radius (D:Pitch L)(h:ℕ)(i:L):ℝ:=D.s i+(D.r i/D.s i)^(h+1)

local notation "R0"=> Rnow D d e
local notation "ST"=>spectator F
local notation "stamp"=>D.toSmall

omit hm hd hx in
private lemma gather (E:Type) [NormedAddCommGroup E](T : L→E) (v : L→ℝ) (d:I→ℕ)(e:J→ℕ)(hv:∀ᶠ i in D.p,0≤v i)
      {C : ℝ} (hc : 0≤C) (k:ℕ)
      (ht: ∀ᶠ i in D.p, Rnow D d e i* ‖T i‖ ≤ C*(badge (t i)*badge (r i))^k * v i) :
    Paint stamp (fun i=> v i / Rnow D d e i) T := by
    refine Economy.Paint.from_cost (max C 1) (lt_max_of_lt_right zero_lt_one) (k+k) ?_
    filter_upwards [hv,D.toSmall.ran,D.outer.ran, ht,D.toSmall.positive,D.outer.positive,D.cost] with i hv hb he ht hx hh hi
    have hx:0<r i:= hx; have hh:0<t i:= hh
    have hz : 1 ≤ badge (t i):=he; have hz' : 1 ≤ badge (r i):= hb
    have he : badge (t i) ≤ badge (r i) := by unfold badge run; linarith only [Real.log_le_log hx hi]
    have hp := mul_pos (pow_pos hx (∑ i,d i)) (pow_pos hh (∑ i,e i));
    change ‖_‖ ≤ max C 1 * (badge (r i))^(k+k) * (v i / _)
    rw [pow_add,← mul_div_assoc]; apply (le_div_iff₀ hp).mpr; rw [mul_comm]
    apply ht.trans; rw [mul_pow] -- changes outer mark in target
    have ha : 0 ≤ badge (t i):= zero_le_one.trans hz; gcongr
    all_goals first| exact he | exact le_max_left .. | positivity

include P simple
lemma old_step : Paint stamp (fun i=> radius D h i / R0 i)
    (fun i=> Orbits.discrepancy (ST (u i)) h (X i) (o i) v (Orbits.shadowOld R.port h (X i) (o i) v) (Y i) w) := by
    obtain ⟨k,b,hb,h⟩:= Fork.price_pair F P simple (names v) (names w) h hm hd
    apply gather D ℂ _ _ d e _ hb k
    · filter_upwards [hx,D.running.eventually h] with i hi ht
      rw [discrepancy_old R.port _ _ _ _ _ _ (spectate F (u i)) (spectate_respects F (u i))
        (spectate_ready F (u i)) (Fork.unique_root hi _ hd)]
      exact ht (r i) (x i) (y i) (o i) hi (u i)
    filter_upwards [D.outer.positive, D.toSmall.positive] with i (ht:0<t i) (hs:0<r i); unfold radius; positivity
lemma phase : Paint stamp (fun i=> t i/R0 i) (fun i=> Orbits.whole (ST (u i)) (X i) v (Y i) w - Orbits.whole S (X i) v (Y i) w) := by
    obtain ⟨k,h⟩:= Fork.price_phase F P simple (names v) (names w) hm hd
    apply gather D ℂ _ _ d e (D.outer.positive.mono fun i h=> h.le) (show (0:ℝ)≤2 by norm_num) k
    filter_upwards [hx,D.running.eventually h] with i hi ht; rw [whole_observed, whole_observed]
    exact ht (r i) (x i) (y i) (o i) hi (u i)

lemma upon_fixed (x': S.Field h) : Paint stamp (fun i=> frameCost e (t i) h) (fun i=> upon (ST (u i)) h (o i) (Y i) w x') := by
    let v:= stages (sole x':Labels S (fun _:Unit=>h)) w
    have ht:= (RootRoom.base_size F R D.outer hm hd (middle_room D x y o M δ hm hd hx) P v u simple)
    have hp : Paint stamp (fun i=> frameCost e (t i) h) (fun i=> upon (ST (u i)) h (o i) (Y i) w x') := by
      have hu: (∑ i,Sum.elim (fun _:Unit=>h) e i) = h+∑ i,e i := by rw [Fintype.sum_sum_type]; simp
      rw [hu] at ht; exact (ht.pull (g:=fun i=>i) tendsto_id D.cost)
    exact hp
-- variable `y` to mark sign
end YM.OPE.Logged.Deck
