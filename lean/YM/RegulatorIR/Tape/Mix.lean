import YM.RegulatorIR.Tape.Basic

noncomputable section
namespace YM.RegulatorIR.Tape
open Function Set Filter
open scoped NNReal ENNReal BigOperators Classical

variable {ι κ α β γ : Type*}

abbrev Rows (α β : Type*) := α → Tape β
def mix (f : Tape α) (k : Rows α β) : Tape β := fun x => ∑' i, f i * k i x

/-- Cost bound on rows in support set. -/
def Meter (S : Set α) (w : Weight α) (v : Weight β) (C : ℝ≥0∞) (k : Rows α β) : Prop :=
 ∀ x ∈ S, tally v (k x) ≤ ↑(w x) * C
abbrev Sends (S : Set α) (T : Set β) (k : Rows α β) := ∀ x ∈ S, Within T (k x)
namespace Meter
variable {S S' : Set α} {w w' : Weight α} {v v' : Weight β} {B C : ℝ≥0∞} {k l : Rows α β}
lemma weak (h : Meter S w v B k) (hB : B ≤ C) : Meter S w v C k := fun x hx => (h x hx).trans (mul_le_mul_right hB _)
lemma weigh (h : Meter S w v C k) (hw : ∀ i ∈ S, w i ≤ w' i) (hv : v' ≤ v) : Meter S w' v' C k := fun x hx => (tally_mono hv).trans ((h x hx).trans (mul_le_mul_left (ENNReal.coe_le_coe.mpr (hw x hx)) _))
lemma restrict (h : Meter S w v C k) (hs : S' ⊆ S) : Meter S' w v C k := fun x hx => h x (hs hx)
lemma add (h : Meter S w v B k) (hh : Meter S w v C l) : Meter S w v (B+C) (k+l) := fun x hx => (tally_add ..).trans ((add_le_add (h x hx) (hh x hx)).trans_eq (mul_add ..).symm)
lemma smul (h : Meter S w v C k) (z : ℝ) : Meter S w v (‖z‖ₑ*C) (z • k) := fun x hx => by
 rw [Pi.smul_apply,tally_smul,mul_left_comm]; exact mul_le_mul_right (h x hx) _
lemma costs (h : Meter S w v C k) (hC : C < ∞) {x : α} (hx : x ∈ S) : Carried (k x) v :=
  (h x hx).trans_lt (ENNReal.mul_lt_top (ENNReal.coe_lt_top) hC)
lemma sum {s : Finset ι} {k : ι → Rows α β} {C : ι → ℝ≥0∞} (h : ∀ i ∈ s, Meter S w v (C i) (k i)) :
    Meter S w v (∑ i∈s,C i) (∑ i∈s,k i) := by
  intro x hx
  rw [Finset.sum_apply, Finset.mul_sum]
  exact (tally_sum ..).trans (Finset.sum_le_sum (fun i hi => h i hi x hx))
lemma tsum {k : ι → Rows α β} {C : ι → ℝ≥0∞} (h : ∀ i, Meter S w v (C i) (k i)) :
    Meter S w v (∑' i,C i) (fun x y => ∑' i,k i x y) := fun x hx =>
  (tally_tsum ..).trans ((ENNReal.tsum_le_tsum fun i => h i x hx).trans_eq ENNReal.tsum_mul_left)
end Meter

lemma Within.mix {f : Tape α} {S : Set α} {T : Set β} {k : Rows α β} (hf : Within S f) (h : Sends S T k) : Within T (mix f k) := by
  refine Within.tsum (fun i => ?_)
  by_cases hi : f i = 0
  · simpa only [hi,zero_mul] using! (Within.zero T)
  exact (h i (hf i hi)).smul (f i)

@[simp] lemma zero_mix (k : Rows α β) : mix 0 k = 0 := by ext; simp [mix]
@[simp] lemma mix_zero (f : Tape α) : mix (β:=β) f 0 = 0 := by ext; simp [mix]
lemma run_eq {f : Tape α} {S : Set α} {k l : Rows α β} (hf : Within S f) (h : EqOn k l S) :
    mix f k = mix f l := by
  ext y; refine tsum_congr fun x => ?_
  by_cases hx : f x = 0
  · rw [hx,zero_mul,zero_mul]
  rw [h (hf x hx)]
lemma mix_at (k : Rows α β) (x : α) : mix (atOne x) k = k x := by
  funext i; unfold mix atOne; rw [tsum_eq_single x]
  simp; intro y hy; simp [hy]
lemma mix_id (f : Tape α) : mix f atOne = f := by
  ext y; unfold mix atOne; rw [tsum_eq_single y]; simp; intro b hb; simp [Ne.symm hb]
lemma mix_smul (f : Tape α) (k : Rows α β) (s : ℝ) : mix (s • f) k = s • mix f k := by
  ext y; change (∑' i, (s * f i) * k i y) = s * ∑' i, f i * k i y; simp_rw [mul_assoc,tsum_mul_left]
lemma mix_smul_rows (f : Tape α) (k : Rows α β) (s : ℝ) : mix f (s • k) = s • mix f k := by
  ext y; change (∑' i, f i * (s * k i y)) = s * ∑' i, f i * k i y; rw [← tsum_mul_left]; exact tsum_congr fun _ => mul_left_comm ..

variable {f g : Tape α} {S : Set α} {w : Weight α} {v : Weight β} {C : ℝ≥0∞} {k l : Rows α β}

lemma tally_mix (f : Tape α) (k : Rows α β) (v : Weight β) :
    tally v (mix f k) ≤ ∑' i, ‖f i‖ₑ * tally v (k i) := by
  simp_rw [← tally_smul]; exact tally_tsum _ (fun i => f i • k i)
lemma Meter.inner_cost (hf : Within S f) (h : Meter S w v C k) :
    ∑' i, ‖f i‖ₑ * tally v (k i) ≤ tally w f * C := by
  unfold tally; rw [← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum fun i => ?_
  by_cases hi : f i = 0
  · simp [hi]
  rw [mul_assoc]; exact mul_le_mul_right (h i (hf i hi)) _
lemma Meter.mix_cost (hf : Within S f) (h : Meter S w v C k) : tally v (mix f k) ≤ tally w f * C :=
  (tally_mix ..).trans (h.inner_cost hf)
lemma Meter.mix_carried (hf : Within S f) (h : Meter S w v C k) (hC : C < ∞) (hF : Carried f w) : Carried (mix f k) v :=
  (h.mix_cost hf).trans_lt (ENNReal.mul_lt_top hF hC)

/-- Exact `tsum` interchanges in the permitted domain. -/
lemma mix_summable' (hw : ∀ i, 0 < v i)
    (hs : ∑' i, ‖f i‖ₑ * tally v (k i) < ∞) (y : β) :
    Summable (fun i => f i * k i y) := by
  have hh : ∑' i, ‖f i*k i y‖ₑ*(v y) < ∞ := (ENNReal.tsum_le_tsum (g:=fun i => ‖f i‖ₑ * tally v (k i))
    (fun i => by rw [enorm_mul,mul_assoc]; exact mul_le_mul_right (point ..) _)).trans_lt hs
  rw [ENNReal.tsum_mul_right] at hh
  apply plain_summable; by_contra! H
  rw [top_le_iff] at H; unfold mass at H; rw [H,ENNReal.top_mul] at hh
  · exact lt_irrefl _ hh
  exact ENNReal.coe_ne_zero.mpr (hw y).ne'

lemma Meter.mix_summable (hw : Lower v) (hf : Within S f) (h : Meter S w v C k) (hC : C < ∞) (hF : Carried f w) (y : β) :
    Summable (fun i => f i * k i y) := by
  obtain ⟨b,hb,he⟩ := hw
  exact mix_summable' (fun i => hb.trans_le (he i)) ((h.inner_cost hf).trans_lt (ENNReal.mul_lt_top hF hC)) y

lemma add_mix (hf : Within S f) (hg : Within S g) (h : Meter S w v C k) (hC : C < ∞) (hv : Lower v)
    (hF : Carried f w) (hG : Carried g w) : mix (f+g) k = mix f k + mix g k := by
  ext y; simp_rw [mix, Pi.add_apply,add_mul]; exact (h.mix_summable hv hf hC hF y).tsum_add (h.mix_summable hv hg hC hG y)
lemma mix_add_rows {D : ℝ≥0∞} (hf : Within S f) (hk : Meter S w v C k) (hl : Meter S w v D l)
    (hC : C < ∞) (hD : D < ∞) (hv : Lower v) (hF : Carried f w) : mix f (k+l) = mix f k + mix f l := by
  ext y; simp_rw [mix, Pi.add_apply,mul_add]; exact (hk.mix_summable hv hf hC hF y).tsum_add (hl.mix_summable hv hf hD hF y)
lemma sub_mix (hf : Within S f) (hg : Within S g) (h : Meter S w v C k) (hC : C < ∞) (hv : Lower v)
    (hF : Carried f w) (hG : Carried g w) : mix (f-g) k = mix f k - mix g k := by
  ext y; simp_rw [mix, Pi.sub_apply,sub_mul]; exact (h.mix_summable hv hf hC hF y).tsum_sub (h.mix_summable hv hg hC hG y)
lemma finset_mix {F : ι → Tape α} {s : Finset ι} (hf : ∀ i∈s, Within S (F i))
    (h : Meter S w v C k) (hC : C < ∞) (hv : Lower v)
    (hF : ∀ i∈s, Carried (F i) w) : mix (∑ i∈s,F i) k = ∑ i∈s,mix (F i) k := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s hs ih =>
    rw [Finset.sum_insert hs,Finset.sum_insert hs,add_mix (hf a (by simp))
      (Within.sum (fun i (hi:i∈s) => hf i (Finset.mem_insert_of_mem hi))) h hC hv (hF a (by simp))
      (Carried.sum (fun i hi => hF i (Finset.mem_insert_of_mem hi))),
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) (fun i hi => hF i (Finset.mem_insert_of_mem hi))]

/-- Exchange with a sum of incoming tapes absolutely controlled in the row weight on `S`. -/
lemma tsum_mix {F : ι → Tape α} (hf : ∀ i, Within S (F i))
    (h : Meter S w v C k) (hC : C < ∞) (hv : Lower v)
    (hF : ∑' i, tally w (F i) < ∞) :
    mix (fun x => ∑' i,F i x) k = fun y => ∑' i, mix (F i) k y := by
  funext y; unfold mix; simp_rw [← tsum_mul_right]
  refine Summable.tsum_comm ?_; apply plain_summable
  have H : (∑' (p : ι × α), ‖F p.1 p.2*k p.2 y‖ₑ) * v y ≤ (∑' i,tally w (F i))*C := calc
    _ = ∑' i : ι, ∑' x : α, ‖F i x‖ₑ * (‖k x y‖ₑ * v y) := by
      rw [← ENNReal.tsum_mul_right, ENNReal.tsum_prod (f:=fun i x => ‖F i x*k x y‖ₑ * v y)]
      simp_rw [enorm_mul,mul_assoc]
    _ ≤ ∑' i, tally w (F i)*C := ENNReal.tsum_le_tsum fun i =>
      (ENNReal.tsum_le_tsum (g:=fun j => ‖F i j‖ₑ*tally v (k j)) fun j => mul_le_mul_right (point ..) _).trans (h.inner_cost (hf i))
    _ = _ := ENNReal.tsum_mul_right
  obtain ⟨b,hb,he⟩:=hv
  have HH := H.trans_lt (ENNReal.mul_lt_top hF hC); by_contra! ht
  rw [top_le_iff] at ht; change (∑' (p : ι × α), ‖F p.1 p.2 * k p.2 y‖ₑ)=∞ at ht
  rw [ht,ENNReal.top_mul] at HH
  · exact lt_irrefl _ HH
  exact ENNReal.coe_ne_zero.mpr (hb.trans_le (he y)).ne'

def follow (k : Rows α β) (l : Rows β γ) : Rows α γ := fun i => mix (k i) l
lemma Meter.follow {T : Set β} {u : Weight γ} {D : ℝ≥0∞} {l : Rows β γ}
    (hk : Meter S w v C k) (hl : Meter T v u D l) (h : Sends S T k) : Meter S w u (C*D) (follow k l) :=
  fun x hx => (hl.mix_cost (h x hx)).trans ((mul_le_mul_left (hk x hx) _).trans_eq (mul_assoc ..))

lemma mix_follow {T : Set β} {u : Weight γ} {D : ℝ≥0∞} {l : Rows β γ}
    (hf : Within S f) (hF : Carried f w) (hk : Meter S w v C k) (hC : C < ∞)
    (hl : Meter T v u D l) (hD : D < ∞) (hu : Lower u) (h : Sends S T k) :
    mix f (follow k l) = mix (mix f k) l := by
  let F (i : α) := f i • k i; have ht : mix f k = fun x => ∑' i, F i x := rfl
  have hq i : Within T (F i) := by
    by_cases he : f i = 0
    · unfold F; rw [he,zero_smul]; exact Within.zero _
    exact (h i (hf i he)).smul _
  have hX : ∑' i, tally v (F i) < ∞ := by
    unfold F; simp_rw [tally_smul]; exact (hk.inner_cost hf).trans_lt (ENNReal.mul_lt_top hF hC)
  rw [ht,tsum_mix hq hl hD hu hX]; funext y; simp_rw [F,mix_smul]; rfl

lemma follow_congr (k' k : Rows α β) (l : Rows β γ) {S} (hf : Within S f)
    (h : EqOn k k' S) : mix f (follow k l) = mix f (follow k' l) := run_eq hf fun _ hx => by
  unfold follow; rw [h hx]
end YM.RegulatorIR.Tape
