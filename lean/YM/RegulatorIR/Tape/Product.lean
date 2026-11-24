import YM.RegulatorIR.Tape.Mix

/-! Binary fusion of anchored polynomials uses tape products before its single-line kernel. -/
noncomputable section
namespace YM.RegulatorIR.Tape
open Function Set Filter
open scoped NNReal ENNReal BigOperators Classical

variable {α β γ σ τ : Type*}

def braid (f : Tape α) (g : Tape β) : Tape (α × β) := fun x => f x.1 * g x.2
def loom (w : Weight α) (u : Weight β) : Weight (α × β) := fun x => w x.1 * u x.2
variable {f f' : Tape α} {g g' : Tape β} {S : Set α} {T : Set β} {w : Weight α} {v : Weight β}
lemma Within.braid (hf : Within S f) (hg : Within T g) : Within (S ×ˢ T) (braid f g) :=
  fun _ hx => ⟨hf _ (left_ne_zero_of_mul hx), hg _ (right_ne_zero_of_mul hx)⟩
@[simp] lemma tally_braid (f : Tape α) (g : Tape β) (w : Weight α) (u : Weight β) :
    tally (loom w u) (braid f g) = tally w f * tally u g := tally_product ..
lemma Carried.braid (hf : Carried f w) (hg : Carried g v) : Carried (braid f g) (loom w v) := by
  unfold Carried; rw [tally_braid]; exact ENNReal.mul_lt_top hf hg

@[simp] lemma zero_braid (g : Tape β) : braid (α:=α) 0 g = 0 := by ext; simp [braid]
@[simp] lemma braid_zero (f : Tape α) : braid (β:=β) f 0 = 0 := by ext; simp [braid]
lemma add_braid (f f' : Tape α) (g : Tape β) : braid (f+f') g = braid f g + braid f' g := by
  ext; simp [braid,add_mul]
lemma braid_add (f : Tape α) (g g' : Tape β) : braid f (g+g') = braid f g + braid f g' := by
  ext; simp [braid,mul_add]
lemma braid_comm (f : Tape α) (g : Tape β) : braid g f = braid f g ∘ Prod.swap := by ext; simp [braid,mul_comm]
lemma braid_at (a : α) (b : β) : braid (atOne a) (atOne b) = atOne (a,b) := by
  funext ⟨x,y⟩; by_cases hx : x=a <;> by_cases hy : y=b <;> simp [braid,atOne,hx,hy]

def cross (k : Rows (α×β) γ) (f : Tape α) (g : Tape β) := mix (braid f g) k
variable {B : ℝ≥0∞} {u : Weight γ} {k : Rows (α × β) γ} (h : Meter (S ×ˢ T) (loom w v) u B k)
lemma tally_cross (hf : Within S f) (hg : Within T g)
    (h : Meter (S ×ˢ T) (loom w v) u B k) :
    tally u (cross k f g) ≤ tally w f * tally v g * B := by
  rw [← tally_braid]; exact h.mix_cost (hf.braid hg)
lemma Within.cross (hf : Within S f) (hg : Within T g) {U : Set γ} (h : Sends (S ×ˢ T) U k) :
    Within U (cross k f g) := (hf.braid hg).mix h

@[simp] lemma cross_zero (k : Rows (α×β) γ) (f : Tape α) : cross k f 0 = 0 := by simp [cross]
@[simp] lemma zero_cross (k : Rows (α×β) γ) (g : Tape β) : cross k 0 g = 0 := by simp [cross]
lemma cross_at (k : Rows (α × β) γ) (a : α) (b : β) :
    cross k (atOne a) (atOne b) = k (a,b) := by rw [cross,braid_at,mix_at]
theorem cross_smul_left (k : Rows (α × β) γ) (s : ℝ) (f : Tape α) (g : Tape β) : cross k (s • f) g = s • cross k f g := by
  rw [cross, show braid (s • f) g = s • braid f g from funext fun i => mul_assoc s _ _, mix_smul]; rfl
theorem cross_smul_right (k : Rows (α × β) γ) (s : ℝ) (f : Tape α) (g : Tape β) : cross k f (s • g) = s • cross k f g := by
  rw [cross, show braid f (s • g) = s • braid f g from funext fun i => mul_left_comm _ s _, mix_smul]; rfl
lemma cross_add_left (h : Meter (S ×ˢ T) (loom w v) u B k)
    (hf : Within S f) (hf' : Within S f') (hg : Within T g) (hF : Carried f w) (hF' : Carried f' w) (hG : Carried g v) (hB : B < ∞) (hu : Lower u) :
    cross k (f+f') g = cross k f g + cross k f' g := by
  rw [cross,add_braid]; exact add_mix (hf.braid hg) (hf'.braid hg) h hB hu (hF.braid hG) (hF'.braid hG)
lemma cross_add_right (h : Meter (S ×ˢ T) (loom w v) u B k)
    (hf : Within S f) (hg : Within T g) (hg' : Within T g') (hF : Carried f w) (hG : Carried g v) (hG' : Carried g' v) (hB : B < ∞) (hu : Lower u) :
    cross k f (g+g') = cross k f g + cross k f g' := by
  rw [cross,braid_add]; exact add_mix (hf.braid hg) (hf.braid hg') h hB hu (hF.braid hG) (hF.braid hG')
lemma cross_tsum_left {ι : Type*} (h : Meter (S ×ˢ T) (loom w v) u B k)
    (F : ι → Tape α) (ha : ∀ i, Within S (F i)) (hg : Within T g) (hF : ∑' i,tally w (F i) < ∞)
    (hG : Carried g v) (hB : B < ∞) (hu : Lower u) :
    cross k (fun x => ∑' i, F i x) g = fun y => ∑' i,cross k (F i) g y := by
  rw [cross,show braid (fun x => ∑' i, F i x) g = fun y => ∑' i, braid (F i) g y from by
    ext; simp_rw [braid,tsum_mul_right]]
  exact tsum_mix (fun i => (ha i).braid hg) h hB hu (by
    simp_rw [tally_braid,ENNReal.tsum_mul_right]; exact ENNReal.mul_lt_top hF hG)
lemma cross_tsum_right {ι : Type*} (h : Meter (S ×ˢ T) (loom w v) u B k)
    (G : ι → Tape β) (ha : Within S f) (hg : ∀ i, Within T (G i)) (hF : Carried f w)
    (hG : ∑' i,tally v (G i) < ∞) (hB : B < ∞) (hu : Lower u) :
    cross k f (fun x => ∑' i, G i x) = fun y => ∑' i,cross k f (G i) y := by
  rw [cross,show braid f (fun x => ∑' i, G i x) = fun y => ∑' i, braid f (G i) y from by
    ext; simp_rw [braid,tsum_mul_left]]
  exact tsum_mix (fun i => ha.braid (hg i)) h hB hu (by
    simp_rw [tally_braid,ENNReal.tsum_mul_left]; exact ENNReal.mul_lt_top hF hG)

lemma cross_mirror (k : Rows (α×β) γ) (f : Tape α) (g : Tape β) :
    cross k f g = cross (k ∘ Prod.swap) g f := by
  rw [cross,cross]; ext y
  rw [mix,mix, ← Equiv.tsum_eq (Equiv.prodComm β α) (fun p : α×β => braid f g p * k p y)]
  exact tsum_congr (fun i => by simp [braid, mul_comm])

def grid (p : Rows α σ) (q : Rows β τ) : Rows (α × β) (σ × τ) := fun z => braid (p z.1) (q z.2)
lemma Meter.grid {p : Rows α σ} {q : Rows β τ} {D : ℝ≥0∞} {t : Weight σ} {t' : Weight τ}
    (h : Meter S w t B p) (hh : Meter T v t' D q) : Meter (S ×ˢ T) (loom w v) (loom t t') (B*D) (grid p q) := by
  intro x hx
  rw [Tape.grid,tally_braid,loom,ENNReal.coe_mul]
  exact (mul_le_mul' (h x.1 hx.1) (hh x.2 hx.2)).trans_eq (mul_mul_mul_comm ..)
lemma Sends.grid {p : Rows α σ} {q : Rows β τ} {A : Set σ} {D : Set τ}
    (h : Sends S A p) (hh : Sends T D q) : Sends (S ×ˢ T) (A ×ˢ D) (grid p q) := fun _ hx => (h _ hx.1).braid (hh _ hx.2)
lemma mix_grid {p : Rows α σ} {q : Rows β τ} {D : ℝ≥0∞} {t : Weight σ} {t' : Weight τ}
    (h : Meter S w t B p) (hh : Meter T v t' D q)
    (hf : Within S f) (hg : Within T g) (hF : Carried f w) (hG : Carried g v)
    (hB : B < ∞) (hD : D < ∞) (hu : Lower t) (hv : Lower t') :
    braid (mix f p) (mix g q) = cross (grid p q) f g := by
  funext ⟨i,j⟩
  let P x := f x * p x i; let Q y := g y * q y j
  have hP : Summable P := h.mix_summable hu hf hB hF i
  have hQ : Summable Q := hh.mix_summable hv hg hD hG j
  have he : (fun x : α×β => P x.1*Q x.2) = fun z => braid f g z * grid p q z (i,j) :=
    funext fun _ => mul_mul_mul_comm ..
  have hu : Summable (fun x : α×β => P x.1*Q x.2) := he ▸ (h.grid hh).mix_summable
    (hu.product hv) (hf.braid hg) (ENNReal.mul_lt_top hB hD) (hF.braid hG) (i,j)
  change (∑' x,P x)*(∑' y,Q y) = ∑' x, braid f g x * grid p q x (i,j)
  exact (hP.hasSum.mul hQ.hasSum hu).tsum_eq.symm.trans (congr_arg tsum he)
end YM.RegulatorIR.Tape
