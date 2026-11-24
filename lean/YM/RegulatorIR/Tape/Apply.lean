import YM.RegulatorIR.Tape.Product

/-! Iterative identities on crossing two rendered tapes. Use ambient bounds when simply
justifying exchanges, separately proving stronger bounds for those entries to be estimated. -/
noncomputable section
namespace YM.RegulatorIR.Tape
open Function Set Filter
open scoped NNReal ENNReal BigOperators Classical
variable {α β γ ρ σ τ : Type*}

variable {S : Set α} {T : Set β} {U : Set ρ} {V : Set σ} {W : Set γ} {w : Weight α} {v : Weight β}
  {a : Weight ρ} {b : Weight σ} {d : Weight γ} {e : Weight τ} {A B C D : ℝ≥0∞}
  {u : Rows α ρ} {t : Rows β σ} {k : Rows (ρ × σ) γ} {l : Rows (α × β) γ} {n : Rows γ τ}
  {f : Tape α} {g : Tape β}

abbrev Pass (S : Set α) (w : Weight α) (v : Weight β) (k : Rows α β) : Prop := ∃ C : ℝ≥0∞, C < ∞ ∧ Meter S w v C k

theorem cross_mix_mix
    (hu : Meter S w a A u) (hf : Within S f) (hF : Carried f w) (hA : A < ∞) (ha : Lower a)
    (ht : Meter T v b B t) (hg : Within T g) (hG : Carried g v) (hB : B < ∞) (hb : Lower b)
    (hU : Sends S U u) (hV : Sends T V t)
    (hk : Meter (U ×ˢ V) (loom a b) d C k) (hC : C < ∞) (hd : Lower d) :
    cross k (mix f u) (mix g t) = cross (fun x => cross k (u x.1) (t x.2)) f g := by
  rw [cross,mix_grid hu ht hf hg hF hG hA hB ha hb]
  exact Eq.symm (mix_follow (hf.braid hg) (hF.braid hG) (hu.grid ht) (ENNReal.mul_lt_top hA hB) hk hC hd (Sends.grid hU hV))

theorem cross_mix_out (hL : Meter (S ×ˢ T) (loom w v) d C l) (hf : Within S f) (hg : Within T g)
    (hF : Carried f w) (hG : Carried g v) (hC : C < ∞) (hn : Meter W d e D n) (hD : D < ∞) (he : Lower e) (h : Sends (S ×ˢ T) W l) :
    mix (cross l f g) n = cross (follow l n) f g :=
  Eq.symm (mix_follow (hf.braid hg) (hF.braid hG) hL hC hn hD he h)

lemma identity_meter : Meter S w w 1 atOne := fun x _ => by simp only [tally_at,mul_one,le_refl]
lemma identity_send : Sends S S atOne := fun _ => within_at

lemma mix_sum_rows {ι : Type*} {k : ι → Rows α β} {D : ι → ℝ≥0∞} {s : Finset ι} (hf : Within S f)
    (hF : Carried f w) (hv : Lower v) (h : ∀ i∈s, Meter S w v (D i) (k i)) (hD : ∀ i∈s, D i<∞) :
    mix f (∑ i∈s,k i)=∑ i∈s,mix f (k i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, mix_add_rows hf (h i (by simp))
      (Meter.sum (fun j (hj:j∈s) => h j (Finset.mem_insert_of_mem hj))) (hD i (by simp))
      (ENNReal.sum_lt_top.mpr (fun j hj => hD j (Finset.mem_insert_of_mem hj))) hv hF,
      ih (fun j hj => h j (Finset.mem_insert_of_mem hj)) (fun j hj => hD j (Finset.mem_insert_of_mem hj))]
lemma cross_finset_left {ι : Type*} {F : ι → Tape α} {s : Finset ι} (h : Meter (S ×ˢ T) (loom w v) d A l) (hA : A < ∞) (hd : Lower d)
    (hf : ∀ i∈s, Within S (F i)) (hF : ∀ i∈s,Carried (F i) w) (hg : Within T g) (hG : Carried g v) :
    cross l (∑ i∈s,F i) g = ∑ i∈s,cross l (F i) g := by
  rw [cross,show braid (∑ i∈s,F i) g = ∑ i∈s,braid (F i) g from by
    ext; simp only [braid,Finset.sum_apply,Finset.sum_mul]]
  exact finset_mix (fun i hi => (hf i hi).braid hg) h hA hd (fun i hi => (hF i hi).braid hG)
end YM.RegulatorIR.Tape
