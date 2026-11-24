import YM.Contacts.Pulse.Pluck
import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Newtown
/-! Discrete PROJECTION infrastructure for multi-leg hybrid width consumption.
Closely following `Newt` (single field) of SIGNED_SOURCE_CONTINUATION,
generalizing to arbitrary slots & perimeter budget spaces. Need total-degree
subtraction of PRODUCT test coefficients. PDE uses parity/w published soft jets. -/
namespace YM.Pulse.Spine
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior
open Finset Bloch Laurent Push.AbsoluteSums Extra.Iteration
open scoped Classical Topology BigOperators NNReal ENNReal
noncomputable section
variable {α β X Y Z E : Type} [NormedAddCommGroup E][NormedSpace ℝ E]{M R:ℝ}
namespace Quill
def jump (i:α)(f:Shift α→E)(z:Shift α):= f (z+arc i)-f z
lemma commute (i j:α)(f:Shift α→E): jump i (jump j f) = jump j (jump i f) := by funext v; simp only [jump]; rw [add_right_comm v]; abel
variable [Fintype α]
def piece : ℕ→ (Shift α→E) → Shift α→ E
| 0,p,_=> p 0
| k+1,p,x=> ((k:ℝ)+1)⁻¹ • ∑ i:α,(x i:ℝ) • piece k (jump i p) (x-arc i)
lemma difference (p:Shift α→E)(k:ℕ)(i:α) : jump i (piece (k+1) p)=piece k (jump i p):= by
  induction k generalizing p i with
  | zero => funext x; simp [jump,piece,arc,Pi.single_apply,add_smul, Finset.sum_add_distrib,ite_smul,apply_ite ((↑):ℤ→ℝ),eq_comm]
  | succ k ih=>
    funext x; set C:ℝ:= k+1; set B:=C+1
    have hC : 0<C:= by unfold C; positivity
    have hB : 0<B := by unfold B; positivity
    let u (i:α):=arc i (α:=α); let v:= jump i p; let r (x:Shift α):=piece (k+1) v x; let s j:=piece (k+1) (jump j p); let g (j:α):=(x j:ℝ)
    have hh j : s j (x+u i-u j)-s j (x-u j)= piece k (jump j v) (x-u j):= by rw [show x+u i-u j=x-u j+arc i from by unfold u; abel]; change jump i _ _=_; rw [show jump i _ _=piece k (jump i (jump j p)) _ from congr_fun (ih (jump j p) i) _,commute]
    have he : jump i (piece ((k+1)+1) p) x=B⁻¹ • ((∑ j,g j • (s j (x+u i-u j)-s j (x-u j))) + r x):= by
      change (((k+1:ℕ):ℝ)+1)⁻¹ • (∑ j,((x+u i) j:ℝ) • s j (x+u i-u j)) - (((k+1:ℕ):ℝ)+1)⁻¹ • ∑ j,(g j) • s j (x-u j)=_
      rw [Nat.cast_add_one,← smul_sub]; congr 1
      simp only [Pi.add_apply, Int.cast_add,add_smul, Finset.sum_add_distrib, smul_sub,Finset.sum_sub_distrib]
      rw [add_sub_right_comm]; congr 1
      unfold u; simp [arc,Pi.single_apply,apply_ite ((↑):ℤ→ℝ),ite_smul]; rfl
    have ht : r x = C⁻¹ • ∑ j,g j • piece k (jump j v) (x-u j):= rfl
    rw [he]; simp_rw [hh]; change B⁻¹ • (_+r x)=r x
    rw [ht]; simp only [smul_add, smul_smul,← add_smul]; congr 1; field_simp; ring

def zen (k:ℕ)(p:Shift α→ E) (x:Shift α):= ∑ i∈Finset.range k,piece i p x
def tail (k:ℕ)(p:Shift α→E) := p - zen k p
lemma turn (k:ℕ)(p:Shift α→E)(i:α): jump i (zen (k+1) p)=zen k (jump i p):= by
  ext1 x
  change zen (k+1) p (x+arc i)-zen (k+1) p x=zen k (jump i p) x; unfold zen; rw [Finset.sum_range_succ',Finset.sum_range_succ']; rw [show piece 0 p (x+_)=piece 0 p x from rfl,add_sub_add_right_eq_sub, ← Finset.sum_sub_distrib]
  exact sum_congr rfl fun j _ => congr_fun (difference p j i) x
lemma t_turn (k:ℕ)(p:Shift α→E)(i:α): jump i (tail (k+1) p) = tail k (jump i p):= by
  rw [show jump i (tail (k+1) p) = jump i p - jump i (zen (k+1) p) from funext fun x=> by simp only [jump,tail,Pi.sub_apply]; abel, turn]; rfl
lemma base (k:ℕ)(p:Shift α→E) : piece (k+1) p 0=0:= by simp [piece]
lemma trace (k:ℕ)(p:Shift α→E): tail (k+1) p 0=0:= by unfold tail zen; rw [Pi.sub_apply,Finset.sum_range_succ']; simp_rw [base]; simp [piece]

variable {p:Shift α→E} {C:ℝ}
private lemma predecessor {x : Shift α} (h : x≠0) : ∃ (i : α) (y : Shift α),
    size x=size y+1 ∧ (x=y+arc i ∨ x=y-arc i) := by
  obtain ⟨i,hi⟩ : ∃ i,x i≠0 := by by_contra! he; exact h (funext he)
  rcases lt_or_gt_of_ne hi with H|H
  · refine ⟨i,x+arc i,?_,Or.inr (by abel)⟩
    unfold size; simp only [Pi.add_apply,arc, Pi.single_apply]
    rw [← Finset.add_sum_erase _ _ (mem_univ i), ← Finset.add_sum_erase _ (fun j => (x j + if j=i then 1 else 0).natAbs) (mem_univ i)]
    rw [sum_congr rfl (show ∀ j∈Finset.univ.erase i,(x j+(if j=i then 1 else 0)).natAbs=(x j).natAbs from fun j hj => by rw [if_neg (mem_erase.mp hj).1,add_zero]), if_pos rfl]
    omega
  refine ⟨i,x-arc i,?_,Or.inl (by abel)⟩
  unfold size; simp only [Pi.sub_apply,arc, Pi.single_apply]
  rw [← Finset.add_sum_erase _ _ (mem_univ i), ← Finset.add_sum_erase _ (fun j => (x j - if j=i then 1 else 0).natAbs) (mem_univ i)]
  rw [sum_congr rfl (show ∀ j∈Finset.univ.erase i,(x j-(if j=i then 1 else 0)).natAbs=(x j).natAbs from fun j hj => by rw [if_neg (mem_erase.mp hj).1,sub_zero]), if_pos rfl]
  omega

omit [NormedSpace ℝ E] in
lemma pointwise (n : ℕ) (h : p 0=0) (he : 0 ≤ M) (hh : ∀ i : α,∀ x : Shift α, (size x:ℝ) ≤ C →
    ‖jump i p x‖ ≤ M*(1+(size x:ℝ))^n) (x : Shift α) (hx : (size x:ℝ) ≤ C) :
    ‖p x‖ ≤ M*(1+(size x:ℝ))^(n+1) := by
  suffices ∀ k : ℕ,∀ x,size x=k → (size x:ℝ) ≤ C → ‖p x‖ ≤ M*(1+(size x:ℝ))^(n+1) by exact this _ _ rfl hx
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro x hk hi
    by_cases hx:x=0
    · subst x; rw [h,norm_zero]; positivity
    obtain ⟨i,y,ht,hP⟩:= predecessor hx
    have hl : (size y:ℝ)+1=size x := by exact_mod_cast ht.symm
    have hy : 0 ≤ (size y:ℝ) := by positivity
    have hC : (size y:ℝ) ≤ C := by linarith
    have hb := ih (size y) (hk ▸ (show size y < size x by omega)) y rfl hC
    let d := 1+(size x:ℝ)
    have hd : 0 ≤ d := by unfold d; positivity
    have hA : ‖p x-p y‖ ≤ M*d^n := by
      rcases hP with H|H
      · have he' : p x-p y=jump i p y := H ▸ rfl
        rw [he']; apply (hh i y hC).trans
        unfold d; gcongr; omega
      rw [norm_sub_rev]
      have he' : p y-p x=jump i p x := congr_arg (fun v => p v-p x) (show y=x+arc i by rw [H]; abel)
      rw [he']; exact hh i x hi
    apply le_trans (b:=‖p x-p y‖+‖p y‖)
    · simpa using norm_add_le (p x-p y) (p y)
    apply (add_le_add hA hb).trans
    have hf : M*(1+(size y:ℝ))^n ≤ M*d^n := by unfold d; gcongr; omega
    have hl' : (1+(size y:ℝ))+1=d := by unfold d; linarith
    change _ ≤ M*d^_
    rw [pow_succ,pow_succ]
    have H0 := mul_le_mul_of_nonneg_right hf (show (0:ℝ) ≤ 1+(size y:ℝ) by positivity)
    calc
      _ ≤ M*d^n+M*(d^n * (1+(size y:ℝ))) := by nlinarith only [H0]
      _ = M*(d^n*d) := by rw [←hl']; ring

-- first in list differentiated first
def iterate (p : Shift α→E) : List α → Shift α→E
| [] => p
| i::l => iterate (jump i p) l

lemma localized (d : ℕ) (hM : 0 ≤ M) (R : ℝ) (h : ∀ l : List α, l.length = d → ∀ x,(size x:ℝ) ≤ R → ‖iterate p l x‖ ≤ M)
    (x : Shift α) (he : (size x:ℝ) ≤ R) : ‖tail d p x‖ ≤ M*(1+(size x:ℝ))^d := by
  induction d generalizing x p with
  | zero => simpa only [tail,Pi.sub_apply, Quill.zen, Finset.range_zero, Finset.sum_empty,sub_zero,pow_zero,mul_one] using (show ‖p x‖ ≤ M from h [] rfl x he)
  | succ i ih =>
    refine pointwise i (Quill.trace ..) hM (C:=R) (fun j v hv => ?_) x he
    rw [t_turn]; apply ih (p:=jump j p) ?_ v hv
    intro l hl; exact h (j::l) (by simp [hl])

-- Pieces are themselves polynomially controlled in the arbitrary norm. Sharper than multiplying-by-path powers each step.
lemma piece_pass (d:ℕ)(hM:0≤ M) (h:∀ l:List α, l.length=d→ ‖iterate p l 0‖ ≤ M)(x:Shift α):
    ‖piece d p x‖ ≤ M * (1+(size x:ℝ))^d := by
  induction d generalizing p x with
  | zero => simpa only [pow_zero,mul_one,piece] using (show ‖p 0‖ ≤ M from h [] rfl)
  | succ k ih=>
    apply pointwise k (base k p) hM (C:=(size x:ℝ)) (fun j z _=> ?_) x le_rfl
    rw [difference]; apply ih (fun l hl=> h (j::l) (by simp [hl]))
lemma moderate (d:ℕ)(f:Shift α→E): ∃ C:ℝ,0≤C ∧ ∀ v,‖piece d f v‖ ≤ C*(1+(size v:ℝ))^d := by
  let V:= List.Vector α d; letI : Fintype V := Fintype.ofEquiv (Fin d→α) (Equiv.vectorEquivFin α d).symm
  let C:= ∑ l:V, ‖iterate f l.val 0‖; have hC:0≤C:= sum_nonneg fun i _=> norm_nonneg _
  refine ⟨C,hC,piece_pass d hC fun l hl=>?_⟩; exact (Finset.single_le_sum (s:=univ) (f:=fun i:V=> ‖iterate f i.val 0‖) (fun i _=> norm_nonneg _) (Finset.mem_univ (α:=V) (⟨l,hl⟩:V)))
section dual
-- SumBudget counts the weighted absolute sum. Typeless finite test in this dualization.
variable (w:β→ℝ)
def brush (s:Finset β)(T:β→ℝ)(f:Shift α→β→ℝ) (x:Shift α) := ∑ i∈s,T i*f x i
def Balanced (u:β→ℝ)(w:β→ℝ)(C:ℝ) := SumBudget (fun b=> w b* ‖u b‖) C
lemma jump_cash (s: Finset β)(T:β→ℝ)(f:Shift α→ β→ℝ)(i:α): jump i (brush s T f)=brush s T (fun x b=> jump i (fun x=> f x b) x) := by funext x; simp [jump,brush,mul_sub,sum_sub_distrib]
lemma piece_cash (s:Finset β)(T:β→ℝ)(f:Shift α→ β→ℝ)(d:ℕ): piece d (brush s T f)=brush s T (fun x b=> piece d (fun x=>f x b) x) := by
  induction d generalizing f with
  | zero=> rfl
  | succ k ih=>
    funext x; rw [piece]; simp_rw [jump_cash,ih]; simp only [brush,piece,smul_eq_mul]; simp_rw [mul_sum]; rw [sum_comm] -- need distribute
    apply sum_congr rfl; intro b _; apply sum_congr rfl; intro i _; ring
lemma tail_cash (s:Finset β)(T:β→ℝ)(f: Shift α→β→ℝ)(d:ℕ): tail d (brush s T f)=brush s T (fun x b=>tail d (fun x=>f x b) x):= funext fun x=> by simp only [tail,zen,Pi.sub_apply,piece_cash,brush,mul_sub,Finset.sum_sub_distrib,mul_sum]; rw [sum_comm (s:=Finset.range d)]
lemma iter_cash (s:Finset β)(T:β→ℝ)(f:Shift α→ β→ℝ)(l:List α): iterate (brush s T f) l=brush s T (fun x b=>iterate (fun x=> f x b) l x):= by induction l generalizing f with | nil=>rfl | cons i l ih=> rw [iterate,jump_cash,ih]; rfl
variable (u:β→ℝ) {w} (hw:∀ b,0≤ w b)
lemma paled (h : Balanced u w C) (s:Finset β)(T:β→ℝ)(hT:∀ b∈s, ‖T b‖ ≤ w b): ‖∑ i∈s,T i*u i‖ ≤ C := (norm_sum_le ..).trans <| (sum_le_sum fun i hi=> (norm_mul ..).trans_le <| mul_le_mul_of_nonneg_right (hT i hi) (norm_nonneg _)).trans <| (h.2.1.sum_le_tsum s fun i _=> h.1 i).trans h.2.2
include hw
lemma dualize (h: ∀ (s:Finset β) (T:β→ℝ), (∀ b∈s, ‖T b‖ ≤ w b)→ ‖∑ i∈s,T i*u i‖ ≤ C): Balanced u w C:= by
  apply budget_of_sum (fun i=> mul_nonneg (hw _) (norm_nonneg _)) -- lemma?
  intro s; let T b:=if u b<0 then -w b else w b
  have he b : w b *‖u b‖=T b*u b:= by unfold T; split_ifs with h; rw [Real.norm_eq_abs, abs_of_neg h]; ring; rw [Real.norm_of_nonneg (le_of_not_gt h)]
  simp_rw [he]; refine (le_abs_self _).trans (h s T (fun b _=>?_)); unfold T; split <;> first | rw [norm_neg,Real.norm_of_nonneg (hw _)] | rw [Real.norm_of_nonneg (hw _)]
lemma pencil (f:Shift α→β→ℝ) (d:ℕ) (hC:0≤C) (h:∀ l:List α,l.length=d→Balanced (fun b=> iterate (fun x=>f x b) l 0) w C) (x:Shift α): Balanced (fun b=>piece d (fun x=>f x b) x) w (C*(1+(size x:ℝ))^d):= dualize _ hw (fun s T hT=> by
  rw [show (∑ b∈s,T b*_)=piece d (brush s T f) x from (congr_fun (piece_cash s T f d) x).symm]; exact piece_pass _ hC (fun l hl=> by rw [iter_cash]; exact paled _ (h l hl) _ T hT) _)
lemma penciled (f:Shift α→β→ℝ) (d:ℕ)(R:ℝ)(hC:0≤C)(h:∀ l:List α, l.length=d→∀ x:Shift α,(size x:ℝ)≤R→Balanced (fun b=> iterate (fun x=>f x b) l x) w C)(x:Shift α)(hx:(size x:ℝ)≤R): Balanced (fun b=>tail d (fun x=>f x b) x) w (C*(1+(size x:ℝ))^d):= dualize _ hw (fun s T hT=> by
  rw [show (∑ b∈s,T b*_)=tail d (brush s T f) x from (congr_fun (tail_cash s T f d) x).symm]; exact localized _ hC R (fun l hl x hx=> by rw [iter_cash]; exact paled _ (h l hl x hx) _ T hT) _ hx)
end dual
-- all moment power prices postwidth. negative exponents not needed.
section
end
end Quill
end
end YM.Pulse.Spine

noncomputable section
namespace YM.Pulse.Spine.Quill
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior
open Finset Bloch Laurent Push.AbsoluteSums Extra.Iteration
open scoped Classical Topology BigOperators NNReal ENNReal
variable {α β X : Type} [Fintype α]{M σ η:ℝ}
lemma expPocket (σ η:ℝ) (d:ℕ)(he:η<σ) : ∃ K:ℝ,0<K∧∀ t:ℝ,0≤t→ (1+t)^d*Real.exp (η*t) ≤ K*Real.exp (σ*t) := by
  by_cases hz:d=0; subst d; exact ⟨1,one_pos,fun t ht=> by rw [pow_zero,one_mul,one_mul]; gcongr⟩
  let v:=(σ-η)/d; let k:= max 1 v⁻¹; have hd : 0<(d:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hz
  have hv : 0<v:= div_pos (sub_pos.mpr he) hd; have hk:1≤ k:= le_max_left ..
  refine ⟨k^d,pow_pos (zero_lt_one.trans_le hk) _,fun t ht=> ?_⟩
  have hu : 1+t ≤ k*(Real.exp (v*t)) := by
    have h := Real.add_one_le_exp (v*t)
    have hl : t≤k*(v*t) := by
      rw [← mul_assoc]; exact le_mul_of_one_le_left ht ((inv_mul_cancel₀ hv.ne').ge.trans (mul_le_mul_of_nonneg_right (le_max_right ..) hv.le))
    nlinarith only [h,hl,hk]
  apply (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hu d) (Real.exp_pos _).le).trans_eq
  rw [mul_pow, ← Real.exp_nat_mul, mul_assoc,← Real.exp_add]; unfold v; congr 2; field_simp; ring
lemma moment {T:Shift α→ℝ} (h:Width σ M T)(l:ℕ)(he:η<σ) : ∃ K:ℝ,0<K ∧ SumBudget (fun t:Shift α=> ‖T t‖*(Real.exp (η*size t)*(1+(size t:ℝ))^l)) (K*M):= by
  obtain ⟨K,hK,H⟩:= expPocket σ η l he; refine ⟨K,hK,budget_mono (budget_scale hK.le h) (fun _=>by positivity) fun p=> ?_⟩
  rw [← mul_assoc K, mul_comm ‖T p‖, mul_comm (Real.exp _)]; exact mul_le_mul_of_nonneg_right (H _ (Nat.cast_nonneg _)) (norm_nonneg _)
lemma moderate_zen (k:ℕ)(p: Shift α→ℝ): ∃ C:ℝ,0≤ C ∧ ∀ v, ‖zen k p v‖ ≤ C*(1+(size v:ℝ))^k:= by
  choose A hA H using fun i=> moderate i p; refine ⟨∑ i∈Finset.range k,A i,sum_nonneg fun i _=>hA _,fun v=>?_⟩; rw [sum_mul]; exact (norm_sum_le ..).trans (sum_le_sum fun i hi=> (H _ _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by simp) (mem_range.mp hi).le) (hA _)))
lemma zen_summable {σ:ℝ≥0}{T:Shift α→ℝ}(hp:0<σ)(h:Width σ M T)(p:Shift α→ℝ)(k:ℕ): Summable (fun x=> ‖T x*zen k p x‖):= by
  obtain ⟨C,hC,H⟩:=moderate_zen k p; obtain ⟨K,hK,h⟩:= moment h k (NNReal.coe_pos.mpr hp); let g:=fun v => C*(‖T v‖*(1+(size v:ℝ))^k)
  have hg : Summable g:= by simpa only [g,zero_mul,Real.exp_zero,one_mul] using h.2.1.mul_left C
  apply hg.of_nonneg_of_le (fun _=>norm_nonneg _); intro i; rw [norm_mul]; exact (mul_le_mul_of_nonneg_left (H i) (norm_nonneg _)).trans_eq (by unfold g; ring)
lemma stardust {σ:ℝ≥0}{F:Shift α→ℝ}(hp:0<σ)(h:Width σ M F)(p:Shift α→ℝ){n:ℕ}(l:Fin n→α) : (∑' x,torn l F x * zen n p x) = 0 := by
  induction n generalizing p with
  | zero=> simp [zen]
  | succ i IH =>
     let j:= l 0; let f:=torn (Fin.tail l) F; let a:= ascend j f; let g:= zen (i+1) p; have he x: torn l F x=a x-f x:= by rw [torn_succ];rfl
     have hF:= tear_cap h (Fin.tail l); have ha : Summable (fun x=>a x*g x):=(zen_summable hp (upward _ hF) p (i+1)).of_norm; have hb: Summable (fun x=>f x*g x):= (zen_summable hp hF p _).of_norm
     let e:= Equiv.addRight (arc j); have h e' : jump j g e'=zen i (jump j p) e':=congr_fun (turn ..) e'
     have hfar : Summable (fun x => a (e x) *g (e x)) := (e.summable_iff (f:=fun x=>a x*g x)).mpr ha
     simp_rw [he,_root_.sub_mul]; change (∑' x,(a x*g x - f x*g x))=_; rw [ha.tsum_sub hb,← e.tsum_eq (fun x=>a x*g x) ,← hfar.tsum_sub hb]; rw [← IH (jump j p) (Fin.tail l)] -- order
     apply tsum_congr; intro v; change ascend j f _ * g _ - f v*g v=f v*_
     rw [ascend,show e v=v+arc j from rfl,add_sub_cancel_right,←h v,jump,_root_.mul_sub] -- defeq
lemma stars {t:ℕ}{σ:ℝ≥0}{F:Tailor t→ℝ}(hp:0<σ)(h:Width σ M F)(p:Tailor t→ℝ)(k:ℕ)(he:Rays k (Laurent.read (pale F) ∘ axes)) : (∑' i,F i*zen k p i)=0 := by
  obtain ⟨η,hη,-,C,-,H⟩:= pry σ t k hp; obtain ⟨V,hV,h⟩:= H M F h he
  rw [h]; simp_rw [Finset.sum_apply,sum_mul]; rw [Summable.tsum_finsetSum (fun i _ => (zen_summable hη (tear_cap (hV i) i) p k).of_norm)]; simp_rw [stardust hη (hV _) p]; simp
end YM.Pulse.Spine.Quill
