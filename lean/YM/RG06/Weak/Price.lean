import YM.RG06.Weak.Tensor
/-!
# Explicit bare coefficient costs of oriented paths

Uniform in the length/period for bounded color letters along this path;
no loss exponential in length, useful with a fixed exponential length
charge. Need to handle zero order separately (matrix unit need not have
norm one in Frobenius). No integrated, mask or group derivative cost inferred
here. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG06.Weak
open scoped Topology ContDiff Classical BigOperators Matrix.Norms.Frobenius
open Function Finset Lattice

def weight (r : ℝ) (n : ℕ):=r^n*(n.factorial:ℝ)⁻¹
@[simp] lemma weight_zero (r):weight r 0=1:=by simp [weight]
lemma weight_pos {r : ℝ}(h:0≤r)(n:ℕ):0≤weight r n:=by unfold weight; positivity
lemma weight_pascal (r t : ℝ)(n:ℕ): (∑ i∈ Finset.range (n+1),weight r i * weight t (n-i))=weight (r+t) n:=by
  unfold weight; rw [add_pow,Finset.sum_mul]
  apply Finset.sum_congr rfl; intro i hi
  have he:=factorial_rule (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  rw [show r ^ i * _ * (t ^ (n - i) * _)=r^i*t^(n-i)*((n.factorial:ℝ)⁻¹*(n.choose i:ℝ)) by rw [he]; ring]
  ring

variable {S : Type*} [NormedRing S]

/-- Unital (and bounded at all higher coefficients). -/
structure Fair (F:ℕ→ S)(r:ℝ) :Prop where
  flat : F 0=1
  bounds : ∀ n:ℕ,n ≠ 0 → ‖F n‖ ≤ weight r n
-- Could also use below with S=ℂ. Need zero sequence separate.
structure Allow (F:ℕ→ S)(r:ℝ) :Prop where
  cap : ∀ n:ℕ, ‖F n‖ ≤ weight r n

variable {F H:ℕ→ S}{r q:ℝ}

lemma join_budget {b c : ℝ}(h:∀ i j, ‖F i*H j‖≤ weight b i*weight c j): Allow (join F H) (b+c) := ⟨fun n=>by
  rw [join_range,← weight_pascal]; exact (norm_sum_le ..).trans (Finset.sum_le_sum fun i _=>h ..)⟩
-- no NormOneClass needed: kill identity before taking norm
lemma Fair.both {b c:ℝ}(hf:Fair F b)(hh:Fair H c)(hc:0≤b):Fair (join F H) (b+c):=by
 constructor
 · rw [join_range]; simp [hf.flat,hh.flat]
 intro n hn; rw [join_range,← weight_pascal]
 refine (norm_sum_le ..).trans (Finset.sum_le_sum fun i hi=>?_)
 by_cases h : i=0
 · subst i; rw [hf.flat,one_mul,weight_zero,one_mul]; simpa using hh.bounds n hn
 by_cases he:n-i=0
 · rw [he,hh.flat,mul_one,weight_zero,mul_one]; exact hf.bounds i h
 exact (norm_mul_le ..).trans (mul_le_mul (hf.bounds _ h) (hh.bounds _ he) (norm_nonneg _) (weight_pos hc _))

lemma Allow.right {b c:ℝ}(h:Allow F b)(hG:Fair H c)(hb:0≤b):Allow (join F H) (b+c):=by
 apply join_budget; intro i j; cases eq_or_ne j 0 with
 | inl hj=>subst j; rw [hG.flat,mul_one,weight_zero,mul_one]; exact h.cap _
 | inr hj=>exact (norm_mul_le ..).trans (mul_le_mul (h.cap _) (hG.bounds _ hj) (norm_nonneg _) (weight_pos hb _))
lemma Allow.left {b c:ℝ}(hG:Fair F b)(h:Allow H c)(hc:0≤c):Allow (join F H) (b+c):=by
 apply join_budget; intro i j; cases eq_or_ne i 0 with
 | inl hj=>subst i; rw [hG.flat,one_mul,weight_zero,one_mul]; exact h.cap _
 | inr hj=>
   rw [mul_comm (weight b _)]; exact (norm_mul_le ..).trans ((le_of_eq (mul_comm ..)).trans (mul_le_mul (h.cap _) (hG.bounds _ hj) (norm_nonneg _) (weight_pos hc _)))

lemma positive_pow (a:S)(n:ℕ)(h:n ≠ 0): ‖a^n‖ ≤ ‖a‖^n:=by
 cases n with
 | zero=>exact absurd rfl h
 | succ n=>
   clear h
   induction n with
   | zero=>simp
   | succ n ih=>rw [pow_succ, pow_succ ‖_‖]; exact (norm_mul_le ..).trans (mul_le_mul_of_nonneg_right ih (norm_nonneg _))

variable {G:Gauge}

lemma fair_tile {x:G.Color}{b:ℝ}(h: G.colorScale*‖x‖ ≤ b):Fair (letter x) b where
  flat:=by simp [letter]
  bounds n hn:=by rw [letter,norm_smul,Real.norm_of_nonneg (by positivity),weight,mul_comm]; refine mul_le_mul_of_nonneg_right ((positive_pow _ _ hn).trans (pow_le_pow_left₀ (norm_nonneg _) ?_ _)) (by positivity); rwa [← G.colorMat_norm] at h

lemma Fair.reverse {A:ℕ→G.Mat}(h:Fair A r):Fair (back A) r:=by
  constructor
  · rw [back,h.flat,star_one]
  intro n hn; rw [back, norm_star]; exact h.bounds n hn

lemma cost_cycle {R:Type*}[AddCommGroup R][One R] (a:Links R G.Color)(x:Four R)(k:Walk)(hr:0≤r)(h:∀v∈inventory x k,G.colorScale*‖a v.1‖ ≤ r): Fair (cycle a x k) (r*k.length):=by
 induction k generalizing x with
 | nil=> refine ⟨rfl,?_⟩; intro n hn; change ‖seed (1:G.Mat) n‖ ≤ _; rw [seed,if_neg hn,norm_zero]; apply weight_pos; simp
 | cons d k ih=>
   have he:Fair (tile a (d.used x)) r:=fair_tile (h ((d.used x),d.neg) (by simp [inventory]))
   have ht:Fair (turn d.neg (tile a (d.used x))) r:=by unfold turn; split <;> first | exact he.reverse | exact he
   change Fair (join _ _) _
   rw [List.length_cons,Nat.cast_succ,mul_add,mul_one,add_comm (r*(k.length:ℕ)) r]
   have hh(v)(hv:v∈inventory (x+d.vec) k): G.colorScale * ‖a v.1‖ ≤ r:= h v (List.mem_cons_of_mem _ hv)
   apply Fair.both ht (ih (x+d.vec) hh) hr

lemma recover_cap (A:G.Mat) : G.colorScale * ‖Pert.First.recoverL G A‖ ≤ ‖A‖:=by
  change G.colorScale * ‖G.projectColor ((1 / 2:ℝ) • (A-star A))‖ ≤ _
  rw [mul_comm]; refine ((le_div_iff₀ G.colorScale_pos).mp (G.project_norm _)).trans ?_
  rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
  linarith only [(show ‖A-star A‖ ≤ ‖A‖+‖A‖ by simpa only [norm_star] using norm_sub_le A (star A))]

@[simp] lemma recover_one : Pert.First.recoverL G 1=0:=by change G.projectColor ((1/2:ℝ) • (1-star (1:G.Mat)))=0; simp

/-- colorMat ∘ skew converts unit path to zero. -/
lemma skew_cap {A:ℕ→G.Mat}(h:Fair A r):Allow (G.colorMat ∘ skew A) r := by
 constructor; intro n; rcases eq_or_ne n 0 with hr|hr
 · subst n; simp [skew,h.flat]
 rw [comp_apply,G.colorMat_norm]; exact (recover_cap ..).trans (h.bounds _ hr)

theorem cost_plate {R:Type*}[AddCommGroup R][One R] (a:Links R G.Color)(x:Four R)(k:Walk)(i j:Axis)(hr:0≤r)
    (hk:∀ v∈inventory x k,G.colorScale * ‖a v.1‖ ≤ r)
    (hb:∀ v∈inventory (stop x k) (square i j),G.colorScale * ‖a v.1‖ ≤ r)(n:ℕ) :
    ‖plateSeries (tile a) x k i j n‖ ≤ weight (r*(2*k.length+4:ℕ)) n/G.colorScale:=by
  let V:=cycle a x k; let Z:=cycle a (stop x k) (square i j)
  have hv : Fair V (r*k.length):=cost_cycle a x k hr hk
  have he : Fair Z (r*(4:ℕ)):=cost_cycle a _ _ hr hb
  have ht := ((skew_cap he).left hv (by positivity)).right hv.reverse (b:=r*k.length+r*(4:ℕ)) (by positivity)
  refine (G.project_norm _).trans ?_
  rw [le_div_iff₀ G.colorScale_pos]; rw [div_mul_cancel₀ _ G.colorScale_pos.ne']
  convert! ht.cap n using 2; push_cast; ring
end YM.RG06.Weak
