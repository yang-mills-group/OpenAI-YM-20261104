import YM.RegulatorIR.Momentum.Bore

/-!
# Polynomial momentum pairing
No convention on complex conjugates needed; order2 μ uses REAL slope. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Momentum
open Function Set Filter Finset Budget Budget.Packet Budget.Tuple Lattice Laurent Geometry Spatial Sources Oracle Oracle.Quarry RG Bloch Precision Tree PertExtension Geometry.Field Exterior Work.F08
open scoped Topology ENNReal NNReal BigOperators Classical Matrix PowerSeries
variable {X Y V:Type} {G:Gauge} {m p:ℕ}{σ F A:ℝ}

def dial (a:Room)(v:Cover):ℝ:=∑ x : Axis,a x * v x
lemma dial_sum (a b:Room)(p:Cover): dial (a+b) p=dial a p+dial b p:=by simp only [dial,Pi.add_apply,add_mul,sum_add_distrib]
lemma dial_step (a:Room)(i:Axis): dial a (hop i)=a i:=by unfold dial; rw [Finset.sum_eq_single i]; simp;intro j _ hj;simp [hj];simp
lemma dial_probe (v:Cover)(i:Axis): dial (Lattice.step i) v=(v i:ℝ):=by simp only [dial,step_apply,ite_mul,one_mul,zero_mul,sum_ite_eq']; exact if_pos (Finset.mem_univ i)
lemma dial_diff (a:Room)(v t:Cover): dial a (v-t)=dial a v-dial a t:=by simp only [dial,Pi.sub_apply,Int.cast_sub,mul_sub,sum_sub_distrib]
lemma dial_norm (a:Room)(v:Cover): ‖dial a v‖ ≤ ‖a‖*size v:=by
 unfold dial size;push_cast;rw [mul_sum]; apply (norm_sum_le ..).trans
 apply sum_le_sum;intro i _; rw [norm_mul, ← norm_natAbs,Real.norm_natCast];exact mul_le_mul_of_nonneg_right (norm_le_pi_norm a i) (by positivity)
lemma step_cost (a:Room)(v:Cover)(h:0<σ)(p:ℕ) : ‖dial a v ^p‖ ≤ (‖a‖^p*scar σ p)*Real.exp (σ*size v):=by
 rw [_root_.norm_pow]; refine (pow_le_pow_left₀ (norm_nonneg _) (dial_norm ..) _).trans ?_; rw [mul_pow,mul_assoc];gcongr; apply le_trans _ (scars σ p h|>.2 (size v));gcongr; linarith

section harmonics
def recital (f:Cover→ℝ) (p:ℕ)(a:Room):ℝ:= ∑' v, f v * dial a v ^p
variable {P Q: Cover→ℝ}(h:Width σ F P)(hv:Width σ A Q)(hp:0<σ)
include h hp
lemma inhaled (n:ℕ)(a:Room): Summable fun v=> P v * dial a v^n:=by
 refine Summable.of_norm_bounded (h.2.1.mul_left (‖a‖^n*scar σ n)) (fun z=>?_);rw [norm_mul,mul_comm (‖P z‖), ← mul_assoc]; exact mul_le_mul_of_nonneg_right (step_cost a z hp n) (norm_nonneg _)
include hv
lemma allot (a:Room)(n:ℕ): recital (P-Q) n a= recital P n a-recital Q n a:=by unfold recital; simp_rw [Pi.sub_apply, sub_mul,(inhaled h hp n a).tsum_sub (inhaled hv hp n a)]
set_option maxHeartbeats 500000 in
lemma seamed (a: Room)(p:ℕ): recital (routed id P fun _=>Q) p a=∑ i∈range (p+1),recital P i a*recital Q (p-i) a * (p.choose i):=by
 let f (q z:Cover):= P q*Q (z-q)*dial a z^p
 let N:=range (p+1); let c (i:ℕ):ℝ:= p.choose i;let g (q:Cover)(i):= P q * dial a q ^i;let G(q:Cover)(i):= Q q*dial a q ^(p-i)
 have he: Summable fun t:Cover×Cover=> f t.1 t.2 := by
    let hb:= paths_budget (d:=id) hp.le (fun i=>le_rfl) h (fun _=> hv); let H(z:Cover):=Real.exp (σ * size z)
    have hz: Summable (fun (t:Cover×Cover)=>H t.2 * ‖P t.1*Q (t.2-t.1)‖):= hb.2.1
    apply Summable.of_norm_bounded (hz.mul_left (‖a‖^p*scar σ p)); intro t; unfold f;rw [norm_mul, mul_comm (‖P _ * _‖), ← mul_assoc];exact mul_le_mul_of_nonneg_right (step_cost a t.2 hp p) (norm_nonneg _)
 have hm (q z:Cover): f q z=∑ i∈N,g q i * G (z-q) i * c i:=by
    unfold f g G;rw [show dial a z=dial a q+dial a (z-q) by rw [dial_diff];ring]; rw [add_pow,Finset.mul_sum]; exact sum_congr rfl fun i _=>by unfold c;ring
 have ht (q:Cover)(i:ℕ): Summable (fun z=>G (z-q) i):=by
    have hh:Summable (fun z:Cover=>G z i):= inhaled hv hp _ a
    exact (show Summable ((fun z:Cover=>G z i) ∘ Equiv.subRight q) from (Equiv.subRight q).summable_iff.mpr hh)
 calc
    _ = ∑' z:Cover,∑'q:Cover,f q z:=by
      unfold recital routed; simp_rw [← tsum_mul_right];rfl
    _ = ∑' q:Cover,∑' z:Cover,f q z:= (Summable.tsum_comm (f:=f) he)
    _ = ∑' q:Cover,∑ i∈N,g q i*recital Q (p-i) a*c i:=by
      apply tsum_congr; intro q; simp_rw [hm]; rw [Summable.tsum_finsetSum (fun i _=>((ht q i).mul_left _).mul_right _)];apply sum_congr rfl; intro i _; rw [tsum_mul_right,tsum_mul_left]; have hx : (∑' x:Cover,G (x-q) i)=recital Q (p-i) a:= (Equiv.subRight q).tsum_eq (fun z=>G z i)
      exact congr_arg (fun z=>g q i * z * c i) hx
    _ = _:=by rw [Summable.tsum_finsetSum (fun i _=>((inhaled h hp i a).mul_right (recital Q (p-i) a)).mul_right (c i))]; simp_rw [tsum_mul_right]; rfl
end harmonics

section spin
def wax (K:Row X Y)(p:ℕ)(a:Room): Matrix X Y ℝ:= Matrix.of fun i j=> recital (K i j) p a
variable {M:Row X Y}(h:M.strip σ F)(hp:0<σ)
include h hp
lemma support_sub {N:Row X Y}(hv:N.strip σ A) (a:Room)(n:ℕ): wax (minusRows M N) n a=wax M n a-wax N n a:=by ext1 i j; exact allot (h i j) (hv i j) hp a n
lemma wax_mul {N:Row Y V}[Fintype Y](hv:N.strip σ A)(a:Room)(p): wax (composeRows M N) p a=∑ i∈range (p+1), (p.choose i:ℝ) • (wax M i a * wax N (p-i) a) :=by
 ext1 x y;rw [wax,Matrix.of_apply,recital];unfold composeRows; simp_rw [Finset.sum_mul]
 rw [Summable.tsum_finsetSum (fun i _=> inhaled (width_routed (d:=id) hp.le (fun w=>le_rfl) (h x i) (fun _=> hv i y)) hp p a)]
 change ∑ j, recital (routed id (M x j) (fun _=> N j y)) p a=_
 simp_rw [fun i:Y=>seamed (h x i) (hv i y) hp a p]; rw [sum_comm,Matrix.sum_apply];apply sum_congr rfl; intro i _; rw [Matrix.smul_apply, Matrix.mul_apply,smul_eq_mul, Finset.mul_sum]; exact sum_congr rfl fun _ _=>mul_comm ..
omit h hp in
lemma wand0 (a:Room): (wax M 0 a).map ((↑):ℝ→ℂ)=M.read 0:=by
 ext1 i j; rw [Matrix.map_apply,wax,Matrix.of_apply,recital];simp only [pow_zero,mul_one,Row.read,Matrix.of_apply,Laurent.read,mode_constant,one_smul];rw [Complex.ofReal_tsum]
end spin
end YM.RegulatorIR.Momentum
