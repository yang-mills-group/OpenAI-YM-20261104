import YM.RG06.Classical.Grant

/-!
# Taylor coefficient erasure propagation; no Wick/mask operators or coupling costs
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG06.ClassicalOn
open Function Analysis Tensor Continuum
open scoped ContDiff BigOperators Matrix.Norms.Frobenius Topology
variable {E F:Type*} [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
variable {G:Gauge}{k l:ℕ}{f u:E4→E}

def part (k:ℕ)(f:E4→E):E4→E:=Tensor.diagonal (Tensor.coeff f k 0)
lemma rate_part (k:ℕ)(f:E4→E):Level k (part k f):=Level.tax ..
lemma part_level (h:Level k f):part k f=f:=funext (h.indicates ·)
lemma part_spill (h:Level k f)(he:l≠k):part l f=0:=funext (h.indicates_other he ·)

lemma part_add (h:Good f)(hI:Good u)(k:ℕ):part k (f+u)=part k f+part k u:=by
 funext x; unfold part Tensor.diagonal; rw [coeff_add ((ContDiff.contDiffAt h).of_le (WithTop.coe_le_coe.mpr le_top)) ((ContDiff.contDiffAt hI).of_le (WithTop.coe_le_coe.mpr le_top)),add_apply,Pi.add_apply]
lemma part_scale (h:Good f)(k:ℕ)(a:ℝ):part k (a • f)=a • part k f:=by
 funext x; unfold part Tensor.diagonal; rw [Tensor.coeff_smul a ((ContDiff.contDiffAt h).of_le (WithTop.coe_le_coe.mpr le_top)),smul_apply,Pi.smul_apply]
lemma part_sum {I:Type*}(s:Finset I)(f:I→E4→E)(h:∀i∈s,Good (f i))(k:ℕ):part k (∑ i∈s,f i)=∑ i∈s,part k (f i):=by
 classical
 induction s using Finset.induction_on with
 | empty=> rw [Finset.sum_empty,Finset.sum_empty]; unfold part; rw [show coeff (0:E4→E) k _=0 from Tensor.coeff_zero k 0];rfl
 | insert a s hv H=>
    have he(i)(hi:i∈s):Good (f i):=h i (Finset.mem_insert_of_mem hi)
    have ht : Good (∑i∈s,f i):=by rw [show (∑i∈s,f i)=fun x=>∑i∈s,f i x from funext fun x=> Finset.sum_apply ..]; exact ContDiff.sum he
    rw [Finset.sum_insert hv, Finset.sum_insert hv, part_add (h a (Finset.mem_insert_self ..)) ht,H he]
lemma part_par (f:E4→E)(h:Good f)(k:ℕ)(i:Axis):par i (part (k+1) f)=part k (par i f):=funext (fun x=> Tensor.slot_lower (j:=k) ((ContDiff.contDiffAt h).of_le (WithTop.coe_le_coe.mpr le_top)) (basis i) x)

structure Secret (k:ℕ)(f:E4→E):Prop where
   good: Good f
   veiled(i:ℕ)(h:i<k):part i f=0

namespace Secret
lemma birth (h:Good f):Secret 0 f:= ⟨h,fun _ h=>False.elim (Nat.not_lt_zero _ h)⟩
lemma zero (k:ℕ):Secret k (fun _:E4=>(0:E)):=⟨contDiff_const,fun i h=>by unfold part;rw [Tensor.coeff_zero];rfl⟩
lemma add (h:Secret k f)(he:Secret k u):Secret k (f+u):=⟨ContDiff.add h.good he.good,fun i hi=>by rw [part_add h.good he.good,h.veiled _ hi,he.veiled _ hi,add_zero]⟩
lemma scale (h:Secret k f)(c:ℝ):Secret k (c • f):=⟨ContDiff.const_smul c h.good,fun i hi=>by rw [part_scale h.good,h.veiled _ hi,smul_zero]⟩
lemma descend (h:Secret (k+1) f)(b:Axis):Secret k (par b f):=⟨h.good.par b, fun i hi=>by rw [← part_par f h.good, h.veiled (i+1) (by omega),Level.bottom (Level.zero (E:=E) 0)]⟩
lemma at0 (h:Secret (k+1) f):f 0=0:=by
 have he:= congr_fun (h.veiled 0 (Nat.zero_lt_succ _)) (0:E4)
 simpa only [part, Tensor.diagonal, Tensor.coeff_apply_zero,Pi.zero_apply] using! he
lemma restore (h:Good f)(hh:f 0=0)(hD:∀b:Axis,Secret k (par b f)): Secret (k+1) f:=by
 refine ⟨h,?_⟩
 intro i hi
 rcases i with _|i
 · ext;simp [part,Tensor.diagonal, Tensor.coeff_apply_zero,hh]
 funext z
 have he(b:Axis):par b (part (i+1) f)=0:=by rw [part_par f h,(hD b).veiled _ (by omega)]
 have H:=(rate_part (i+1) f).euler z; simp_rw [he,Pi.zero_apply,smul_zero,Finset.sum_const_zero] at H
 exact (smul_eq_zero.mp H.symm).resolve_left (by positivity)

lemma low (h:Secret k f)(hm:l≤k): Secret l f:=⟨h.good,fun _ hi=>h.veiled _ (hi.trans_le hm)⟩
lemma vis (h:Level k f): Secret k f:=⟨h.smooth,fun _ hi=>part_spill h (ne_of_lt hi)⟩
lemma bracket_legal {A B:Section G}(h:Secret k A)(e:Good B): Secret k (bracket A B) :=by
 induction k generalizing A B with
 | zero=> exact birth (Good.mark h.good e)
 | succ k H=>
    refine restore (Good.mark h.good e) (by unfold bracket; rw [h.at0,map_zero];rfl) (fun i=>?_)
    rw [show par i (bracket A B)=bracket (par i A) B + bracket A (par i B) from funext (par_bracket h.good e i)]
    exact Secret.add (H (h.descend i) e) (H (h.low (Nat.le_succ _)) (e.par i))
lemma bracket_even {A B:Section G}(h:Good A)(he:Secret k B): Secret k (bracket A B):=by
 rw [show bracket A B = (-1:ℝ) • bracket B A from funext (fun x=>by rw [neg_one_smul]; exact bracket_anti ..)]
 exact (he.bracket_legal h).scale _
end Secret
end YM.RG06.ClassicalOn
