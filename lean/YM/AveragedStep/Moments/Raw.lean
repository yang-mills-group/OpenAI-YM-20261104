import YM.AveragedStep.Joint.Face
import YM.AveragedStep.Joint.Noise
/-! # Moment books on the actual paired law. No product assumption.

Suppress repetitions only when the source language itself has suppressed them.
`Ranked` is at one specified load, not a uniform analytic or exponential
moment. In the rare diagnostic below we pay a different load.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AveragedStep
open Filter Function Lattice Wilson RG MeasureTheory
open scoped Topology BigOperators Classical

private lemma sum_power {I:Type*} (s:Finset I)(z:I→ℝ)(h:s.Nonempty)(m:ℕ):
    |∑ i∈s,z i|^m ≤ (s.card:ℝ)^m * ∑ i∈s, |z i|^m := by
  obtain ⟨i,hi,H⟩ := Finset.exists_max_image s (fun i=>|z i|) h
  have he : |∑ i∈s,z i|≤ (s.card:ℝ)* |z i|:= (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum H).trans_eq (by simp))
  refine (pow_le_pow_left₀ (abs_nonneg _) he m).trans ?_
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (f:=fun j=>|z j|^m) (fun j _=>by positivity) hi) (by positivity)

private lemma product_power {I:Type*} (s:Finset I)(z:I→ℝ) :
    (∏ i∈s,|z i|) ≤ 1+∑ i∈s,|z i|^s.card := by
  rcases s.eq_empty_or_nonempty with h|h
  · simp [h]
  obtain ⟨i,hi,H⟩:= Finset.exists_max_image s (fun i=> |z i|) h
  have hh := Finset.prod_le_prod (s:=s) (f:=fun j=>|z j|) (g:=fun _=>|z i|)
     (fun j _=>abs_nonneg _) H
  apply le_add_of_nonneg_of_le zero_le_one
  apply hh.trans
  rw [Finset.prod_const]; exact Finset.single_le_sum (f:=fun i=>|z i|^s.card) (fun j _=>by positivity) hi

variable {G:Gauge}{c f:Side}{S:StepData c f}{τ:ℝ}
structure Ranked (τ:ℝ) (q:Query S G) (m:ℕ) (C:ℝ) : Prop where
   safe : Admits q
   bill : readQ S (τ^2) (fun i x=> |q i x|^m) ≤ C
namespace Ranked
variable {q d : Query S G} {m : ℕ} {C D : ℝ}
lemma enlarge (h : Ranked τ q m C)(he:C ≤ D): Ranked τ q m D := ⟨h.safe,h.bill.trans he⟩

variable (hb : S.patch.Branches S.kernel G)
include hb
lemma zero (h:Admits q): Ranked τ q 0 1:= ⟨h,(by simp [read_number S (τ^2) hb 1])⟩
lemma const (k:ℝ): Ranked τ (S:=S) (G:=G) (fun _ _=>k) m (|k|^m):=⟨Admits.const k,(read_number S (τ^2) hb _).le⟩
lemma below (h:Admits d) (hh:Ranked τ q m C)
    (he:∀ i x,S.likelihood x.1 i≠0→ |d i x| ≤ |q i x|): Ranked τ d m C:=
  ⟨h,(read_le _ _ hb ((Admits.abs h).npow m) (hh.safe.abs.npow m)
    (fun i x hx=>pow_le_pow_left₀ (abs_nonneg _) (he i x hx) _)).trans hh.bill⟩
omit hb in
lemma scale (h:Ranked τ q m C)(k:ℝ):Ranked τ (k • q) m (|k|^m*C):= by
  refine ⟨h.safe.scale k,?_⟩
  simp_rw [Pi.smul_apply,smul_eq_mul,abs_mul,mul_pow]
  change readQ S (τ^2) ((|k|^m:ℝ) • fun i x=> |q i x|^m) ≤ _
  rw [read_scale]; exact mul_le_mul_of_nonneg_left h.bill (by positivity)
omit hb in
lemma reflect (h:Ranked τ q m C): Ranked τ (fun i x=>|q i x|) m C:= by
  refine ⟨h.safe.abs,?_⟩; simpa only [abs_abs] using h.bill
variable {I : Type*}
lemma sum (s:Finset I) (z:I→Query S G)(B:I→ℝ)(h:∀ i∈s,Ranked τ (z i) m (B i)) (hm : m≠0):
    Ranked τ (fun i x=>∑ j∈s,z j i x) m ((s.card:ℝ)^m*∑ j∈s,B j):=by
  have hd:=Admits.sum s z fun i hi=> (h i hi).safe
  refine ⟨hd,?_⟩
  rcases s.eq_empty_or_nonempty with ht|ht
  · subst s; simp only [Finset.sum_empty,abs_zero,zero_pow hm,read_number S _ hb, mul_zero,le_rfl]
  let D j (i:S.Choices)(x:Board G c f):=|z j i x|^m
  let Y : Query S G :=fun i x=>∑ j∈s,D j i x
  have hf (j) (hj:j∈s): Admits (D j) := ((h j hj).safe.abs.npow m)
  apply (read_le _ _ hb (hd.abs.npow m)
    ((Admits.sum s D hf).scale ((s.card:ℝ)^m)) (fun i x _=>sum_power s (fun j=>z j i x) ht m)).trans
  rw [read_scale,read_fin_sum _ _ hb _ _ hf]; apply mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact Finset.sum_le_sum fun j hj=> (h j hj).bill
lemma many (s:Finset I)(z:I→Query S G)(B:I→ℝ)(h:∀ i∈s,Ranked τ (z i) s.card (B i)):
    readQ S (τ^2) (fun i x=>∏ j∈s,|z j i x|) ≤ 1+∑ j∈s,B j:=by
  let D j : Query S G :=fun i x=> |z j i x|^s.card
  have he(j)(hj:j∈s) : Admits (D j):=(h j hj).safe.abs.npow _
  let d' : Query S G:=fun i x=>∑ j∈s,D j i x
  have ht:Admits (1+d'):=Admits.one.add (Admits.sum s D he)
  apply (read_le _ _ hb (Admits.product s _ (fun i hi=>(h i hi).safe.abs)) ht
     (fun i x _=>product_power s (fun j=>z j i x))).trans
  rw [read_add _ _ hb Admits.one,read_one _ _ hb,read_fin_sum _ _ hb s _ he]
  · exact add_le_add_right (Finset.sum_le_sum fun i hi=> (h i hi).bill) _
  exact Admits.sum s D he
end Ranked
end YM.AveragedStep
