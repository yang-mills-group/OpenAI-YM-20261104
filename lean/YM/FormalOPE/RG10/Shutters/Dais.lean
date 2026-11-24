import YM.FormalOPE.RG10.Shutters.Pivot
import YM.Next.WARD_BIN.Degree
/-! Sign conventions on X-action's coupling inversion. Equivariance under curvature slot parity. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Shutters
open Function Maxwell Labels Extraction Filter Finset Extra.FD PertExtension MeasureTheory
  Topology Metric PertExtension.Position PertExtension.Physical PowerSeries Triangle
  RG10.Position
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}{F:Frames G}{d n:ℕ}(q:ℕ+){P:Plan F}
local notation "a"=> PertExtension.Physical.Profile.n
local notation "ℳ" d => Mark (Deck F d) PertExtension.Physical.Profile.n
local notation "w" d=> Deck.slots F d
local notation "☕" d=>Pert.Parity.Coat F d

lemma curtain (i:Deck F d) : (☕ d) (deck F d i)= lapse (S:=ℂ) ((w d) i) • deck F d i:= by
 let v:= precedent F d i; let z:= Deck.grades F d i; let T:= deck F d
 have he : Pert.Parity.wash G d v= lapse (S:=ℂ) ((w d) i) • v := by
   apply Subtype.ext; apply Labels.eval_ext; intro A; change Labels.read A (Pert.Parity.shadow G v.val)= Labels.read A (lapse (S:=ℂ) ((w d) i) • v.val)
   rw [Pert.Parity.shadow_read,map_smul,← show (-1:ℝ) • A = -A from neg_one_smul ℝ A]; rw [YM.WardBin.multiplied_grade (-1) A v (advance F d i)] -- args
   simp [lapse, smul_eq_mul,Complex.real_smul]
 have hf : T i= Pert.RawLabels.enroll F d v := (writes_inj F d) ((kept F d i).symm.trans (form F d v).symm)
 change (☕ d) (T i)= _ • T i; rw [hf, Pert.Parity.Coat_inherit,he,map_smul]

local notation "I"=> Fin 3
def entry (i: Fin 3) := if i=0 then 1 else 0
lemma basic_odd (i: Fin 3) : (☕ 6) (Pert.Triangle.basic F i)= lapse (S:=ℂ) (entry i) • Pert.Triangle.basic F i:= by
 have he := congr_fun (Pert.Triangle.oddity' F) i; by_cases h:i=0 <;> simpa only [entry,h, ↓reduceIte, comp_apply,lapse, neg_smul,one_smul,pow_zero,pow_one] using he

lemma paycheck {i:Fin 3}{j:Deck F 6}(h: Odd ((w 6) j+ entry i)): Peal.tune F i j=0 := by
 let T:= deck F 6; let x:=Pert.Triangle.basic F i
 have hp := basic_odd (F:=F) i; let Q : Module.End ℂ ((freeTable F).Field 6):= ☕ 6
 let b:= T.repr x; have he i: Q (T i)= lapse (S:=ℂ) ((w 6) i) • T i:= curtain i
 change Q (Pert.Triangle.basic F i)= _ at hp
 nth_rw 1 [← T.sum_repr (Pert.Triangle.basic F i)] at hp; simp_rw [map_sum,map_smul,he] at hp
 have hg:= congr_arg (fun y=> T.repr y j) hp; simp_rw [map_sum,map_smul,Finsupp.finsetSum_apply,Finsupp.smul_apply, Module.Basis.repr_self,Finsupp.single_apply,smul_eq_mul,mul_ite,mul_one,mul_zero] at hg
 let k:=Peal.tune F i j
 unfold T at hg; rw [Finset.sum_ite_eq', if_pos (mem_univ _), ← Peal.contour] at hg
 have he : lapse (S:=ℂ) (Deck.slots F 6 j)*lapse (entry i)= -1:= by rw [lapse,lapse,← pow_add,h.neg_one_pow]
 have hu: lapse (S:=ℂ) (Deck.slots F 6 j) ≠ lapse (entry i):= by intro hv; rw [hv,lap_twice] at he; norm_num at he
 apply Complex.ofReal_injective;
 exact eq_zero_or_eq_zero_of_mul_eq_zero («a»:=(k:ℂ)) (b:=lapse ((w 6) j)-lapse (entry i)) (by rw [mul_sub, show (k:ℂ)*_ = _ from hg]; ring) |>.resolve_right (sub_ne_zero.mpr hu)

local notation "g"=> rescale (-1:ℝ)
lemma blank (r:ℝ): g (PowerSeries.C r)=C r:= by rw [rescale_eq_subst]; exact subst_C _
lemma exposes (L:(ℳ 6)→fps) (h:snooze a (w 6) L=L)(x:Fin n↪ Fin 3) : g (Peal.touch F L x)=lapse (∑ k, entry (x k))*Peal.touch F L x := by
 unfold Peal.touch; simp_rw [map_sum,map_mul, mul_sum, blank]; apply sum_congr rfl; intro i _
 by_cases ht: ∏ k,Peal.tune F (x k) (i k)=0
 · simp [ht]
 have hu : ∀ j, ¬ Odd ((w 6) (i j) + entry (x j)) := fun j h=> ht (prod_eq_zero (mem_univ j) (paycheck h))
 rw [show g (L ⟨⟨n,_⟩,_⟩) = _ from ((lamp a (w 6) L).mp h) ⟨⟨n,_⟩,_⟩]; unfold slots; change _ * (lapse (∑ k,(w 6) (i k))*_)=_;
 have he:lapse (S:=fps) (∑ k,(w 6) (i k))= lapse (∑ k, entry (x k)):= by unfold lapse; rw [← prod_pow_eq_pow_sum,← prod_pow_eq_pow_sum]; exact prod_congr rfl (fun k _=>lap_twist (hu k))
 rw [he]; exact mul_left_comm ..

lemma onOdd (L:(ℳ 6)→fps) (h:snooze a (w 6) L=L) : g (Peal.mint F L)= -Peal.mint F L := by
 let f(n)(x:Fin n↪Fin 3):= Peal.touch F L x; let y:= Peal.together F L
 have he i : g (f 2 (Fin.succAboveEmb i))*g (f 1 (Peal.single i))= -(f 2 (Fin.succAboveEmb i)*f 1 (Peal.single i)):= by
   unfold f; rw [exposes L h,exposes L h];
   have he : (∑ k,entry ((Fin.succAboveEmb i) k)) + ∑ k,entry (Peal.single i k)=1:= by
     simp_rw [Fin.sum_univ_succ]; fin_cases i <;> decide
   rw [mul_assoc,lapse,lapse,mul_left_comm (Peal.touch F L (Fin.succAboveEmb i)) ((-1:fps)^_) _,← mul_assoc, ←pow_add, he]; simp
 have hh : g y=-y:= by
   change g (f 3 (.refl _)-(∑ k:Fin 3,_)+2 * ∏ i:Fin 3,_) = _; rw [map_add,map_mul,map_sub,map_ofNat,map_prod,map_sum]; simp_rw [map_mul]; change g (f 3 (.refl _))-(∑ k:Fin 3,g (f 2 (Fin.succAboveEmb k))*g (f 1 (Peal.single k)))+2 *∏ i:Fin 3,g (f 1 (Peal.single i))=_; simp_rw [he,sum_neg_distrib]; unfold f y Peal.together; simp_rw [exposes L h]; simp [Peal.single, Fin.prod_univ_succ, entry,lapse, Fin.sum_univ_succ]; ring
 have hu : constantCoeff y=0:= by have he:= congr_arg (coeff 0) hh; rw [coeff_rescale,pow_zero,one_mul,map_neg, coeff_zero_eq_constantCoeff_apply] at he; linarith
 unfold Peal.mint Triangle.deviation; change g (C (_:ℝ)*(y-C (constantCoeff y)))= _; unfold y at hu hh; simp [y,hu,hh, blank]
end YM.FormalOPE.RG10.Shutters
