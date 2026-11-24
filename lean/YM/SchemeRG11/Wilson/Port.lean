import YM.SchemeRG11.Wilson.Mart
/-! Regulator-to-cover result. Raw top stencils, through one only. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Acorn
open Lattice Function Filter Haze Pert Bare Labels Bark MvPolynomial Tree Catch Cellular Full Atoll Pile Align Tile
open MeasureTheory ProbabilityTheory
open scoped Classical ContDiff Topology
variable {G:Gauge} {I:Type}[Fintype I][DecidableEq I]
variable (s:Finset I)(p:I→ Pile.pLabel G) {T:Itinerary} (u:I→ℕ→ Cover)(o:StepPath T)
variable {N:Side}
omit [Fintype I] [DecidableEq I] in
lemma assignment(h:ℝ)(d:I→ℕ)(hd:∀ i, IsWeightedHomogeneous Labels.generation (p i) (d i))(t:I→Site N):
 lined s t h p = h⁻¹^(∑ i∈s,d i) • lined s t 1 p:=by
 unfold lined; simp only [(dominion h _ (hd _)).1] -- argument tricky rec infinite when matching 1?
 simp only [map_smul]; simp only [MvPolynomial.smul_eq_C_mul,Finset.prod_mul_distrib,← _root_.map_prod, Finset.prod_pow_eq_pow_sum]
omit [Fintype I] in
lemma account(h:ℝ)(d:I→ℕ)(hd:∀ i, IsWeightedHomogeneous Labels.generation (p i) (d i))(t:I→Site N):
 dust s t h p=h⁻¹^(∑ i∈s,d i) • dust s t 1 p:=by
 unfold dust; rw [assignment s p h d hd, smul_add, mul_smul_comm, Finset.smul_sum]; congr 1; apply Finset.sum_congr rfl; intro i hi
 rw [(dominion h _ (hd i)).2,assignment (s.erase i) p h d hd,map_smul, show ∑ i∈s,d i=d i+∑ k∈s.erase i,d k from (Finset.add_sum_erase _ _ hi).symm,pow_add, smul_mul_smul_comm]

omit [Fintype I] [DecidableEq I] in
lemma vaultable (k:ℕ) (t:I→vellum G): adsorb (o k) (aerial s t (fun a=> u a k))=∏ i∈s,adsorb (poseN u (o:=o) k i) (t i):=by simp only [aerial,map_prod,vapour];rfl

def firstCovers (h:ℝ)(t:I→ Cover):= (-(1:ℝ)) * (∑ i:Axis,∑ j:Axis,∑' x : Cover, turnup s (fun a=>castZero h (p a)) t i j x)+ ∑ i∈s,(land G).avg (cross (t i) (castFirst h (p i)) * aerial (s.erase i) (fun a=>castZero h (p a)) t)
omit [Fintype I] in
lemma unpack(t:I→Site N):
 (spray G N).avg (dust s t 1 p)=-(1/2:ℝ)*(∑ i:Axis,∑ j:Axis,∑ x:Site N,Graft s (fun a=>castZero 1 (p a)) t i j x)+ ∑ i∈s, (spray G N).avg (adsorb (t i) (castFirst 1 (p i)) * lined (s.erase i) t 1 p):=by
 rw [dust,map_add,_root_.map_sum]; congr 1; rw [faces,smul_mul_assoc,map_smul,smul_eq_mul]; apply congrArg
 simp_rw [Finset.sum_mul, _root_.map_sum]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i hi;rw [Finset.sum_comm];rfl
include o
lemma traverse (hI:Interior T o)(hw:∀ a, Medium T (u a)): Flat T (fun k=> (spray G (T.period k)).avg (dust s (poseN (o:=o) u k) 1 p)- firstCovers s p 1 fun a=>u a k):=by
 let Q a:=castZero 1 (p a)
 let R(a : I)(k:ℕ):= (spray G (T.period k)).avg (adsorb (poseN u k (o:=o) a) (castFirst 1 (p a)) * lined (s.erase a) (poseN u k (o:=o)) 1 p) - (land G).avg (cross (u a k) (castFirst 1 (p a))*aerial (s.erase a) Q (fun a=>u a k))
 have hr(i:I)(hi:i∈s): Flat T (R i):=by
   let P:= update Q i (castFirst 1 (p i))
   have hp(k:ℕ): aerial s P (fun a=>u a k)=cross (u i k) (castFirst 1 (p i))*aerial (s.erase i) Q (fun a=>u a k):=by
     unfold aerial; rw [← Finset.mul_prod_erase _ _ hi]; simp only [P,Function.update_self]; apply congrArg; exact Finset.prod_congr rfl fun j hj=> by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
   apply sameF (brushed P s u hw hI); filter_upwards with k; rw [hp,map_mul]; erw [vaultable (s.erase i) u o k Q, vapour];rfl
 let A(i j:Axis)(k:ℕ):= (∑ x: Site (T.period k),Graft s Q (poseN u k (o:=o)) i j x) - 2* ∑' x:Cover,turnup s Q (fun a=>u a k) i j x
 have ht(i j:Axis):Flat T (A i j):= turnover s Q u hI hw i j
 have hh:Flat T (fun k=>∑ i:Axis,∑ j:Axis,A i j k):=finFlat _ _ fun i _=>finFlat _ _ fun j _=>ht i j
 apply sameF ((flatter hh (Tile.capped_c (-(1/2:ℝ)))).add (finFlat s R hr))
 filter_upwards with k
 rw [unpack]; unfold R A firstCovers
 rw [Finset.sum_sub_distrib]; simp_rw [Finset.sum_sub_distrib, ← Finset.mul_sum]; unfold Q; ring
omit o
omit [Fintype I] in
lemma downfall (d:I→ℕ)(hd:∀ i, IsWeightedHomogeneous Labels.generation (p i) (d i))(h:ℝ)(t: I→ Cover):
   firstCovers s p h t=h⁻¹^(∑ i∈s,d i)* firstCovers s p 1 t:=by
 have he(s:Finset I):aerial s (fun i=>castZero h (p i)) t=h⁻¹^(∑ i∈s,d i) • aerial s (fun i=>castZero 1 (p i)) t:=by
   unfold aerial; simp only [(dominion h _ (hd _)).1,map_smul]; simp only [MvPolynomial.smul_eq_C_mul,Finset.prod_mul_distrib,←_root_.map_prod, Finset.prod_pow_eq_pow_sum]
 have hf(i j:Axis): (∑' x : Cover, turnup s (fun a=>castZero h (p a)) t i j x)= h⁻¹^(∑ i∈s,d i)*(∑' x:Cover, turnup s (fun a=>castZero 1 (p a)) t i j x):=by simp_rw [turnup,he,mul_smul_comm,map_smul,smul_eq_mul, tsum_mul_left]
 unfold firstCovers; rw [mul_add,mul_left_comm _ (-(1:ℝ))]; congr 1
 · simp_rw [hf,Finset.mul_sum]
 rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi; rw [(dominion h _ (hd i)).2,map_smul,he, ← Finset.add_sum_erase _ _ hi, pow_add, smul_mul_smul_comm,map_smul];rfl
include o in
lemma enters (d:I→ℕ)(hd:∀ i, IsWeightedHomogeneous Labels.generation (p i) (d i))(hr:Interior T o)(hw:∀ a,Medium T (u a)) :
 Flat T (fun k=> (spray G (T.period k)).avg (dust s (poseN (o:=o) u k) (T.gap k) p)-firstCovers s p (T.gap k) fun a=>u a k):=by
 simp_rw [account s p (T.gap _) d hd, downfall s p d hd (T.gap _), map_smul, smul_eq_mul, ←mul_sub]; apply powerFlat _ (traverse s p u o hr hw)
abbrev coverGod (h:ℝ)(t:I→ Cover):= (land G).avg (aerial s (fun i=>castZero h (p i)) t)
include o in
omit [Fintype I] [DecidableEq I] in
lemma dashes(d:I→ℕ)(hd:∀ i, IsWeightedHomogeneous Labels.generation (p i) (d i))(hr:Interior T o)(hw:∀ a,Medium T (u a)) :
 Flat T (fun k=> (spray G (T.period k)).avg (lined s (poseN (o:=o) u k) (T.gap k) p)-coverGod s p (T.gap k) fun a=>u a k):=by
 have he(h:ℝ)(t:I→ Cover):coverGod s p h t=h⁻¹^(∑ i∈s,d i)*coverGod s p 1 t :=by
   unfold coverGod aerial; simp only [(dominion h _ (hd _)).1,map_smul]; simp only [MvPolynomial.smul_eq_C_mul, Finset.prod_mul_distrib,← map_prod,Finset.prod_pow_eq_pow_sum]; rw [C_mul',map_smul];rfl
 simp_rw [assignment s p (T.gap _) d hd,map_smul,smul_eq_mul,he (T.gap _),← mul_sub,coverGod,lined]; apply powerFlat
 apply sameF (brushed (fun a=>castZero 1 (p a)) s u hw hr); filter_upwards with k
 rw [vaultable s u o k]
end YM.SchemeRG11.Acorn
