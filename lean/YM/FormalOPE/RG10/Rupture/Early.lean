import YM.FormalOPE.RG10.Wing.Passport
/-!
 # Binary connection kernel recursion on the normalized chart
 EXP moments as well as polynomial, cost grow only with formal order and vertex rank.
 Gives a weakened-body but enough exponential suppression for repeated packet join diagrams.
 Use on center-collapsed or separated reports including same frame, EVERY analytic supply still
 separate. No primitive masks, and untested addresses interpreted by producer footprints.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Rupture
open Function PowerSeries Finset Route Route.Bulk HStein Multi.Vacuum.Gauss
open scoped Topology BigOperators Classical
variable {I B J L: Type} [Fintype J]
variable (q:I→Row J)(V:Channel (I⊕B))
local notation "P"=>Packet (I⊕B)
local notation "W"=>Channel (I⊕B)
local notation "f"=>stepwise q V

def split (q:I→Row J)(V:Channel (I⊕B))(N:Channel (I⊕B)) : Channel (I⊕B)→ₗ[ℂ] Channel B where
 toFun M:= Binary.disagreement q M N V
 map_add' p r:= by unfold Binary.disagreement; simp_rw [add_mul, ← send]; simp_rw [map_add]; ring; -- inspect
 map_smul' c p:= by change Binary.disagreement q (c • p) N V=c • _; unfold Binary.disagreement; simp_rw [smul_sub,← send, smul_mul_assoc, map_smul]; rw [smul_mul_assoc] -- inspect

variable (M N:Channel (I⊕B)) (p r:Packet (I⊕B)) (t :ℕ)
lemma start : split q V N M=stepwise q V (M*N)-stepwise q V M*stepwise q V N:= rfl
lemma commute : split q V N M=split q V M N:= by rw [start,start,_root_.mul_comm M N,mul_comm (stepwise q V M)]
lemma thru {u v':W} (h:Through t u v') : Through t (split q V N u) (split q V N v'):= by
 rw [start,start,send,send,send,send,send]
 intro i hi; rw [map_sub,map_sub,HStein.through_transfer q V t (h.mul (Through.refl _)) i hi, ((HStein.through_transfer q V t h).mul (Through.refl (transfer q N V))) i hi]
lemma shift : split q V N (PowerSeries.X^t*M)=PowerSeries.X^t * split q V N M:= by
 simp_rw [start,send]; rw [mul_assoc, paid, paid, mul_sub,mul_assoc]
lemma unit : stepwise q V 1=1:= by unfold stepwise; change move q (advance V * 1) * invOfUnit _ _=1; rw [mul_one,← show income q V=move q (advance V) from rfl]; apply mul_invOfUnit; rw [← coeff_zero_eq_constantCoeff_apply, accounting]; rfl -- inspect
lemma stable : split q V N 1=0:= by rw [start, one_mul,unit,one_mul]; ring

-- coefficient grades at one substrate
local notation "U"=> split q V

def foot (N: Channel (I⊕B)) : P→ₗ[ℂ] Packet B where
 toFun p:= coeff t (split q V N (C p))
 map_add' u v' := by simp
 map_smul' c p:= by have he : C (c • p) = c • C p:= by apply PowerSeries.ext; intro i; cases i <;> simp
                    change coeff t (U N (C (c • p)))=c • _; rw [he, _root_.map_smul, coeff_smul]
lemma stance : foot q V t N p=coeff t (split q V N (C p)):= rfl -- order?
lemma swapped : foot q V t (C r) p=foot q V t (C p) r:= by rw [stance,stance,commute]
-- processing all perturbative orders, paying rank change for second source in same coupling step
lemma expand : coeff t (split q V N M)=∑ i∈antidiagonal t, foot q V i.2 N (coeff i.1 M):= by
 rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j=> foot q V j N (coeff i M)), thru q V N t (Wing.Facets.paper M t) t le_rfl,map_sum,map_sum]
 apply sum_congr rfl; intro i hi; rw [Wing.Facets.radical, shift, coeff_X_pow_mul', if_pos (mem_range_succ_iff.mp hi)]; rfl
lemma thorough : coeff t (split q V N M)=∑ i∈antidiagonal t,∑ j∈antidiagonal i.2, foot q V j.2 (C (coeff j.1 N)) (coeff i.1 M):= by rw [expand]; refine sum_congr rfl (fun i hi=>?_); rw [stance,commute,expand]; apply sum_congr rfl; exact fun j _=> swapped q V ..
lemma upstairs (b:B) : foot q V t N (MvPolynomial.X (Sum.inr b)*p)=MvPolynomial.X b*foot q V t N p:= by rw [stance,stance,start,start,_root_.map_mul (C (R:=Packet (I⊕B)))]; simp_rw [send]; rw [mul_assoc (C (MvPolynomial.X (Sum.inr b))), show C (MvPolynomial.X (Sum.inr b) : Packet (I⊕B))=sprout _ from rfl,HStein.coarse,HStein.coarse,mul_assoc (sprout b),← mul_sub, sprout, coeff_C_mul] -- type ambiguity
lemma stable_row : foot q V t N 1=0:= by rw [stance,map_one,stable,map_zero]

variable [Fintype I] (a:I)
local notation "D"=> journeyD (uptick q a)
-- move entire commutator before splitting p; V may contain only-coarse counterterms too.no effect
lemma turns (h : coeff 0 V=0) : split q V N (sprout (.inl a)*M)= split q V N ((journeyD (uptick q a) M)+journeyD (uptick q a) V * M)+stepwise q V (M*journeyD (uptick q a) N) := by
 simp_rw [start,send]; rw [mul_assoc (sprout (Sum.inl a)), bill _ _ _ _ h,bill _ _ _ _ h, Derivation.leibniz]; simp_rw [smul_eq_mul];
 rw [show M*D N+N*D M+D V*(M*N)=(D M+D V*M)*N+M*D N by ring, ← send, _root_.map_add]; simp_rw [send]; ring
lemma bushes (h:coeff 0 V=0) : foot q V t (C r) (MvPolynomial.X (Sum.inl a)*p) = foot q V t (C r) (uptick q a p)+ (∑ j∈antidiagonal t,foot q V j.2 (C r) (uptick q a (coeff j.1 V)*p))+ opt q V t (p*uptick q a r) := by
 have hl (p:P): D (C p)=C (uptick q a p):= by apply PowerSeries.ext; intro i; rw [shelves]; cases i <;> simp
 rw [stance,_root_.map_mul, show C (MvPolynomial.X (Sum.inl a))=sprout _ from rfl, turns _ _ _ _ a h, hl r,←_root_.map_mul, map_add, _root_.map_add, hl p,map_add]; rw [expand _ _ (journeyD (uptick q a) V*C p) (C r) t]; simp_rw [coeff_mul_C,shelves]; rfl -- inspect

end YM.FormalOPE.RG10.Rupture
