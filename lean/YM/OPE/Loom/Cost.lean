import YM.OPE.Rate
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
/-!
# Budget class that accounts ANY polynomial in T

With engineering scale factor held explicit & positive eventually. During
matching-independent improvements and interpolation use `T ~ log(1/s)`.
Not controlled by merely subpower costs. No phase norm proxy here.
-/
set_option autoImplicit false
noncomputable section
open Filter Function Set
open scoped Topology BigOperators
namespace YM.OPE.Loom
variable {I J X Y Z : Type*}
def Bill [Norm X] (φ : Filter I) (T : I→ℝ) (F : I→X) (a : I→ℝ) := ∃ K:ℕ,∀ᶠ i in φ, ‖F i‖ ≤ ‖a i‖*‖T i‖^K
structure Bi (φ : Filter I) (T a b : I→ℝ) : Prop where
    up : Bill φ T a b
    down : Bill φ T b a
abbrev Cheap [Norm X] (φ : Filter I) (T : I→ℝ) (F : I→X) := Bill φ T F (fun _=>1)
abbrev Coins (φ : Filter I) (T a : I→ℝ) := Bi φ T a (fun _=>1)
variable {φ : Filter I}{φ':Filter J}{T a b c u v : I→ℝ}{F F' : I→X} {G : I→Y}{H:I→ Z}
namespace Bill
section
variable [Norm X](h:Bill φ T F a)
include h
lemma congr (hx:F=ᶠ[φ] F')(hA:a=ᶠ[φ] b) : Bill φ T F' b := by
    obtain ⟨K,h⟩:=h; exact ⟨K, (hx.and (hA.and h)).mono fun _ hp=> hp.1 ▸ hp.2.1 ▸ hp.2.2⟩
lemma norm_le [Norm Y] (hx:∀ᶠ i in φ, ‖G i‖≤ ‖F i‖) : Bill φ T G a:= by obtain ⟨K,h⟩:= h; exact ⟨K,(hx.and h).mono fun _ hi=> hi.1.trans hi.2⟩
lemma slack (hT:Tendsto T φ atTop) : ∀ᶠ K:ℕ in atTop,∀ᶠ i in φ, ‖F i‖ ≤ ‖a i‖*‖T i‖^K:=by
    obtain ⟨k,H⟩:= h; filter_upwards [eventually_ge_atTop k] with K hK; filter_upwards [H,hT.eventually_ge_atTop 1] with i hi hp
    exact hi.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (hp.trans (Real.le_norm_self _)) hK) (norm_nonneg _))
lemma of_tendsto {k : J→ I} (hk:Tendsto k φ' φ) : Bill φ' (T ∘ k) (F ∘ k) (a ∘ k):= by obtain ⟨K,H⟩:= h; exact ⟨K,hk.eventually H⟩
lemma mono (hx:∀ᶠ i in φ, ‖a i‖≤ ‖b i‖) : Bill φ T F b := by
    obtain ⟨K,h⟩:=h; exact ⟨K,(h.and hx).mono fun i ⟨hi,hh⟩=> hi.trans (mul_le_mul_of_nonneg_right hh (pow_nonneg (norm_nonneg _) _))⟩
lemma trans (hx: Bill φ T a b) : Bill φ T F b:= by
    obtain ⟨k,h⟩:=h; obtain ⟨j,H⟩:=hx; refine ⟨j+k,?_⟩; filter_upwards [h,H] with i hi hh
    rw [pow_add, ← mul_assoc]; exact hi.trans (mul_le_mul_of_nonneg_right hh (pow_nonneg (norm_nonneg _) _))
lemma enlarge (hT: Bill φ u T (fun _=>1)) : Bill φ u F a:=by
    obtain ⟨k,h⟩:=h; obtain ⟨j,H⟩:=hT; refine ⟨j*k,?_⟩; filter_upwards [h,H] with i hi hh
    rw [pow_mul]; rw [norm_one,one_mul] at hh; exact hi.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hh _) (norm_nonneg _))
omit h in
lemma made (hx:∀ᶠ i in φ, ‖F i‖≤ ‖a i‖): Bill φ T F a:= ⟨0,hx.mono fun i hi=>by simpa only [pow_zero,mul_one] using hi⟩
end
lemma same (φ : Filter I) (T a : I→ℝ) : Bill φ T a a:= made (Eventually.of_forall fun _=>le_rfl)
lemma const [Norm X] (x : X) (hT:Tendsto T φ atTop) : Cheap φ T (fun _=>x):= by refine ⟨1,?_⟩; filter_upwards [hT.eventually_ge_atTop ‖x‖] with i hi; rw [norm_one,pow_one,one_mul]; exact hi.trans (Real.le_norm_self _)
lemma mul_bill [Norm X][SeminormedAddGroup Y][Norm Z] (h:Bill φ T F a)(hx: Bill φ T G b)(hh:∀ᶠ i in φ, ‖H i‖≤ ‖G i‖*‖F i‖) : Bill φ T H (fun i=> b i*a i) := by
    obtain ⟨k,h⟩:= h; obtain ⟨j,hx⟩:= hx; refine ⟨k+j,?_⟩; filter_upwards [hh,h,hx] with i hq hs ht
    rw [norm_mul,pow_add]; apply hq.trans ((mul_le_mul_of_nonneg_left hs (norm_nonneg _)).trans _); refine le_trans (mul_le_mul_of_nonneg_right ht (mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _))) (le_of_eq ?_); ring
lemma mul [SeminormedRing X] (h:Bill φ T F a)(hx: Bill φ T F' b): Bill φ T (fun i=> F i*F' i) (fun i=> a i*b i) := hx.mul_bill h (Eventually.of_forall fun _=> norm_mul_le ..)
lemma smul [NormedField X][SeminormedAddCommGroup Y][NormedSpace X Y] (h:Bill φ T F a)(hx: Bill φ T G b): Bill φ T (fun i=>F i • G i) (fun i=> a i*b i):= hx.mul_bill h (Eventually.of_forall fun _=> norm_smul_le ..)
lemma add [SeminormedAddGroup X] (h:Bill φ T F a)(hx: Bill φ T F' a)(hT:Tendsto T φ atTop): Bill φ T (fun i=>F i+F' i) a:= by
    obtain ⟨K,hq,hv⟩:= ((h.slack hT).and (hx.slack hT)).exists; refine ⟨K+1,?_⟩; filter_upwards [hq,hv,hT.eventually_ge_atTop 2] with i hi hk hT
    rw [pow_succ, ←mul_assoc]; refine (norm_add_le ..).trans ((add_le_add hi hk).trans ?_); rw [←mul_two]; exact mul_le_mul_of_nonneg_left (hT.trans (Real.le_norm_self _)) (mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _))
lemma sub [SeminormedAddGroup X] (h:Bill φ T F a)(hx:Bill φ T F' a)(hT:Tendsto T φ atTop): Bill φ T (fun i=>F i-F' i) a:= by
    simp_rw [sub_eq_add_neg]; apply h.add _ hT; exact hx.norm_le (by simp)
lemma inverse (h : Bill φ T a b) (hx:∀ᶠ i in φ, a i≠0) : Bill φ T (fun i=>(b i)⁻¹) (fun i=>(a i)⁻¹):= by
    obtain ⟨K,h⟩:=h; refine ⟨K,?_⟩; filter_upwards [h,hx] with i hi hh; by_cases ht:b i=0
    · rw [ht,inv_zero,norm_zero]; positivity
    rw [norm_inv,norm_inv,←div_eq_inv_mul]; apply (inv_le_iff_one_le_mul₀ (by exact norm_pos_iff.mpr ht)).mpr
    rw [mul_comm,← mul_div_assoc, one_le_div (norm_pos_iff.mpr hh)]; exact hi
lemma power [SeminormedRing X] (hT:Tendsto T φ atTop)(n:ℕ)(h:Bill φ T F a) : Bill φ T (fun i=>(F i)^n) (fun i=>(a i)^n):=by
    induction n with
    | zero=> simpa only [pow_zero] using! Bill.const (1:X) hT
    | succ n ih=> simpa only [pow_succ] using ih.mul h
lemma zero [SeminormedAddGroup X] : Bill φ T (fun _=>(0:X)) a:= made (by filter_upwards with i; simp)
lemma sum [SeminormedAddCommGroup X] {s:Finset J} (f:J→ I→ X) (hT:Tendsto T φ atTop)(h:∀ i∈s,Bill φ T (f i) a) : Bill φ T (fun i=>∑ j∈s,f j i) a:=by
    classical
    induction s using Finset.induction with
    | empty=> simpa only [Finset.sum_empty] using (zero (X:=X))
    | insert i s hi ih=> simpa only [Finset.sum_insert hi] using (h i (Finset.mem_insert_self ..)).add (ih fun j hj=> h j (Finset.mem_insert_of_mem hj)) hT
lemma prod [SeminormedCommRing X] {s:Finset J}{f:J→ I→ X}{a:J→ I→ℝ} (hT:Tendsto T φ atTop)(h:∀ i∈s,Bill φ T (f i) (a i)) : Bill φ T (fun i=>∏ j∈s,f j i) (fun i=> ∏ j∈s,a j i):= by
    classical
    induction s using Finset.induction with
    | empty=> simpa only [Finset.prod_empty] using (Bill.const (1:X) hT)
    | insert i s hi ih=> simpa only [Finset.prod_insert hi] using (h i (Finset.mem_insert_self ..)).mul (ih fun j hj=> h j (Finset.mem_insert_of_mem hj))
end Bill
namespace Bi
lemma refl (φ : Filter I) (T a : I→ℝ): Bi φ T a a:= ⟨Bill.same .., Bill.same ..⟩
lemma symm (h: Bi φ T a b): Bi φ T b a:= ⟨h.down,h.up⟩
lemma trans (h:Bi φ T a b)(hp:Bi φ T b c): Bi φ T a c:= ⟨h.up.trans hp.up,hp.down.trans h.down⟩
lemma congr (h:Bi φ T a b)(he:a=ᶠ[φ] u)(hh:b=ᶠ[φ] v) : Bi φ T u v:= ⟨h.up.congr he hh,h.down.congr hh he⟩
lemma mul (h:Bi φ T a b)(hp:Bi φ T u v): Bi φ T (fun i=>a i*u i) (fun i=>b i*v i):= ⟨h.up.mul hp.up,h.down.mul hp.down⟩
lemma power (h:Bi φ T a b)(hT:Tendsto T φ atTop)(n:ℕ): Bi φ T (fun i=>(a i)^n) (fun i=>(b i)^n):= ⟨h.up.power hT n,h.down.power hT n⟩
lemma inv (h:Bi φ T a b)(hp:∀ᶠ i in φ, b i≠0) : Bi φ T (fun i=>(a i)⁻¹) (fun i=>(b i)⁻¹):= by
   refine ⟨h.down.inverse hp,h.up.inverse ?_⟩; obtain ⟨k,he⟩:= h.down; filter_upwards [he,hp] with i hi hh; contrapose! hh; simpa only [hh,norm_zero,zero_mul,norm_le_zero_iff] using hi
lemma const (c:ℝ) (hc:c≠0) (hT:Tendsto T φ atTop): Coins φ T (fun _=>c):= by
   have he:=Bill.const c⁻¹ hT; refine ⟨Bill.const _ hT,?_ ⟩; simpa using he.inverse (by simp [hc])
lemma prod {s:Finset J}{f g:J→ I→ℝ} (hT:Tendsto T φ atTop)(h:∀ i∈s,Bi φ T (f i) (g i)) : Bi φ T (fun i=>∏ j∈s,f j i) (fun i=>∏ j∈s,g j i):=
   ⟨Bill.prod hT (fun i hi=> (h i hi).up),Bill.prod hT (fun i hi=> (h i hi).down)⟩
lemma of_tendsto {k : J→ I} (h:Bi φ T a b) (hk:Tendsto k φ' φ) : Bi φ' (T ∘ k) (a ∘ k) (b ∘ k) :=⟨h.up.of_tendsto hk,h.down.of_tendsto hk⟩
end Bi
namespace Cheap
lemma of_bound [Norm X] (k:ℕ) (h:∀ᶠ i in φ,‖F i‖ ≤ ‖T i‖^k): Cheap φ T F:= ⟨k,by simpa using h⟩
lemma id (φ:Filter I)(T:I→ℝ): Cheap φ T T:= of_bound 1 (by simp)
lemma mul [SeminormedRing X] (h:Cheap φ T F)(hx:Cheap φ T F') : Cheap φ T (fun i=> F i*F' i):= by simpa using Bill.mul h hx
lemma div (h:Cheap φ T a)(hx:Coins φ T b): Cheap φ T (fun i=>a i/b i):= by have hp := Bill.mul h (hx.inv (by simp)).up; simpa [div_eq_mul_inv] using hp
lemma times [SeminormedRing X] (h:Cheap φ T F)(hx: Bill φ T F' a) : Bill φ T (fun i=>F i*F' i) a:= by simpa using Bill.mul h hx
lemma power [SeminormedRing X] (h:Cheap φ T F)(hT:Tendsto T φ atTop)(n:ℕ): Cheap φ T (fun i=>(F i)^n):= by simpa using (Bill.power hT n h)
end Cheap
namespace Coins
lemma mul (h:Coins φ T a)(hx:Coins φ T b): Coins φ T (fun i=>a i*b i):= by simpa using Bi.mul h hx
lemma power (h:Coins φ T a)(hT:Tendsto T φ atTop)(n:ℕ): Coins φ T (fun i=>(a i)^n) := by simpa using Bi.power h hT n
lemma inv (h:Coins φ T a): Coins φ T (fun i=>(a i)⁻¹):= by simpa using Bi.inv h (by simp)
lemma div (h:Coins φ T a)(hx:Coins φ T b): Coins φ T (fun i=>a i / b i) := by simpa only [div_eq_mul_inv] using Coins.mul h hx.inv
lemma by_le (h:Cheap φ T a)(hx:∀ᶠ i in φ,1≤ ‖a i‖): Coins φ T a:= ⟨h,Bill.made (by simpa using hx)⟩
end Coins
lemma flash (hT:Tendsto T φ atTop): RateIs φ T T 0:= by
   refine ⟨hT.eventually_gt_atTop _, ?_⟩; simpa [Function.comp_def] using ((Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hT)
lemma rapid (hT:Tendsto T φ atTop) {x:ℝ}[SeminormedAddGroup X](hp:Bill φ T F a)(hx:RateLE φ T a x) : RateLE φ T F x:= by
   obtain ⟨k,H⟩:= hp; refine (((hx.norm).mul ((flash hT|>.pays hT|>.norm).pow k hT)).mono (by simp)).of_norm_le H
lemma known (hT:Tendsto T φ atTop) {x:ℝ}(hp:Bi φ T b a)(hx:RateIs φ T a x)(hb:∀ᶠ i in φ,0 < b i) : RateIs φ T b x :=by
   have hu:= rapid hT hp.up (hx.pays hT)
   -- use sandwich Bi versions
   obtain ⟨k,h⟩:= hp.up; obtain ⟨k',h'⟩:=hp.down
   refine RateIs.of_sandwich (f:=fun i=>a i/(T i)^k') (f':=b) ?_ hu ?_ (by simp) hT
   · simpa only [mul_zero,sub_zero] using hx.div ((flash hT).power k')
   filter_upwards [h',hx.pos,hb,hT.eventually_gt_atTop 0] with i hi ha hb ht; rw [Real.norm_of_nonneg ha.le,Real.norm_of_nonneg hb.le,Real.norm_of_nonneg ht.le] at hi; exact (div_le_iff₀ (pow_pos ht _)).mpr hi
end YM.OPE.Loom
