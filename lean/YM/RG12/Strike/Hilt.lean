import YM.RG12.Strike.Spear
/-!
# Exact resonance test: ONE leg from the integrated action at the mark

Prove line derivative on ANY radial annuli (not just calibrated differencing scales).
Rather than invoking the distribution across 0, use exact massless trace and dualize to
another harmonic tensor. Also proves the identity on ANY resonant polynomial families (no
harmonic restriction in this direction). Doesn't include finite normalization resonances,
consumed separately as common-homogeneous. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Strike
open Filter Function Set MeasureTheory Real Finset
open scoped Topology InnerProductSpace ContDiff ComplexConjugate BigOperators Classical
variable {w:R→ℂ}(hw:Dried w){n:ℕ}{P:Cells→ℂ}(hP:Rated n P)(v:Cells)
-- integral interchange. need line off-origin integrable times sun because compact radial support.
-- use `withered` to retain costs.
include hw
lemma sticky (v p:Cells): Integrable (fun x : R=>w x * barrage field p x *sun v x) :=
   weighted _ (withered hw (barrage field p) (fun y hy=> (vellum punct_open punct_field p y hy).continuousAt)) (sun_cont v)
abbrev chip (w:R→ℂ)(v p:Cells):ℂ:=∫ x:R,w x*barrage field p x * sun v x
lemma rated_tip (n:ℕ) : Rated n (chip w v):=by
  constructor
  · intro x y hp _; unfold chip
    have he(i:R) : w i * barrage field x i = w i * barrage field y i:=by
      by_cases h:i=0
      · cases h; simp [hw.near.eq_of_nhds]
      rw [regimen punct_open punct_field (show i∈puncture from h) hp]
    simp_rw [he]
  intro u _; unfold chip; rw [← integral_finsetSum _ (fun a _=> sticky hw _ _)]
  have he(x:R): (∑i:Axis4,w x*barrage field (i::i::u) x*sun v x)=0:=by
     by_cases h:x=0
     · subst x; simp [hw.near.eq_of_nhds]
     rw [← Finset.sum_mul,← Finset.mul_sum, vanes u x h, mul_zero, zero_mul]
  simp_rw [he]; simp
include hP
lemma vanish (he:v.length<n):∑ i:Strip n,P (List.ofFn i)*chip w v (List.ofFn i)=0:=by
   let C (Y:Stroke):= (dressed hw Y ({weight:=1,rate:=0,deck:=[]}:Stroke))
   let A(x:R):=w x*(black x ^ (n+1))⁻¹
   have ha: Round A:=by
      have hf:=dressed hw ({weight:=1,rate:=n+1,deck:=[]}:Stroke) ({weight:=1,rate:=0,deck:=[]}:Stroke); change Round (fun x=>_*_*(_^ (0:ℕ))⁻¹) at hf; simpa only [pow_zero,inv_one,mul_one] using! hf
   obtain ⟨c,h⟩:=shave ha n
   have hv := h P hP v he.le; rw [if_neg he.ne] at hv
   let U:=unionized P n
   have hb : (∫ x:R,w x*U x*sun v x)=0:=by
     rw [show (fun x:R=>w x*U x*sun v x)=(fun x=>coefficient n*(A x*fall (gauge n P) x*sun v x)) from ?_, integral_const_mul,hv,mul_zero]
     funext x; by_cases h:x=0
     · cases h; simp [A,hw.near.eq_of_nhds]
     unfold U;rw [pose n P hP x h];unfold A;ring
   have he(x):w x*U x*sun v x=∑i:Strip n,P (List.ofFn i)* (w x*barrage field (List.ofFn i) x*sun v x):=by
      unfold U unionized; rw [mul_sum,sum_mul]; apply sum_congr rfl;intro i _; ring
   unfold chip; simp_rw [← integral_const_mul]; rw [← integral_finsetSum,show (fun x=> ∑ i:Strip n,_) = (fun x=> w x*U x*sun v x) from funext (fun i=>(he i).symm)]; exact hb
   intro i _; exact (sticky hw _ _).const_mul _
-- dual harmonic moment. arbitrary P. By completeness on the harmonic derivative slots,
-- every exact lower-degree contraction kernel charge vanishes. Also infinitesimal.
omit hw v in
lemma Rated.reflect : Rated n (conj ∘ P):=by
   constructor
   · intro _ _ he hl; exact congr_arg (starRingEnd ℂ) (hP.sym he hl)
   intro v hv; change (∑i:Axis4,conj (P _))=0; rw [← map_sum,hP.clean hv];exact map_zero _
omit hP in
theorem single (K:Cells)(hk:v.length < K.length) : chip w v K=0:=by
   let n:=K.length; let P:=chip w v; let f(p:Strip n):= P (List.ofFn p)
   have h:=rated_tip hw v n|>.reflect; have hL:= vanish hw h v hk
   have he:(∑ i:Strip n, (‖f i‖^2:ℝ))=0:=by
      change (∑ i:Strip n,conj (f i)*f i)=0 at hL
      simp_rw [← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq,←Complex.ofReal_sum] at hL -- check
      exact_mod_cast hL
   have hK : (‖f K.get‖^2:ℝ)=0:= (Finset.sum_eq_zero_iff_of_nonneg (fun i _=> sq_nonneg _)|>.mp he) _ (mem_univ _)
   have ht := norm_eq_zero.mp (sq_eq_zero_iff.mp hK)
   unfold f at ht;rw [List.ofFn_get] at ht;exact ht
-- harmonic line result purchases full lower-degree polynomial; V3 marks resonance here l=p+2
-- and polynomial tests can be arbitrary, no harmonic hypothesis in THAT label.
omit hP v in
theorem resonance (K:Cells){p:ℕ}(he:p+2= K.length)(T:Strip p→ℂ):
    (∫ x:R,w x*barrage field K x*fall T x)=0:=by
   simp_rw [fall,sun_ofFn,mul_sum,mul_left_comm (w _*_) (T _)]
   rw [integral_finsetSum _ (fun i _=> (sticky hw _ _).const_mul _)]; apply sum_eq_zero;intro i _;rw [integral_const_mul,show (∫ x:R,_) =chip w (List.ofFn i) K from rfl, Strike.single hw ..,mul_zero];simp only [List.length_ofFn];omega
end YM.RG12.Strike
