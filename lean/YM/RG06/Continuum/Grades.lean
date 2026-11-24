import YM.RG06.Continuum.Raw
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Engineering and link/coupling grading in the external curvature prescription
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG06.Continuum
open MvPolynomial
open scoped BigOperators Classical
variable {G:Gauge}
section grade
variable {R : Type*} [CommRing R] {I J : Type*} {M : Type*} [AddCommMonoid M]
abbrev Tier (w:I→M)(n:M)(p:MvPolynomial I R):=MvPolynomial.IsWeightedHomogeneous w p n
namespace Tier
variable {w:I→M}{n:M}{p q:MvPolynomial I R} {a b:M}
protected lemma neg (h:Tier w n p):Tier w n (-p):=
  Submodule.neg_mem (MvPolynomial.weightedHomogeneousSubmodule R w n) h
-- from earlier apps with Σ engineering native
lemma bind (v:I→MvPolynomial J R) (t:J→M) (ht:∀ i,Tier t (w i) (v i))(h:Tier w n p):
    Tier t n (MvPolynomial.eval₂Hom MvPolynomial.C v p):=by
  generalize he:p=q at h ⊢
  -- no type variables change
  rw [q.as_sum,map_sum]
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro i hi
  rw [MvPolynomial.eval₂Hom_monomial]
  apply MvPolynomial.IsWeightedHomogeneous.C_mul
  have he:= h (MvPolynomial.mem_support_iff.mp hi)
  rw [←he,Finsupp.weight_apply]
  exact MvPolynomial.IsWeightedHomogeneous.prod _ _ _ (fun k _=>(ht k).pow _)
end Tier
end grade

namespace Raw


def size (i:Key G):ℕ:=i.chain.length+1
def measure (i:Key G):ℕ×ℕ:=(size i,1) -- order, potential slot count

-- Derivation raises size by one, preserves factors, a bound used on recursive external
-- dictionary before projecting by covariance.
private lemma derive_grade {M : Type*}[AddCommMonoid M](t:Key G→M) (δ:M)(he:∀ i j,t ⟨i.primary,j::i.chain,i.color⟩=t i+δ)(a:Axis):∀{p:Pol G}{n:M},Tier t n p→ Tier t (n+δ) (extending a p):=by
  intro p n hp
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero=> rw [map_zero]; exact isWeightedHomogeneous_zero ..
  | add p q hp hq hr hs=>rw [map_add]; exact hr.add hs
  | monomial u c hr=>
    subst n; unfold extending; rw [mkDerivation_monomial]
    apply Submodule.smul_mem (MvPolynomial.weightedHomogeneousSubmodule _ _ _)
    unfold Finsupp.sum; apply IsWeightedHomogeneous.sum
    intro i hi
    change Tier t ((Finsupp.weight t) u + δ) (MvPolynomial.monomial (u-Finsupp.single i 1) ((u i:ℕ):ℂ) * extendX a i)
    have hv:u-Finsupp.single i 1 + Finsupp.single i 1=u:=tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)))
    have hz:= congr_arg (Finsupp.weight t) hv; rw [map_add,Finsupp.weight_single] at hz; rw [← hz, one_smul,add_assoc]
    exact (isWeightedHomogeneous_monomial t _ _ rfl).mul (he i a ▸ isWeightedHomogeneous_X ..)

lemma primitive_grade (i:Axis)(a:G.ColorIndex):Tier measure (1,1) (primitive i a):=by exact isWeightedHomogeneous_X ℂ measure (⟨_,_,_⟩:Key G)
lemma kick_grade (i:Axis)(q:Vector G){n l:ℕ}(h:∀ a,Tier measure (n,l) (q a))(a:G.ColorIndex): Tier measure (n+1,l) (kick i q a):=by
  have he:=derive_grade (G:=G) measure (1,0) (fun u v=> by simp only [measure,size,List.length_cons,Prod.mk_add_mk,Nat.add_zero]) i (h a)
  exact he
lemma cross_grade (p q:Vector G){n k l j:ℕ}(hp:∀ a,Tier measure (n,l) (p a))(hq:∀ a,Tier measure (k,j) (q a))(a:G.ColorIndex):
    Tier measure (n+k,l+j) (cross p q a):=by
  unfold cross; apply IsWeightedHomogeneous.sum; intro b hb; apply IsWeightedHomogeneous.sum; intro f hf;
  exact ((hp b).C_mul _).mul (hq f)

-- Grade each bare perturbative coefficient separately without assuming the decomposition for the
-- common actual fields. λ counts all brackets, link B and its jets carry one potential leg each.
def fieldOrder (i j:Axis):ℕ→Vector G
 | 0 => kick i (primitive j)+ -kick j (primitive i)
 | 1 => cross (primitive i) (primitive j)
 | _+2 => 0

def haulOrder (i:Axis)(v:ℕ→Vector G):ℕ→Vector G
 | 0=>kick i (v 0)
 | k+1=> kick i (v (k+1)) + cross (primitive i) (v k)

def parse :{j:ℕ} → (Fin j→Axis) → (ℕ→Vector G)→ (ℕ→Vector G)
 | 0,_,v=>v
 | _+1,w,v=>haulOrder (w 0) (parse (Fin.tail w) v)

def coeffFrame {j:ℕ}(w:Fin j→Axis)(a b:Axis)(c:G.ColorIndex)(k:ℕ):Pol G:=
 MvPolynomial.C ((j.factorial:ℂ)⁻¹) * parse w (fieldOrder a b) k c

lemma field_ordered (i j:Axis)(k:ℕ)(a:G.ColorIndex): Tier measure (2,k+1) (fieldOrder (G:=G) i j k a):=by
  cases k with
  | zero=> exact (kick_grade i _ (primitive_grade j) _).add (Tier.neg (kick_grade j _ (primitive_grade i) _))
  | succ k=> cases k with
    | zero=> exact cross_grade _ _ (primitive_grade i) (primitive_grade j) _
    | succ l=> exact isWeightedHomogeneous_zero ..

lemma recorded {j:ℕ}(w:Fin j→Axis)(p:ℕ→Vector G){n l:ℕ}(hp:∀ k a,Tier measure (n,k+l) (p k a))(k:ℕ)(a:G.ColorIndex): Tier measure (n+j,k+l) (parse w p k a):=by
  induction j generalizing k a with
  | zero=> exact hp k a
  | succ j H=>
    rw [parse]; cases k
    next=>exact kick_grade _ _ (fun c=>H (Fin.tail w) _ c) _
    next k=>
     change Tier measure (n+j+1,k+1+l) (_+_)
     apply IsWeightedHomogeneous.add (kick_grade _ _ (fun c=>H (Fin.tail w) _ c) _)
     rw [show n+j+1= 1+(n+j) from add_comm .., show k+1+l=1+(k+l) by omega]
     exact cross_grade _ _ (primitive_grade _) (fun c=>H (Fin.tail w) _ c) _
lemma grade_frame {j:ℕ}(w:Fin j→Axis)(a b:Axis)(c:G.ColorIndex)(k:ℕ):Tier measure (j+2,k+1) (coeffFrame w a b c k):=by
  unfold coeffFrame; apply IsWeightedHomogeneous.C_mul
  rw [add_comm j]; exact recorded _ _ (fun _ _=>field_ordered ..) _ _
end Raw
end YM.RG06.Continuum

noncomputable section
namespace YM.RG06.Continuum.Raw
variable {G:Gauge}
open MvPolynomial
open scoped BigOperators Classical
lemma stops {j:ℕ}(w:Fin j→Axis)(a b:Axis)(k:ℕ)(h:j+2 ≤ k):parse w (fieldOrder (G:=G) a b) k=0:=by
  induction j generalizing k with
  | zero=> obtain ⟨l,hl⟩:= Nat.exists_eq_add_of_le h; rw [hl,Nat.add_comm 2]; rfl
  | succ j H=>
     cases k
     next=> omega
     next k=>
       rw [parse,haulOrder]
       rw [H _ (k+1) (by omega), H _ k (by omega)]
       ext1 i; simp [kick,cross]
lemma poly_fields (g:ℂ) (a b:Axis)(R:ℕ)(hR:1≤R):
    field (G:=G) g a b= ∑ k∈Finset.range (R+1),g^k • fieldOrder a b k:=by
  rw [Finset.sum_range_succ']; cases R
  next=> omega
  next R=> rw [Finset.sum_range_succ',Finset.sum_eq_zero (s:=Finset.range R) (by intro i _; simp [fieldOrder])]; unfold field; simp [fieldOrder,add_comm]

lemma cross_combo (g:ℂ) (a:Axis) (v:ℕ→Vector G)(s:Finset ℕ):
    cross (primitive a) (∑ k∈s,g^k • v k)=∑ k∈s,g^k • cross (primitive a) (v k):=by
  ext1 i
  simp only [cross,Finset.sum_apply, Pi.smul_apply,MvPolynomial.smul_eq_C_mul,Finset.smul_sum,Finset.mul_sum]
  rw [Finset.sum_comm (s:=s)]
  refine Finset.sum_congr rfl fun j _=> ?_; rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun c _=> Finset.sum_congr rfl fun k _=>by ring)
lemma kick_combo (g:ℂ)(a:Axis)(v:ℕ→Vector G)(s:Finset ℕ): kick a (∑ k∈s,g^k • v k)= ∑ k∈s,g^k • kick a (v k):=by ext1 i; simp [kick,map_sum]

/-- Finite expansion in the *same* g variable; no field equations imposed. -/
lemma poly_form (g:ℂ){j:ℕ}(w:Fin j→Axis)(a b:Axis)(R:ℕ)(hr:j+1 ≤ R) : sequence g w (field (G:=G) g a b) =∑ k∈Finset.range (R+1), g^k • parse w (fieldOrder a b) k:=by
  induction j with
  | zero=>exact poly_fields g a b R hr
  | succ j H=>
     let p:=parse (Fin.tail w) (fieldOrder (G:=G) a b)
     change haul g (w 0) (sequence g (Fin.tail w) (field g a b)) = ∑ k∈Finset.range (R+1),g^k • haulOrder (w 0) p k
     rw [haul,H (Fin.tail w) (by omega)]
     change kick (w 0) (∑ k∈Finset.range (R+1), g^k • p k) + g • cross (primitive (w 0)) (∑ k∈Finset.range (R+1), g^k • p k) = _
     rw [cross_combo,kick_combo]; conv_rhs=> rw [Finset.sum_range_succ']
     simp_rw [haulOrder, pow_zero, one_smul, smul_add,Finset.sum_add_distrib]
     -- split 1st LHS sum from zero and RHS-plus's last term from cross
     rw [Finset.sum_range_succ' (fun k=>g^k • kick (w 0) (p k)),Finset.sum_range_succ (fun k=> g^k • cross (primitive (w 0)) (p k)), show p R=0 from stops _ _ b _ (by omega)]
     have he:cross (G:=G) (primitive (w 0)) 0 = 0:=by ext1 i; simp [cross]
     rw [he,smul_zero,add_zero,pow_zero,one_smul]; simp only [Finset.smul_sum,smul_smul,pow_succ']; abel
lemma coeff_rebuild (g:ℂ){j:ℕ}(w:Fin j→Axis)(a b:Axis)(c:G.ColorIndex)(R:ℕ)(h:j+1 ≤ R):
    frame g w a b c= ∑ k∈Finset.range (R+1),g^k • coeffFrame w a b c k:=by
  unfold frame coeffFrame; rw [poly_form _ _ _ _ _ h, Finset.sum_apply,Finset.mul_sum];refine Finset.sum_congr rfl ?_
  simp [MvPolynomial.smul_eq_C_mul,mul_left_comm]
end YM.RG06.Continuum.Raw
