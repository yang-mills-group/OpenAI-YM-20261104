import YM.MSbar.Tree.Pairs
import YM.Next.RANK.GaussTags

/-!
# Separate a colliding cluster in leading Gaussian rule

Use the pair of symmetric covariance kernels and a cross, without any
condition on the within-cluster support or costs. Exact theorem (no
estimates in this file). No convention about an ordering of the
positions in grouping terms. Contact self pairs expected to be deleted
already by the given cov when using Wick Pol. Include utilities for
substituting and scaling stamps so prove tolerance estimates when cross
terms move. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.OPE
open Function Filter Set Next.Rank.Normal
open MvPolynomial
open Finsupp
open scoped Topology BigOperators Classical ContDiff
variable {A B V W ι : Type} (Q : Symmetric A) (R : Symmetric B)

def join (Q : Symmetric A) (R : Symmetric B) (U : A → B → ℂ) : Symmetric (A ⊕ B) where
  cov x y:= x.elim (fun i=> y.elim (Q.cov i) (U i)) (fun v=> y.elim (fun i=> U i v) (R.cov v))
  symm x y:=by cases x <;> cases y
               · exact Q.symm ..
               · rfl
               · rfl
               exact R.symm ..
variable (U : A→ B → ℂ)

def front : poly A →ₐ[ℂ] poly (A ⊕ B) := rename Sum.inl
def rear : poly B →ₐ[ℂ] poly (A ⊕ B) := rename Sum.inr

def mixed (p : poly A) (v : poly B) := blend (join Q R U) 0 (front p * rear v)

lemma mixed_add (p q : poly A) (e : poly B) : mixed Q R U (p+q) e=mixed Q R U p e+mixed Q R U q e:= by unfold mixed; rw [_root_.map_add,add_mul,_root_.map_add]
lemma mixed_smul (p : poly A) (a : ℂ) (e : poly B) : mixed Q R U (a • p) e=a • mixed Q R U p e:= by unfold mixed; rw [_root_.map_smul, smul_mul_assoc,_root_.map_smul]
def depend (e : poly B) : poly A →ₗ[ℂ] ℂ := ⟨⟨fun p=>mixed Q R U p e,fun p q=>mixed_add Q R U p q e⟩,fun a p=> mixed_smul Q R U p a e⟩

private lemma inj_at (f : V→W) : (exchange fun i=> single (f i) 1)=rename f:= (labelled f).symm
private lemma silent (Y : V→ℂ) (a : W→V) (p : poly W): slit Y (rename a p)=rename a (slit (Y ∘ a) p):= by
  rw [labelled,exchange_slit]; have he : reads (fun i=> single (a i) 1) Y=Y ∘ a:= by ext i; simp [reads]
  rw [he]
private lemma ignore_rear (e : poly B) (p : poly A) : milk (join Q 0 0) (front p* rear e)=front (milk Q p)* rear e:= by
  have H  : ∀ r : poly B, milk (join Q (R:=0) 0) (rear r)=rear r:= by
    intro r; unfold rear; rw [labelled,prepared]; rw [show scope (fun i:B=> single (Sum.inr i) 1) (join Q (0:Symmetric B) 0)=0 from ?_,froze];
    apply Symmetric.ext; funext i j; exact match_name _ _ _ _
  induction p using MvPolynomial.induction_on with
  | C a => rw [fine, front, rename_C,drink,H]
  | add p q hp hq=> simp only [_root_.map_add, add_mul,hp,hq]
  | mul_X p i hp =>
    let V:= join Q (0 : Symmetric B) 0
    have ht : (V.cov (.inl i)) ∘ Sum.inr=0 := rfl
    have hf : (V.cov (.inl i)) ∘ Sum.inl=Q.cov i:=rfl
    have h (i' : A) : front (X (R:=ℂ) i')=X (Sum.inl (β:=B) i'):=rename_X ..
    rw [mul_comm p, _root_.map_mul front,h,mul_assoc,feeds,hp, Derivation.leibniz,feeds]
    have ha := silent (V.cov (.inl i)) Sum.inr e; rw [ht,slit_zero,_root_.map_zero] at ha
    have hb := silent (V.cov (.inl i)) Sum.inl (milk Q p); rw [hf] at hb
    rw [show slit (V.cov (.inl i)) (rear e)=0 from ha,show slit (V.cov (.inl i)) (front (milk Q p))=_ from hb,smul_zero,zero_add]
    rw [_root_.map_add,_root_.map_mul front,h]; unfold front; ring

lemma splitCluster (p : poly A) (q : poly B) : mixed Q R U p q=mixed 0 R U (milk Q p) q:= by
  unfold mixed; rw [← ignore_rear, blend_components, blend_components, warms]
  rw [show (join (0:Symmetric A) R U)+(join Q (0:Symmetric B) 0)=join Q R U from ?_]
  symm; apply Symmetric.ext; funext i j
  change _=((join _ _ _).cov i j+(join _ _ _).cov i j); cases i <;> cases j <;> simp only [join,Sum.elim_inl, Sum.elim_inr]
  · exact (zero_add (Q.cov _ _)).symm
  · exact (add_zero (U _ _)).symm
  · exact (add_zero (U _ _)).symm
  exact (add_zero (R.cov _ _)).symm

variable (K : V → A →₀ ℂ)
def liftFront (K : V → A →₀ ℂ): V ⊕ B → A ⊕ B →₀ ℂ := Sum.elim (fun i=>mapDomain Sum.inl (K i)) (fun v=>single (.inr v) 1)
abbrev changed : V→B→ℂ := fun i=> linearCombination ℂ U (K i)
private lemma splice (p : poly V) : (front (B:=B)) (exchange (Z:=A) K p)=exchange (liftFront K) (front (B:=B) p):= by
  apply DFunLike.congr_fun (f:=(front (B:=B)).comp (exchange K)) (g:=(exchange (liftFront K)).comp (front (B:=B))) (x:=p)
  ext1 i; rw [AlgHom.comp_apply, AlgHom.comp_apply,front,front,rename_X, exchange_x,exchange_x]; change (rename (R:=ℂ) (Sum.inl (β:=B))).toLinearMap _= glyph (mapDomain _ _)
  rw [glyph,glyph,LinearMap.map_finsupp_linearCombination,linearCombination_mapDomain]; simp [Function.comp_def]
private lemma remains (p : poly B) : (rear (A:=A)) p=exchange (liftFront (B:=B) K) ((rear (A:=V)) p):= by
  suffices h : (rear (A:=A))=(exchange (liftFront (B:=B) K)).comp rear from DFunLike.congr_fun h p
  ext i; rw [AlgHom.comp_apply,rear,rear,rename_X,rename_X, exchange_x]; simp [liftFront,glyph]

lemma join_scope : scope (liftFront K) (join Q R U)=join (scope K Q) R (changed U K):= by
  apply Symmetric.ext; funext i j; cases i <;> cases j <;> simp only [scope, join, Sum.elim_inl,Sum.elim_inr]
  all_goals dsimp only [liftFront, Sum.elim_inl,Sum.elim_inr]
  case inr.inr i j =>
    rw [treats,linearCombination_single,one_smul,linearCombination_single,one_smul]; rfl
  case inr.inl i j => rw [treats_comm]; exact cross j i
  case inl.inr i j=> exact cross i j
  case inl.inl i j=>
    let P:=join Q R U
    unfold treats; rw [linearCombination_mapDomain,linearCombination_mapDomain]; congr! 2
    funext v; simp only [linearCombination_apply,Finsupp.sum, Finset.sum_apply, Pi.smul_apply,Function.comp_apply,Sum.elim_inl]
where cross (i : V) (a : B): treats (join Q R U) (mapDomain Sum.inl (K i)) (single (.inr a) 1)=changed U K i a:= by rw [treats, linearCombination_single, one_smul, linearCombination_mapDomain]; simp only [changed,linearCombination_apply,Finsupp.sum,Finset.sum_apply, Pi.smul_apply,Function.comp_apply, join,Sum.elim_inl,Sum.elim_inr]

lemma reads_nil (Q : A → B →₀ ℂ): reads Q (0:B→ℂ)=0:= by ext i; simp [reads]
lemma mixed_lift (p : poly V) (v : poly B) : mixed Q R U (exchange K p) v=mixed (scope K Q) R (changed U K) p v:=by
  unfold mixed; rw [splice]; nth_rw 1 [remains K v]; rw [← _root_.map_mul,wets,join_scope,reads_nil]

lemma scope_nil : scope K 0=0:= by apply Symmetric.ext; funext i j; change linearCombination ℂ (linearCombination ℂ (0:A→A→ℂ) _) _ =0; simp

lemma close (R1 Q1 : ι → Symmetric (A ⊕ B)) (p : poly (A ⊕ B)) (L : Filter ι) (g : ι → ℝ) (h : ∀ u v,Accords L g (fun t=>(R1 t).cov u v) (fun t=>(Q1 t).cov u v)) : Accords L g (fun t => blend (R1 t) 0 p) (fun t=>blend (Q1 t) 0 p):= Accords.blends h (fun _=>Accords.constants 0) p

lemma mixed_perturb {U W : ι → A → B →ℂ} (Q : Symmetric A)(R : Symmetric B) (L : Filter ι) (g : ι →ℝ) (p : poly A) (v : poly B) (h : ∀ x y,Accords L g (fun t=> U t x y) (fun t=> W t x y)) : Accords L g (fun t=> mixed Q R (U t) p v) (fun t=>mixed Q R (W t) p v):= by
  apply close; intro x y; cases x <;> cases y
  · exact Accords.constants _
  · exact h _ _
  · exact h _ _
  exact Accords.constants _
end YM.MSbar.OPE
