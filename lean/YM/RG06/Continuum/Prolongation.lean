import YM.RG06.Continuum.Position
import YM.RG06.Continuum.Coupling
import YM.RG06.Continuum.TurnActual
import YM.Next.MAXWELL.Simple

/-!
# Derivatives as fields (classical operator representatives)

There are two kinds of spatial derivatives in the contract. `W.Address` spells
*profile* derivatives at fixed horizon. Here instead take total LOCAL FIELD derivatives: they
prolong the horizon. This distinction matters even on separated support. There is a cleanly
defined differentiation also on the common classical quotient, consistent with actual SMOOTH
connection rendering. Don't infer a choice of composite operator in an interacting quantum
scheme or a matched T.Field d+1. Keep the unsymmetrized derivative lifts.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG06.Continuum
open MvPolynomial Labels Maxwell Analysis Pert.Bare
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}
namespace Form

def prepend (i:Axis)(x:Glyph G):Glyph G:=⟨x.order+1,Fin.cons i x.chain,x.faceL,x.faceR,x.color⟩
-- x.chain normalized /j! so (j+1) times the (j+1)-glyph for prefactor
-- connection change of frame not included; deterministic cancellation below for invariant p
def followX (i:Axis)(x:Glyph G):Form.Pol G:= MvPolynomial.C ((x.order+1:ℕ):ℂ)* X (prepend i x)
def follow (i:Axis):Derivation ℂ (Form.Pol G) (Form.Pol G):= mkDerivation ℂ (followX i)
def followT (i:Axis)(v:Tower G):Tower G:=fun j a b w=> ((j+1:ℕ):ℝ) • v (j+1) a b (Fin.cons i w)
def rotor (X:G.Color)(v:Tower G):Tower G:= fun j a b w=> G.ad X (v j a b w)
def rotorX (Y:G.Color)(x:Glyph G):Form.Pol G:=∑ i:G.ColorIndex, MvPolynomial.C (↑(G.ad Y (WilsonRules.baseColor G i) x.color):ℂ)*MvPolynomial.X {x with color:=i}

lemma flow (v:Tower G)(q:ℝ→Tower G)(x:ℝ)(H: q x=v)
    (Y:Glyph G→Form.Pol G)(hq:∀ k:Glyph G,HasDerivAt (fun t=> coords (q t) k) (applyTo v (Y k)) x)(p:Form.Pol G):
    HasDerivAt (fun t=> applyTo (q t) p) (applyTo v (mkDerivation ℂ Y p)) x:=by
  induction p using MvPolynomial.induction_on with
  | C c=>
    have he: mkDerivation ℂ Y (MvPolynomial.C c) = 0:=mkDerivationₗ_C ..
    simp only [he,map_zero,applyTo, MvPolynomial.aeval_C,Algebra.algebraMap_self,RingHom.id_apply]; exact hasDerivAt_const ..
  | add p z hp hz=> simp_rw [_root_.map_add]; exact hp.add hz
  | mul_X p k hp=>
    rw [Derivation.leibniz,smul_eq_mul,smul_eq_mul,_root_.map_add,_root_.map_mul,_root_.map_mul,mkDerivation_X,applyTo,MvPolynomial.aeval_X]
    have he:=hp.mul (hq k); simp only [H] at he; unfold applyTo at he; simp only [_root_.map_mul, MvPolynomial.aeval_X,applyTo];rw [add_comm,mul_comm (coords v k)];exact he

lemma rotor_value (Y:G.Color)(v:Tower G)(x:Glyph G):applyTo v (rotorX Y x)=coords (rotor Y v) x:=by
  unfold rotorX rotor coords applyTo
  simp only [ _root_.map_sum]; rw [← WilsonRules.base_expansion (v x.order x.faceL x.faceR x.chain)] -- rw inside vars? rewrites implicit? only RHS target but LHS contains v
  simp only [_root_.map_mul,MvPolynomial.aeval_C,MvPolynomial.aeval_X,_root_.map_smul,WithLp.ofLp_sum,PiLp.smul_apply, smul_eq_mul,Finset.sum_apply,_root_.map_sum,Complex.ofReal_sum,Complex.ofReal_mul,Algebra.algebraMap_self,RingHom.id_apply,coords]; exact Finset.sum_congr rfl fun _ _=>mul_comm ..
lemma follow_value (i:Axis)(v:Tower G)(x:Glyph G):applyTo v (followX i x)=coords (followT i v) x:=by
  simp [followX,followT,coords,applyTo, prepend]

/-- infinitesimal global-color invariance in ALL independent slots (including ghost-free off
shell insertions in arbitrary tensor ports) -/
lemma killed_color {p:Form.Pol G} (h:p∈invariant G)(Y:G.Color): mkDerivation ℂ (rotorX Y) p=0:= by
  apply redundant_ext
  intro v
  have hi (w : Tower G)(u:G.El):applyTo (spin u w) p=applyTo w p:=h w u
  let r(t:ℝ):=spin (G.lieExp (t • Y)) v
  have he:=flow v r 0 (funext (fun j=> by
    unfold r spin; simp [G.adjoint_one])) (rotorX Y) (p:=p) (fun k=> ?_)
  · simp_rw [r,hi] at he
    exact (he.unique (hasDerivAt_const ..)).trans (map_zero _).symm
  let L:G.Color→L[ℝ]ℂ:=Complex.ofRealCLM ∘L EuclideanSpace.proj k.color
  rw [rotor_value]
  exact L.hasFDerivAt.comp_hasDerivAt (0:ℝ) (Free.adj_has Y (v k.order k.faceL k.faceR k.chain))

lemma follows_g {p:Form.Pol G}(h:p∈invariant G)(i:Axis):follow i p∈invariant G :=by
  intro q u
  have he(v:Tower G):HasDerivAt (fun t:ℝ=> applyTo (v+t • followT i v) p) (applyTo v (follow i p)) 0:= flow _ _ _ (by simp) (followX i) (fun a=>by
    let L:G.Color→L[ℝ]ℂ:=Complex.ofRealCLM ∘L EuclideanSpace.proj a.color
    rw [follow_value]; unfold coords
    exact L.hasFDerivAt.comp_hasDerivAt (0:ℝ) (by
       simpa only [id_eq,one_smul] using! (((hasDerivAt_id (0:ℝ)).smul_const (followT i v a.order a.faceL a.faceR a.chain)).const_add (v a.order a.faceL a.faceR a.chain))) ) p
  apply (he (spin u q)).unique
  have hc(t:ℝ):spin u q+t • followT i (spin u q)=spin u (q+t • followT i q):=by
    funext j a b v; simp [spin,followT]
  simp_rw [hc, show ∀ (v:Tower G),applyTo (spin u v) p=applyTo v p from fun v=>h v u]; exact he q

lemma follow_grade (i:Axis) {M:Type*}[AddCommMonoid M](σ:Glyph G→M)(e:M)
    (he:∀ k:Glyph G, σ (prepend i k)=σ k+e){p:Form.Pol G}{n:M}(h:Tier σ n p): Tier σ (n+e) (follow i p) :=by
  induction h using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero=> rw [map_zero]; exact isWeightedHomogeneous_zero ..
  | add p q _ _ hr hs=>rw [map_add]; exact hr.add hs
  | monomial u c hr=>
    subst n; unfold follow; rw [mkDerivation_monomial]
    apply Submodule.smul_mem (MvPolynomial.weightedHomogeneousSubmodule _ _ _)
    unfold Finsupp.sum; apply IsWeightedHomogeneous.sum
    intro k hk
    change IsWeightedHomogeneous _ (((monomial (u - Finsupp.single k 1)) ((u k:ℕ):ℂ)) * followX i k) _
    have hv:u-Finsupp.single k 1 + Finsupp.single k 1=u:=tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hk)))
    have hz:= congr_arg (Finsupp.weight σ) hv; rw [map_add,Finsupp.weight_single] at hz; rw [← hz, one_smul,add_assoc]
    exact (isWeightedHomogeneous_monomial σ _ _ rfl).mul (he k ▸ ((isWeightedHomogeneous_X ℂ σ (prepend i k)).C_mul ((k.order+1:ℕ):ℂ)))

lemma follow_within (i:Axis){p:Form.Pol G}{d:ℕ}(hp:p∈limited G d):follow i p∈ limited G (d+1):=by
  rw [p.as_sum,map_sum]; apply Submodule.sum_mem; intro b hb; apply (MvPolynomial.mem_restrictSupport_iff ℂ).mpr
  intro a ha
  have he:=follow_grade i weight 1 (fun _=>rfl) (MvPolynomial.isWeightedHomogeneous_monomial weight b (MvPolynomial.coeff b p) rfl (m:=Finsupp.weight _ b)) (MvPolynomial.mem_support_iff.mp ha)
  change (Finsupp.weight weight) a ≤ d+1; rw [he]; exact Nat.add_le_add_right ((MvPolynomial.mem_restrictSupport_iff ℂ).mp hp hb) _

def exactD (i:Axis){d:ℕ}: Field G d →ₗ[ℂ] Field G (d+1):=
   ((follow i).toLinearMap.comp (localSpace G d).subtype).codRestrict (localSpace G (d+1))
    fun p=>⟨follow_within i p.property.1,follows_g p.property.2 i⟩

-- Covariant scalar identity for genuine smooth connections inserted into `Form` ports
-- Proof enforces missing g factor and factorial shift by comparing derivative in gauge orbit
private lemma prepend_cov (g:ℝ)(A:Connection G)(i:Axis){j:ℕ}(w:Fin j→Axis)(a b:Axis):
  par i (covJet g A w a b)= ((j+1:ℕ):ℝ) • (covJet g A (Fin.cons i w) a b) - fun x=> G.ad (g • A i x) (covJet g A w a b x):=by
  let f:=nablas g A w (curvature g A a b)
  have he: par i (fun x=> ((j.factorial:ℝ)⁻¹) • f x)=(j.factorial:ℝ)⁻¹ • par i f:=by
    -- scalar not singular, no smooth required
    funext x; unfold par D; rw [show (fun x=> ((j.factorial:ℝ)⁻¹) • f x)=((j.factorial:ℝ)⁻¹) • f from rfl,fderiv_const_smul_field] -- name?
    rfl
  unfold covJet;change par i (fun x=> ((j.factorial:ℝ)⁻¹) • f x)= _
  rw [he,nablas]; funext x
  simp only [covariant,Fin.cons_zero,Fin.tail_cons, Pi.smul_apply,Pi.add_apply,Pi.sub_apply, map_smul,LinearMap.smul_apply,smul_add,smul_smul,bracket]
  rw [Nat.factorial_succ]; push_cast
  have hr:((j:ℝ)+1)* ((((j:ℝ)+1)* j.factorial)⁻¹)= (j.factorial:ℝ)⁻¹:=by field_simp
  change _= (((j:ℝ)+1) * ((((j:ℝ)+1)* j.factorial)⁻¹)) • par i f x + (((j:ℝ)+1) * (((((j:ℝ)+1)* j.factorial)⁻¹) * g)) • G.ad (A i x) (f x) - _
  rw [← mul_assoc,hr]; simp only [f];abel

private def sail (i:Axis)(x:E4)(t:ℝ) :E4:= t • basis i+x
lemma par_sail {V:Type*}[NormedAddCommGroup V][NormedSpace ℝ V](i:Axis){f:E4→V}(x:E4)(h:Good f):
    HasDerivAt (fun t=> f (sail i x t)) (par i f x) 0:=by
  have hv:HasDerivAt (sail i x) (basis i) (0:ℝ):=by simpa only [sail,id_eq,one_smul] using! (((hasDerivAt_id (0:ℝ)).smul_const (basis i)).add_const x)
  unfold par D; refine ((show HasFDerivAt f (fderiv ℝ f x) (sail i x 0) from by rw [sail,zero_smul,zero_add]; exact (h.germ x).hasFDerivAt).comp_hasDerivAt 0 hv)

lemma actual_smooth (g:ℝ)(A:Connection G)(h:Smooth A)(p:Form.Pol G):Good (fun x=> actual g A x p):=by simp_rw [← tree_receipt p g A h]; exact Raw.read_diff A h _

lemma receives (g:ℝ)(A:Connection G)(h:Smooth A){p: Form.Pol G}(hp:p∈invariant G)(i:Axis): par i (fun y=> actual g A y p) = fun y=> actual g A y (follow i p):=by
  funext y
  let Y:=g • A i y
  let F:=followX i (G:=G)-rotorX Y
  let v:= evaluate g A y
  change par i (fun x=> applyTo (evaluate g A x) p) y=applyTo v (follow i p)
  apply (par_sail i (f:=fun x=> applyTo (evaluate g A x) p) y (actual_smooth g A h p)).unique
  have HE:=flow v (fun t=>evaluate g A (sail i y t)) 0 (by simp [v,sail]) F (p:=p) (fun a=>?_)
  · have HH : mkDerivation ℂ F p=follow i p - mkDerivation ℂ (rotorX Y) p:=by
       unfold F follow; change mkDerivationEquiv ℂ _ p = mkDerivationEquiv ℂ _ p - mkDerivationEquiv ℂ _ p
       rw [_root_.map_sub];rfl
    rw [HH,killed_color hp,sub_zero] at HE; exact HE
  unfold F; rw [Pi.sub_apply,map_sub,follow_value,rotor_value]; unfold Y v followT rotor Form.evaluate coords
  let L:G.Color→L[ℝ]ℂ:=Complex.ofRealCLM ∘L EuclideanSpace.proj a.color
  have hs:Good (fun x=>covJet g A a.chain a.faceL a.faceR x):=by
      unfold covJet; exact ContDiff.const_smul _ (Smooth.higherCov g A h _ _ (Smooth.F g A h _ _))
  have he:= L.hasFDerivAt.comp_hasDerivAt (0:ℝ) (par_sail i y hs)
  change HasDerivAt (fun t=>L (covJet g A a.chain a.faceL a.faceR (sail i y t))) (L (((a.order+1:ℕ):ℝ) • covJet g A (Fin.cons i a.chain) a.faceL a.faceR y)- L (G.ad _ _)) _
  change HasDerivAt _ (L (par i (covJet g A a.chain a.faceL a.faceR) _)) _ at he; rw [prepend_cov] at he; exact (by rw [← map_sub]; exact he)

def prolonged (g:ℝ)(i:Axis){d:ℕ}:Label G d →ₗ[ℂ] Label G (d+1):=
   bridge g ∘ₗ exactD i ∘ₗ asGlyph
lemma receipts (g:ℝ)(A:Connection G)(h:Smooth A){d:ℕ}(p:Label G d)(i:Axis):
   par i (fun x=> submit g A x p)=fun x=>submit g A x (prolonged g i p):=by
   change par i (fun x=> actual g A x (asGlyph p).val)=_
   rw [receives g A h (asGlyph p).property.2]; funext y; exact respects g A h (exactD i (asGlyph p)) y
lemma nearby (g:ℝ){d:ℕ}(p:Field G d)(i:Axis):
    prolonged g i (bridge g p)=bridge g (exactD i p):=by
   refine submit_ext g 0 (fun A h=>?_)
   rw [← respects g A h (exactD i p)]
   have hh:=congr_fun (receipts g A h (bridge g p) i) 0
   simp_rw [← hh, ← respects g A h p, receives g A h p.property.2];rfl

-- Pinned O4 conventions (derivative on rotated operator & index, not argument
-- x implicitly rotated). Shows compatibility on the observable quotient by smooth fields.
open Extra.FD
lemma submitO (g:ℝ)(s:Ortho)(A:Connection G)(h:Smooth A){d:ℕ}(p:Label G d):
    (fun z=> submit g A z (Labels.tensor s p))=fun z=> submit g (O.position s⁻¹ A) (Ortho.move s⁻¹ z) p:=by
   funext z; change actual g A z (asGlyph (Labels.tensor s p)).val= _
   rw [← turn_lift]; change actual g A z (depart s (asGlyph p).val)=actual g _ _ (asGlyph p).val
   simp_rw [actual,turned_labels,O.applies s⁻¹ g A h,inv_inv,mov_apply,Ortho.move_inv]
lemma prolonged_shift (g:ℝ)(s:Ortho){d:ℕ}(i:Axis)(p: Label G d):
    prolonged g i (Labels.tensor s p) = ∑ b:Axis,(↑(s.val i b):ℂ) • Labels.tensor s (prolonged g b p):=by
   refine submit_ext g 0 (fun A h=>?_)
   let B:=O.position s⁻¹ A
   have e:Smooth B:=O.whole s⁻¹ A h
   have he:=congr_fun (receipts g A h (Labels.tensor s p) i) 0
   rw [_root_.map_sum,← he]; rw [submitO]
   · let f(z:E4):=submit g B z p
     change par i (fun z=> f (mov s⁻¹ z)) 0= _
     have hf: Good f:=actual_smooth g B e _
     rw [show par i (fun z=>f (mov s⁻¹ z)) 0=∑ b:Axis,(s.val i b) • par b f (mov s⁻¹ 0) from mov_gradient s i (x:=0) (ContDiff.contDiffAt hf)]
     refine Finset.sum_congr rfl fun b _=>?_ ; rw [_root_.map_smul]
     change (s.val i b) • par b (fun x=>submit g B x p) _ = _;rw [receipts g B e]
     rw [show submit g A 0 (Labels.tensor s (prolonged g b p))= submit g B (mov s⁻¹ 0) (prolonged g b p) from congr_fun (submitO g s A h _) 0,Complex.real_smul]
     rfl
   exact h
lemma prolonged_real (g:ℝ){d:ℕ}(i:Axis)(p: Label G d):
    prolonged g i (Labels.realBar p)=Labels.realBar (prolonged g i p):=by
   refine submit_ext g 0 (fun A h=>?_)
   have he{e:ℕ}(q:Label G e)(x:E4): submit g A x (Labels.realBar q)= star (submit g A x q):=by
     change applyTo _ (asGlyph _).val = star (applyTo _ (asGlyph _).val); rw [← real_lift]; exact real_script ..
   simp only [he, ← congr_fun (receipts g A h p i) 0,← congr_fun (receipts g A h (Labels.realBar p) i) 0]
   exact congr_fun (par_linear ((starL ℝ (A:=ℂ)).toContinuousLinearMap) (f:=fun x=>submit g A x p) (actual_smooth g A h _) i) 0
lemma prolonged_across (g:ℝ){d e:ℕ}(h:d≤e)(i:Axis)(p: Label G d):
    prolonged g i (Labels.raiseLabel G h p) = Labels.raiseLabel G (Nat.succ_le_succ h) (prolonged g i p):=rfl

/-- All total local derivative demands prolong filtration; keep these slots for contact matching
and OPE, no dropped address derivative or coincidence interpretation. -/
def exactWords (w:List Axis){d:ℕ}:Field G d→ₗ[ℂ] Field G (d+w.length):= match w with
 | []=> LinearMap.id
 | i::w=>exactD i ∘ₗ exactWords w

def submitWords (g:ℝ)(w:List Axis){d:ℕ}:Label G d→ₗ[ℂ]Label G (d+w.length):=bridge g ∘ₗ exactWords w ∘ₗ asGlyph
lemma word_step (g:ℝ)(i:Axis)(w:List Axis){d:ℕ}(p:Label G d):submitWords g (i::w) p=prolonged g i (submitWords g w p):=(nearby g (exactWords (d:=d) w (asGlyph p)) i).symm
lemma applied (g:ℝ)(A:Connection G)(h:Smooth A){d:ℕ}(p:Label G d)(w:List Axis):
    derivative w (fun y=> submit g A y p)=fun y=> submit g A y (submitWords g w p):=by
   induction w with
   | nil=> rw [derivative]; rw [show submitWords (G:=G) (d:=d) g [] p=(p:Label G d) from retract p g]
   | cons i w H=> rw [derivative,H,receipts g A h,word_step]
lemma permutation (g:ℝ){d:ℕ}(p:Label G d)(w u:List Axis)(he:w.Perm u):
    Labels.raiseLabel G (Nat.add_le_add_left (List.Perm.length_eq he).le d) (submitWords g w p)=submitWords g u p:=by
   refine submit_ext g 0 fun A h=>?_; rw [submit_includes]
   rw [← congr_fun (applied g A h p w) 0, ← congr_fun (applied g A h p u) 0,permutes w u he (show Good (fun y=>submit g A y p) from actual_smooth g A h _)] -- elaboration implicit f

lemma differentiated_grade {d:ℕ}(p:Label G d){n l:ℕ}(h:p∈Labels.Grade (n,l))(i:Axis): Tier Form.bidegree (n+1,l) (exactD (G:=G) i (asGlyph p)).val:= follow_grade i Form.bidegree (1,0) (fun _=>rfl) (homogeneous p _ h)
lemma words_homo {d:ℕ}(p:Label G d){n l:ℕ}(h:p∈Labels.Grade (n,l))(w:List Axis) : Tier Form.bidegree (n+w.length,l) (exactWords w (asGlyph p)).val:=by
   induction w with
   | nil=> exact homogeneous p _ h
   | cons a w H=>exact follow_grade _ _ ((1,0):ℕ×ℕ) (fun _=>rfl) H
-- Independent all-order common-operator polynomial dictionary for integrated density tasks
-- (Exact coefficients for UNINTEGRATED total derivatives; no claim about integration contact terms.)
lemma exact_progress (g:ℝ){d:ℕ}(p:Label G d){n l:ℕ}(h:p∈Labels.Grade (n,l))(w:List Axis)(R:ℕ)(hR:n+w.length-l≤R):
   (submitWords g w p).val=∑ k∈Finset.range (R+1),(g:ℂ)^k • layer k (exactWords w (asGlyph p)).val:= layered (words_homo p h w) (↑g) hR
end Form
end YM.RG06.Continuum
