import YM.RG06.Continuum.RadialRead

/-!
# Covariant continuum alphabet, invariant local polynomials, *radial* comparison

Introduce independent D^n F glyphs with ordered derivatives and curvature pair orientations (no
antisymmetry or Bianchi in the alphabet), normalized /n! and color in the same physical skew
basis. Give explicit maps from this enlarged book to the bare connection-jet prescription and
the common polynomial labels, and a right inverse with exactly the announced slot degree. Do not
identify or annihilate operators modulo total derivatives. The equivalence with identities on
**all** smooth connections (not just polynomial radial samples) requires GaugeOrbit. And at no
point is a classical equivalence asserted to hold as an interacting physical equivalence without
contact/representation terms. These are 4D *address-book/lift and projection* statements, not an
evanescent projection in dimensional subtraction.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG06.Continuum
namespace Form
open Labels Maxwell Lattice MvPolynomial Function Pert.Bare
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical InnerProductSpace
variable {G:Gauge}
structure Glyph (G:Gauge) where
  order:ℕ
  chain:Fin order→Axis
  faceL:Axis
  faceR:Axis
  color:G.ColorIndex
  deriving DecidableEq
abbrev Pol (G:Gauge):=MvPolynomial (Glyph G) ℂ

/-- unconstrained curvature slots, `Response` recovered, ordered & normalized /j! -/
abbrev Tower (G:Gauge):=∀ j,Response G j

def coords (p:Tower G)(k:Glyph G):ℂ:= ↑(p k.order k.faceL k.faceR k.chain k.color)

def applyTo (p:Tower G) : Pol G→ₐ[ℂ]ℂ:= MvPolynomial.aeval (coords p)

def evaluate (g:ℝ)(A:Connection G)(x:E4) :Tower G:= fun _ i j w=> covJet g A w i j x

def encode (g:ℂ)(k:Glyph G):Raw.Pol G:= Raw.frame g k.chain k.faceL k.faceR k.color
def graph (g:ℂ):Pol G→+* Raw.Pol G:= eval₂Hom MvPolynomial.C (encode g)

def actual (g:ℝ)(A:Connection G)(x:E4)(q:Pol G):= applyTo (evaluate g A x) q
lemma tree_receipt (q:Pol G)(g:ℝ)(A:Connection G)(h:Smooth A)(x:E4):Raw.read A x (graph (↑g) q)=actual g A x q:=by
  unfold actual graph
  induction q using MvPolynomial.induction_on with
  | C c=> simp [Raw.read,applyTo]
  | add q u hp hr=> simp only [_root_.map_add,hp,hr] -- simp alters before match?
  | mul_X q i hp=>
    simp only [_root_.map_mul, eval₂Hom_X',hp];
    rw [encode,Raw.frame_eq A h, applyTo,MvPolynomial.aeval_X]; rfl

/-- Engineering horizon *of labels*, analogous to `Labels.limited`. -/
def weight (i:Glyph G):ℕ := i.order+2
def bidegree (i:Glyph G):ℕ×ℕ:=(weight i,1)
def limited (G:Gauge)(d:ℕ):= restrictSupport ℂ {b|(Finsupp.weight (weight (G:=G))) b ≤ d}
def spin (u:G.El)(p:Tower G): Tower G:=fun j a b w=> G.adjoint u (p j a b w)
def invariant (G:Gauge):Submodule ℂ (Pol G) where
  carrier:={p|∀ q:Tower G,∀ u:G.El, applyTo (spin u q) p=applyTo q p}
  zero_mem':=by simp
  add_mem' {x y} h e q u:=by rw [map_add,h q u,e q u,map_add]
  smul_mem' c x h q u:=by rw [map_smul,h q u,map_smul]

def localSpace (G:Gauge)(d:ℕ):= limited G d ⊓ invariant G
abbrev Field (G:Gauge)(d:ℕ):= ↥(localSpace G d)

section
variable {d:ℕ}
lemma in_bounds {v:Pol G}(hp:v∈ limited G d){b}(hb:b ∈ v.support)(i)(hi:i∈ b.support):weight i ≤ d:=by
  have he: Finsupp.weight (weight (G:=G)) b ≤ d:= (MvPolynomial.mem_restrictSupport_iff ℂ).mp hp hb
  rw [Finsupp.weight_apply,Finsupp.sum] at he
  have hv:1 ≤ b i:=Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
  refine (le_mul_of_one_le_left (Nat.zero_le (weight i)) hv).trans ((Finset.single_le_sum (f:=fun x=>b x*weight x) (fun _ _=> Nat.zero_le _) hi).trans ?_)
  exact he

lemma radial_check_var {i:Glyph G}(p:Labels.Jet G)(g:ℝ)(h:weight i ≤ d):
    Labels.read p (Raw.radialPol (encode (↑g) i)) = coords (evaluate g (radField d p) 0) i:=by
  unfold coords encode evaluate
  exact Raw.radial_receipt d p _ _ _ _ _ h

def toCommon (g:ℂ):Pol G →ₗ[ℂ] Labels.Pol G where
  toFun p:= Raw.radialPol (graph (G:=G) g p)
  map_add' a b:=by rw [map_add,map_add]
  map_smul' t a:=by simp [MvPolynomial.smul_eq_C_mul,Raw.radialPol,graph] -- bind

lemma var_scope (g:ℂ)(i:Glyph G): Tier Labels.generation (weight i) (toCommon g (MvPolynomial.X i)) := by
  change Tier _ _ (Raw.radialPol ((eval₂Hom _ _) _))
  rw [eval₂Hom_X',encode,Raw.coeff_rebuild g _ _ _ _ _ le_rfl,map_sum]
  apply MvPolynomial.IsWeightedHomogeneous.sum; intro k hk
  rw [MvPolynomial.smul_eq_C_mul,_root_.map_mul, Raw.radialPol,MvPolynomial.eval₂Hom_C]; apply MvPolynomial.IsWeightedHomogeneous.C_mul
  intro b he
  have hp:= Raw.graded_pol (Raw.grade_frame i.chain i.faceL i.faceR i.color k) he
  rw [Labels.weight_slot] at hp; exact congrArg Prod.fst hp
lemma scope {g:ℂ}{p: Pol G}(h:p∈ limited G d):toCommon g p∈Labels.limited G d :=by
  rw [p.as_sum,map_sum]
  apply Submodule.sum_mem; intro i hi
  let m:= Finsupp.weight (Form.weight (G:=G)) i
  have hm : m ≤ d:= (MvPolynomial.mem_restrictSupport_iff ℂ).mp h hi
  change Raw.radialPol (graph g ((MvPolynomial.monomial i) (p.coeff i))) ∈ _
  unfold graph; rw [MvPolynomial.eval₂Hom_monomial,_root_.map_mul,Raw.radialPol,MvPolynomial.eval₂Hom_C]
  unfold Finsupp.prod; rw [map_prod]
  let u : Glyph G→Labels.Pol G:=fun i=> Raw.radialPol (encode g i)
  have he : Tier Labels.generation m (MvPolynomial.C (p.coeff i) * ∏ a∈i.support,u a ^ i a):=by
    apply MvPolynomial.IsWeightedHomogeneous.C_mul; unfold m; rw [Finsupp.weight_apply]
    refine MvPolynomial.IsWeightedHomogeneous.prod _ _ _ fun b hb=> ?_
    have hh:= var_scope g b
    change Tier _ _ (Raw.radialPol ((eval₂Hom _ _) _)) at hh
    rw [MvPolynomial.eval₂Hom_X'] at hh
    exact hh.pow ..
  simp_rw [map_pow]
  apply (MvPolynomial.mem_restrictSupport_iff ℂ).mpr
  intro b hb; change Labels.height b ≤ d; apply le_trans _ hm
  exact (he (MvPolynomial.mem_support_iff.mp hb)).le

lemma radial_checks (p:Field G d)(J:Labels.Jet G)(g:ℝ):
    Labels.read J (toCommon (↑g) p.val)=actual g (radField d J) 0 p.val:=by
  change Labels.read J (Raw.radialPol (graph (↑g) p.val))=_
  rw [p.val.as_sum,map_sum,map_sum,map_sum]; unfold actual; rw [map_sum]
  refine Finset.sum_congr rfl fun b hb=> ?_
  rw [graph,eval₂Hom_monomial,map_mul,map_mul,Raw.radialPol,eval₂Hom_C]
  unfold Finsupp.prod applyTo
  rw [map_prod,map_prod, MvPolynomial.aeval_monomial]; dsimp
  simp_rw [map_pow]
  have hx:= p.property.1
  have hk:∀i∈b.support,Labels.read J (Raw.radialPol (encode (↑g) i)) = coords (evaluate g (radField d J) 0) i:=fun i hi=>radial_check_var J g (in_bounds hx hb _ hi)
  change Labels.read J (MvPolynomial.C _)* _=_
  unfold Raw.radialPol at hk
  simp only [Labels.read,MvPolynomial.aeval_C,Algebra.algebraMap_self,RingHom.id_apply]
  exact congrArg (fun c:ℂ=> p.val.coeff b * c) (Finset.prod_congr rfl (fun a ha=>by
    exact congrArg (fun c:ℂ=> c ^ b a) (hk a ha)))
end
section inverse
variable {d:ℕ}
open Pert.Align
-- Take on ANY unconstrained input first (for coloring property)
def recover (p : Tower G): Labels.Jet G:=fun j=> radialize (p j)
lemma rec_color (p:Tower G)(u:G.El):recover (spin u p)=Labels.colored u (recover p):=funext (fun _=>radial_color ..)

def vertex (v:Spot G d) : Glyph G:=⟨d,v.γ,v.slash,v.via,v.color⟩
lemma spot_meter (V:Tower G) (a:Spot G d): ((a.meter (V d) : ℝ):ℂ)=coords V (vertex a):=by
   unfold coords vertex Spot.meter probes
   rw [LinearMap.comp_apply]
   change (↑(inner ℝ (unitColor G a.color) ((V d) a.slash a.via a.γ)):ℂ)=_
   congr 1
   change inner ℝ (EuclideanSpace.single a.color 1) (V d a.slash a.via a.γ) = _
   simpa only [WilsonRules.baseColor,EuclideanSpace.basisFun_apply] using! (WilsonRules.base_inner (V d a.slash a.via a.γ) a.color)

def dualX (i:Labels.Key G): Form.Pol G:=
   ∑ v:Spot G i.1, MvPolynomial.X (vertex v) * MvPolynomial.C (↑((Labels.axes G i.1).repr (radialize v.impulse) i.2):ℂ)
lemma dual_true (p:Tower G)(i:Labels.Key G):applyTo p (dualX i)=Labels.coord (recover p) i:=by
   have he:= meter_full (p i.1)
   unfold dualX
   simp only [_root_.map_sum,_root_.map_mul,applyTo,MvPolynomial.aeval_X,MvPolynomial.aeval_C,Algebra.algebraMap_self,RingHom.id_apply,← spot_meter]
   unfold Labels.coord recover
   conv_rhs=> rw [he]
   change _= (↑(((Labels.axes G i.1).repr (radialMap (∑ v, _))) _):ℂ)
   rw [_root_.map_sum,_root_.map_sum,Finsupp.finsetSum_apply,Complex.ofReal_sum];
   refine Finset.sum_congr rfl fun a _=> ?_; rw [map_smul,map_smul,Finsupp.smul_apply,smul_eq_mul,Complex.ofReal_mul]; rfl

def sectionPol : Labels.Pol G→ₐ[ℂ] Form.Pol G:= MvPolynomial.aeval dualX
lemma section_reads (A:Tower G)(p:Labels.Pol G):applyTo A (sectionPol p)=Labels.read (recover A) p:=by
  have h : (applyTo A).comp sectionPol= Labels.read (recover A):= by
    ext i; rw [AlgHom.comp_apply, sectionPol,MvPolynomial.aeval_X,dual_true, Labels.read,MvPolynomial.aeval_X]
  exact DFunLike.congr_fun h p
lemma section_grade (k:Labels.Key G): Tier Form.bidegree (Labels.bidegree k) (sectionPol (MvPolynomial.X k)):= by
  rw [sectionPol,MvPolynomial.aeval_X]; unfold dualX
  refine IsWeightedHomogeneous.sum _ _ _ fun i _=>?_ ; rw [mul_comm]; exact (isWeightedHomogeneous_X ..).C_mul _
lemma homogeneous (p:Labels.Label G d)(m:ℕ×ℕ)(h:p∈Labels.Grade m):Tier Form.bidegree m (sectionPol p.val):=by
   change Tier Form.bidegree _ (MvPolynomial.eval₂Hom _ dualX _)
   exact Tier.bind dualX Form.bidegree (fun i=>by simpa only [sectionPol,MvPolynomial.aeval_X] using! section_grade (G:=G) i) ((Labels.pure_grade m p).mp h) -- prod η

def asGlyph : Label G d→ₗ[ℂ] Field G d:=(sectionPol.toLinearMap.comp (Labels.localFields G d).subtype).codRestrict (Form.localSpace G d) (by
  intro p; change sectionPol p.val∈Form.localSpace G d
  constructor
  · rw [← decompose p,AddSubmonoidClass.coe_finsetSum,_root_.map_sum]; apply Submodule.sum_mem; intro i hi
    rw [AddSubmonoidClass.coe_finsetSum,_root_.map_sum]; apply Submodule.sum_mem; intro j hj
    apply (MvPolynomial.mem_restrictSupport_iff ℂ).mpr; intro a ha
    have he:= homogeneous (gradePart (i,j) p) (i,j) (gradePart_mem (i,j) p) (MvPolynomial.mem_support_iff.mp ha)
    have hp:=congrArg Prod.fst he
    change (Finsupp.weight weight) a ≤ d; simp only [Finsupp.weight_apply,Finsupp.sum, Prod.fst_sum,bidegree] at *; exact hp.trans_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
  intro q u; simp only [section_reads,rec_color]; exact p.property.2 _ _)
lemma from_radial (A:Label G d)(q:Labels.Jet G)(g:ℝ): applyTo (evaluate g (radField d q) 0) (asGlyph A).val= Labels.read q A.val:=by
  change applyTo _ (sectionPol A.val)= _ ; rw [section_reads, ← Source.Drops.racts A (recover _), ← Source.Drops.racts A q]
  apply congrArg (fun p : Source.Drops.Snap G d=> Labels.read (Source.Drops.expand d p) A.val)
  funext k; exact reconstruct g d q k.val (by have ha:=k.isLt; omega)

/-- Right-inverse independent curvature representation, with exactly the requested open legs for
all actual nonlinear couplings. -/
lemma rebound (A:Label G d)(g:ℝ): toCommon (↑g) (asGlyph A).val=A.val:= Labels.eval_ext _ _ (fun p=> (radial_checks (asGlyph A) p g).trans (from_radial A p g))
end inverse
end Form
end YM.RG06.Continuum
