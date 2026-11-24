import YM.RG06.Continuum.Rotation
import YM.RG06.Continuum.Abelian

/-!
# Off-shell classical field book on all E4 positions
`bridge` solves exactly the observational quotient on smooth connections at ANY site (not just
radial-specific Tests in eg `W.Homological`), E4 translation and G covariance included. These
are *pointwise* finite-jet relations, not claims about contact or continuum Euclidean correlations.
This file also proves that in 4D every sufficiently gauge invariant finite polynomial on ordinary
partial jets (even without a manifest curvature structure) has a common label with this same
meaning, using the smooth radial gauge proof. Keep lifts of these identities if dimensional
projections/analytic continuation are later required. Differential and EOM behavior in separate
files.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG06.Continuum
open Form Function Tensor Labels Analysis
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators
variable {G:Gauge} {V:Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def relative (z:E4) (f:E4→V) (y:E4):V:=f (y+z)
lemma Good.relative {f:E4→V}(h:Good f)(x:E4):Good (Continuum.relative x f):=ContDiff.comp h (contDiff_id.add contDiff_const)
lemma par_relative {f:E4→V}(h:Good f)(x:E4)(i:Axis): par i (relative x f)=relative x (par i f):=by
 funext y
 unfold par relative D
 have he:= ((h.germ (y+x)).hasFDerivAt.comp y ((hasFDerivAt_id y).add_const x)).fderiv; erw [he]; rfl
lemma derivative_relative {f:E4→V}(h:Good f)(x:E4)(w:List Axis): derivative w (relative x f)=relative x (derivative w f):=by
 induction w with
 | nil=>rfl
 | cons a w H=> rw [derivative,H,par_relative (higher h w),derivative]

def center (A:Connection G)(x:E4):Connection G:=fun i=>relative x (A i)
lemma smooth_center {A:Connection G}(h:Smooth A)(x:E4):Smooth (center A x):=fun i=>(h i).relative x

lemma read_center (p:Raw.Pol G){A:Connection G}(h:Smooth A)(x y:E4) : Raw.read (center A x) y p=Raw.read A (y+x) p:=by
 unfold Raw.read center; simp_rw [derivative_relative (h _),relative]
lemma actual_center (g:ℝ)(p:Form.Pol G){A:Connection G}(h:Smooth A)(x y:E4): Form.actual g (center A x) y p = Form.actual g A (y+x) p:=by rw [← tree_receipt p g (center A x) (smooth_center h x), ← tree_receipt p g A h,read_center _ h x y]

def ClassicalIdentity (g:ℝ){d:ℕ}(p:Form.Field G d):Prop:=∀ A:Connection G,Smooth A→∀ x,actual g A x p.val=0
/-- Primary smooth-field kernel theorem. -/
theorem all_positions (g:ℝ){d:ℕ}(p:Form.Field G d):p∈radical G g d ↔ ClassicalIdentity g p :=by
  rw [radial_tests]; constructor
  · intro h A s x
    obtain ⟨J,hJ⟩:= solved g (smooth_center s x) d
    simpa only [actual_center g _ s,zero_add] using! (hJ p).trans (h J)
  intro h J; exact h _ (rad_smooth d J) 0

/-- Off-shell continuum rendering of any common 4D curvature label -/
def submit (g:ℝ){d:ℕ}(A:Connection G)(x:E4):Label G d→ₗ[ℂ]ℂ:= (((applyTo (evaluate g A x)).toLinearMap).comp (localSpace G d).subtype).comp asGlyph
lemma respects (g:ℝ){d:ℕ}(A:Connection G)(h:Smooth A)(p:Form.Field G d)(x:E4): actual g A x p.val=submit g A x (bridge g p):=by
 let q:=p-asGlyph (bridge g p)
 have he:q∈radical G g d:=by change bridge g q=0; unfold q; rw [map_sub, retract,sub_self]
 have hh:=(all_positions g _).mp he A h x
 change applyTo _ (p.val-(asGlyph (bridge g p)).val)=0 at hh; rw [map_sub,sub_eq_zero] at hh;exact hh
lemma submit_ext (g:ℝ){d:ℕ}{p q:Label G d}(x:E4)
    (h:∀ A:Connection G,Smooth A→submit g A x p=submit g A x q): p=q:=by
 apply Subtype.ext; apply Labels.eval_ext; intro A
 have hp:= h (center (radField d A) (-x)) (smooth_center (rad_smooth d A) (-x))
 change actual g _ x (asGlyph p).val = actual g _ x (asGlyph q).val at hp
 rw [actual_center g _ (rad_smooth d A) (-x), actual_center g _ (rad_smooth d A) (-x), add_neg_cancel,actual,actual,from_radial,from_radial] at hp; exact hp
lemma submit_includes (g:ℝ)(A:Connection G)(x:E4){d e:ℕ}(p:Label G d)(h:d≤e):submit g A x (Labels.raiseLabel G h p)=submit g A x p:=rfl
lemma tree_inf (g:ℝ)(hg:g≠0){d:ℕ}(p:Form.Field G d)(A:Connection G)(s:Smooth A)(v:Phase G)(hv:Ready v)(x:E4):actual g (dressed g A v) x p.val=actual g A x p.val:=by
 apply Eq.trans _ (p.property.2 (evaluate g A x) (v x))
 change applyTo _ p.val = applyTo _ p.val
 refine congrArg (fun t=>applyTo t p.val) ?_; funext j i b w
 unfold spin evaluate covJet
 rw [at_depth g hg A s v hv,shade]; simp

namespace Raw
open MvPolynomial
/-- Keep the full raw local polynomial book, but distinguish which subspace is invariant under
all actual smooth finite phases. At coupling zero, gauge condition = Abelian gauge translations
PLUS the original simple color orthogonal action. This defines the gauge-invariant *pure A
sector at tree level*. No use of BV or ghost fields; don't take these evaluation kernels as
BV cohomology. -/
def gauge (g:ℝ) (p:Raw.Pol G): Prop:=
  (∀ A:Connection G,Smooth A→∀ u:G.El,read (changeColor A u) 0 p=read A 0 p) ∧
  (if g≠0 then ∀ A:Connection G,Smooth A→∀ s:Phase G,Ready s→ read (dressed g A s) 0 p=read A 0 p
   else ∀ A:Connection G,Smooth A→∀ q: Continuum.Section G,Good q→ read (fun i=> A i+par i q) 0 p=read A 0 p)

def enough (G:Gauge)(d:ℕ): Submodule ℂ (Raw.Pol G):= restrictSupport ℂ {b|Finsupp.weight size b ≤ d}

lemma locally {p:Raw.Pol G}{i:Raw.Key G}{d:ℕ}(h:p∈enough G d)(hi:i∈p.vars):size i ≤ d:=by
 obtain ⟨b,hb,hB⟩:=(mem_vars_iff_mem_support _).mp hi
 have hh:= (mem_restrictSupport_iff ℂ).mp h hb
 change Finsupp.weight size b ≤ d at hh; refine le_trans (le_trans ?_ (Finset.single_le_sum (s:=b.support) (a:=i) (f:=fun k=>b k * size k) (fun k _=>Nat.zero_le _) hB)) hh
 exact le_mul_of_one_le_left (Nat.zero_le _) (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hB))

lemma near_keys {p:Raw.Pol G}{d:ℕ}(h:p∈enough G d)(J:Labels.Jet G): read (radField d J) 0 p= Labels.read J (radialPol p):=by
  rw [p.as_sum,map_sum,map_sum,map_sum]
  refine Finset.sum_congr rfl fun b hb=>?_ ; rw [read,eval_monomial, radialPol,eval₂Hom_monomial,_root_.map_mul,Labels.read,MvPolynomial.aeval_C]
  unfold Finsupp.prod; rw [map_prod,Algebra.algebraMap_self,RingHom.id_apply]
  refine congrArg _ (Finset.prod_congr rfl fun i hi=>?_) -- products powers
  rw [map_pow]; change _ = Labels.read J (radialVar i) ^ b i; rw [var_reads d J i (locally h (support_subset_vars_of_mem_support hb hi))]

lemma directed {p:Raw.Pol G}{A:Connection G}(s:Smooth A){d:ℕ}(h:p∈enough G d)(hA:killed d A) :read A 0 p=Labels.read (snapshot d A s hA) (radialPol p):=by
  rw [← near_keys h,p.as_sum,map_sum,map_sum]; refine Finset.sum_congr rfl fun b hb=>?_
  rw [read,eval_monomial,read,eval_monomial]
  unfold Finsupp.prod; refine congrArg _ (Finset.prod_congr rfl (fun i hi=>?_));
  change (↑(derivative i.chain (A i.primary) 0 i.color) :ℂ)^ _=_; rw [snapshot_jet s hA _ _ (locally h (support_subset_vars_of_mem_support hb hi))]

lemma render {d:ℕ}{p:Raw.Pol G}(h:p∈enough G d) : radialPol p∈ Labels.limited G d:= by
  rw [p.as_sum,map_sum]; apply Submodule.sum_mem; intro b hb
  apply (MvPolynomial.mem_restrictSupport_iff ℂ).mpr; intro a ha
  let m:= Finsupp.weight Raw.measure b
  have he := Tier.bind radialVar Labels.bidegree grades_var (MvPolynomial.isWeightedHomogeneous_monomial Raw.measure b (MvPolynomial.coeff b p) (m:=m) rfl) (MvPolynomial.mem_support_iff.mp ha)
  have hx := congrArg Prod.fst he
  have hd : Finsupp.weight size b ≤ d:= (mem_restrictSupport_iff ℂ).mp h hb
  change Labels.height a ≤ d
  rw [Labels.weight_slot] at hx;change Labels.height a=m.1 at hx;rw [hx]
  unfold m Raw.measure
  simp only [Finsupp.weight_apply,Finsupp.sum,Prod.fst_sum,Prod.smul_fst];exact hd

def ticket {d:ℕ}(g:ℝ)(p:Raw.Pol G)(h:p∈enough G d)(hv:gauge g p):Labels.Label G d:= ⟨radialPol p,render h,(fun J u=> by rw [← near_keys h, ← near_keys h,radialized]; exact hv.1 _ (rad_smooth d J) u)⟩
lemma submit_ticket {d:ℕ}(g:ℝ)(p:Raw.Pol G)(h:p∈enough G d)(hv:gauge g p): ∀ A:Connection G,Smooth A→∀x:E4,
  Raw.read A x p = submit g A x (ticket g p h hv):=by
  have hb:{k:ℕ}→∀ A:Connection G,Smooth A→ ∃ B:Connection G, Smooth B ∧ killed k B ∧ Form.evaluate g B 0=Form.evaluate g A 0 ∧ Raw.read A 0 p=Raw.read B 0 p:= by
    intro k; induction k with
    | zero=>intro A s; exact ⟨A,s,(fun _ hk=>False.elim (Nat.not_lt_zero _ hk)),rfl,rfl⟩
    | succ k H=>
      intro A s
      obtain ⟨B,hB,w,e,c⟩:= H A s
      by_cases hc:g≠0
      · exact ⟨dressed g B (dye g B k),sound _ _ hB _ (dye_ok g B k),stage g hc k B hB w,(center_same g hc B hB _ (dye_ok g B k) (dye_flat g B k)).trans e,
          c.trans (Eq.symm ((if_pos hc|>.mp hv.2) B hB _ (dye_ok g B k)))⟩ -- Eq-> iff
      · simp only [not_not, ne_eq] at hc -- hc? by_cases hs sets hc : ¬..; simp?
        subst g
        exact ⟨freeStage B k,smoothFree B hB k,(fun i hi z=> free_curve_price B hB k w i (Nat.lt_succ_iff.mp hi) z),(eval_free B hB k).trans e,
         c.trans (Eq.symm (by simpa only [freeStage,par_neg,sub_eq_add_neg] using! ((if_neg (not_not_intro rfl)|>.mp hv.2) B hB (-(obstacle k B)) (ContDiff.neg (obstacle_smooth k B)))))⟩
  intro A s x
  let q:= asGlyph (ticket g p h hv)
  obtain ⟨B,e,hk,hu,ha⟩:= hb (k:=d) (center A x) (smooth_center s x)
  change Raw.read A x p=actual g A x q.val
  rw [← zero_add x, ← read_center p s x 0, ← actual_center g q.val s x 0, ha,directed e h hk]
  unfold actual; rw [← hu];symm
  change actual g B 0 (asGlyph _).val= _
  rw [snapshot_eval g e hk (asGlyph _)]
  exact from_radial (ticket g p h hv) (snapshot d B e hk) g

-- Conversely independent curvature operators meet these tree gauge tests
def freeTranslate (A:Connection G)(q:Section G):Connection G:=fun i=>A i+par i q
lemma free_f (A:Connection G)(h:Smooth A)(q:Section G)(hq:Good q)(i j:Axis)(x:E4):curvature 0 (freeTranslate A q) i j x = curvature 0 A i j x:=by
 unfold freeTranslate curvature
 rw [par_add (h _) (hq.par _),par_add (h _) (hq.par _)]; simp only [zero_smul,Pi.add_apply,Pi.neg_apply,par_cross hq i j]; abel
lemma eval_grad (A:Connection G)(h:Smooth A)(q:Section G)(hq:Good q)(x:E4): Form.evaluate 0 (freeTranslate A q) x = Form.evaluate 0 A x:=by
 funext j i b w
 unfold Form.evaluate covJet
 have he(A B:Connection G)(k:ℕ)(w:Fin k→Axis)(v:Section G):nablas 0 A w v=nablas 0 B w v:=by
    induction k with
    | zero=> rfl
    | succ k H=>rw [nablas,nablas,H]; simp [covariant]
 rw [he _ A,show curvature 0 (freeTranslate A q) i b= curvature 0 A i b from funext (fun x=>free_f A h q hq i b x)]
lemma graph_invariants (g:ℝ){d:ℕ}(p:Form.Field G d): gauge g (graph (↑g) p.val) := by
 constructor
 · intro A h u; rw [Form.tree_receipt _ _ A h, Form.tree_receipt _ g (changeColor A u) (show Smooth _ from fun i=> (G.adjoint u).toContinuousLinearMap.contDiff.comp (h i))]
   unfold Form.actual; rw [spin_curved _ h]; exact p.property.2 _ _
 split
 next hG=>
   intro A h s hs; rw [Form.tree_receipt _ _ A h, Form.tree_receipt _ g _ (sound _ _ h _ hs),tree_inf _ hG p _ h s hs]
 next hG=>
   simp only [not_not,ne_eq] at hG; subst g
   intro A h s hs
   change read (freeTranslate _ _) _ _ = _; rw [Form.tree_receipt _ _ A h, Form.tree_receipt _ 0 (freeTranslate A s) (show Smooth _ from fun i=> ContDiff.add (h i) (hs.par i)),Form.actual,Form.actual, eval_grad A h s hs]

lemma gauge_every {p:Raw.Pol G}(g:ℝ)(h:gauge g p):
    (∀ A:Connection G,Smooth A→∀ u:G.El,∀ x:E4, read (changeColor A u) x p=read A x p) ∧
  (if g≠0 then ∀ A:Connection G,Smooth A→∀ s:Phase G,Ready s→∀ x, read (dressed g A s) x p=read A x p
   else ∀ A:Connection G,Smooth A→∀ q: Continuum.Section G,Good q→∀ x, read (freeTranslate A q) x p=read A x p):=by
  have ht(x)(A:Connection G)(e:Smooth A):(read (center A x) 0) p=read A x p:=by rw [read_center _ e,zero_add]
  constructor
  · intro A s u x
    rw [← ht x A s,← ht x (changeColor A u) (fun i=> (G.adjoint u).toContinuousLinearMap.contDiff.comp (s i))]
    exact h.1 _ (smooth_center s x) u
  split
  next hG=>
   intro A s v w x
   let v' :Phase G:=fun y=>v (y+x)
   have hs :Ready v':=(show Good (face v) from w).relative x
   rw [← ht x A s,← ht x (dressed g A v) (sound _ _ s _ w)]
   suffices he: center (dressed g A v) x=dressed g (center A x) v' by rw [he]; exact ((if_pos hG).mp h.2) _ (smooth_center s _) _ hs
   funext i y; change _=shade v' (relative x (A i)) y-g⁻¹ • G.projectColor (par i (relative x (face v)) y* bar v' y); rw [par_relative (show Good (face v) from w)];rfl
  next hn=>
   intro A s q e x; rw [← ht x A s,← ht x (freeTranslate A q) (fun i=>ContDiff.add (s i) (e.par i))]
   have hN: center (freeTranslate A q) x=freeTranslate (center A x) (relative x q):=by funext i y; change _= A i (y+x)+par i (relative x q) y; rw [par_relative e];rfl
   rw [hN]; exact ((if_neg hn).mp h.2) _ (smooth_center s x) _ (e.relative x)
end Raw
end YM.RG06.Continuum
