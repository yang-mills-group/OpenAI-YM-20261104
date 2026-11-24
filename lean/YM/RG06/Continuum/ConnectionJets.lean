import YM.RG06.Continuum.Connection
import YM.Maxwell.Exterior
import YM.Gauge.Casimir

/-!
# Bare differential operators before any scheme

Work on arbitrary continuum connections near a site, Euclidean conventions in 4 spacetime
dimensions. This layer identifies field LABELS, not graphs or renormalized vertices. Physical
color is the real skew convention of `Gauge`. `curvature` and `covariant` keep an explicit scalar `g`
multiplying the bracket. For substituting an unrescaled connection (links integrate A) take g=1;
for link-log fluctuation variable exp(g B) per bond divide one g per curvature factor. Do not
infer a named g in the external scheme here. No use of equations or gauge fixing in their
definition; do NOT symmetrize the iterated covariant derivatives implicitly (commute only as
stated with bracketed F). Ordinary derivative words are ordered using the SAME head-outermost
convention. Smooth-global assumptions suffice because testing polynomial germs at any point sees
the entire finite jet domain; identities with hypotheses on smooth connections do not promise a
global smooth connection in the Yang–Mills measure!
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG06.Continuum
open Analysis Function
open scoped Topology ContDiff Matrix.Norms.Frobenius
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- E4-real partial derivatives, unnormalized throughout (when reading Taylor coefficients we
divide explicitly). Root at any x. -/
def par (i : Axis) (f:E4→V) := Analysis.D (basis i) f

def Good (f:E4→V) := ContDiff ℝ ∞ f
lemma Good.par {f:E4→V} (h:Good f)(i:Axis): Good (YM.RG06.Continuum.par i f) :=
  contDiff_iff_contDiffAt.mpr fun _=> dSmooth (ContDiff.contDiffAt h) _ (by simp)
lemma Good.germ {f:E4→V}(h:Good f)(x:E4):DifferentiableAt ℝ f x:=ContDiff.differentiable h (by simp) x
lemma par_linear (L: V →L[ℝ] W){f:E4→ V}(h:Good f) (i:Axis) : par i (fun x=>L (f x))=fun x=>L (par i f x):=by
  funext x;unfold par D; rw [show (fun x=>L (f x))=L ∘ f from rfl,fderiv_comp x L.differentiableAt (h.germ _),L.fderiv];rfl
lemma par_add {f g:E4→V}(h:Good f)(hg:Good g)(i:Axis):par i (f+g)=par i f+par i g:=by funext x; unfold par D;rw [fderiv_add (h.germ x) (hg.germ x)];rfl
lemma par_neg {f:E4→V}(i:Axis):par i (-f)= -par i f:=by funext x;unfold par D;rw [fderiv_neg];rfl
lemma par_scale (c:ℝ){f:E4→V}(h:Good f)(i:Axis):par i (c • f)=c • par i f:=by funext x; unfold par D;rw [fderiv_const_smul (h.germ x)];rfl
lemma par_cross {f:E4→V}(hf:Good f)(i j: Axis)(x:E4): par i (par j f) x=par j (par i f) x :=
  Analysis.commuteD ((ContDiff.contDiffAt hf).of_le (show ((2:ℕ):WithTop ℕ∞)≤∞ from WithTop.coe_le_coe.mpr le_top)) ..

def derivative (w:List Axis)(f:E4→V):E4→V:= match w with
 | []=> f
 | a::l=> par a (derivative l f)

/-- Fin j presentation for basis/tensor APIs. -/
def delta : {j:ℕ} → (Fin j → Axis) → (E4→V) → E4→V
 | 0, _, f => f
 | _+1, w, f=> par (w 0) (delta (Fin.tail w) f)

lemma deltaList (j:ℕ)(w: Fin j→Axis)(f:E4→V):delta w f=derivative (List.ofFn w) f:=by
  induction j with
  | zero=> simp [delta,derivative]
  | succ j H=>simp only [delta,List.ofFn_succ,derivative,H];rfl
lemma higher {f:E4→V}(h:Good f)(w:List Axis): Good (derivative w f):=by induction w with
  | nil=> exact h
  | cons a l H=> exact H.par _
lemma healthy {f:E4→V}(h:Good f){j:ℕ}(w:Fin j→Axis) :Good (delta w f):= by rw [deltaList]; exact higher h _

lemma permutes (w s : List Axis)(h:w.Perm s){f:E4→V}(hp:Good f): derivative w f=derivative s f:=by
  induction h with
  | nil=>rfl
  | cons a h H=> exact congrArg (par a) H
  | @swap a b s=> funext x; exact par_cross (higher hp s) ..
  | trans h h' H H'=> exact H.trans H'

lemma dx (j:ℕ)(w:Fin j→Axis)(f:E4→V)(hp:Good f): delta w f = fun x=>iteratedFDeriv ℝ j f x (basis ∘ w):=by
  induction j with
  | zero=> funext x; simp [delta]
  | succ j H=>
    have he : basis ∘ w = Fin.cons (basis (w 0)) (basis ∘ Fin.tail w) := funext fun i=> Fin.cases rfl (fun b=>by simp [Fin.tail,Function.comp_def]) i
    simp_rw [delta,he,H,Analysis.cons_jet (show ContDiffAt ℝ ((j+1:ℕ):WithTop ℕ∞) f _ from (ContDiff.contDiffAt hp).of_le (WithTop.coe_le_coe.mpr le_top))]; rfl

section gauge
variable {G:Gauge}

abbrev Section (G:Gauge):= E4→G.Color
abbrev Connection (G:Gauge):=Axis→ Section G
def Smooth (A:Connection G):=∀ i,Good (A i)
/-- Bracket conventions pinned by `Gauge.colorMat_ad x y = X Y - Y X`. -/
def bracket (f q : Section G) (x:E4) := G.ad (f x) (q x)
lemma bracket_anti (a b:G.Color) : G.ad a b= -G.ad b a:=by apply G.colorMat_injective; rw [map_neg,G.colorMat_ad,G.colorMat_ad]; abel
lemma bracket_self (a:G.Color):G.ad a a=0:=by apply G.colorMat_injective; rw [map_zero,G.colorMat_ad,sub_self]
lemma bracket_jacobi (a b c:G.Color): G.ad (G.ad a b) c=G.ad a (G.ad b c) - G.ad b (G.ad a c):= LinearMap.congr_fun (G.ad_jacobi a b) c

lemma Good.mark {f q:Section G}(h:Good f)(hq:Good q): Good (bracket f q):=by
  let L : G.Color→L[ℝ](G.Color→L[ℝ]G.Color):= (LinearMap.toContinuousLinearMap.toLinearMap.comp G.ad).toContinuousLinearMap
  exact ((L.contDiff.comp (show ContDiff ℝ ∞ _ from h)).clm_apply (g:=q) (show ContDiff ℝ ∞ _ from hq))
lemma par_bracket {f q:Section G}(h:Good f)(hq:Good q)(i:Axis)(x:E4) : par i (bracket f q) x = bracket (par i f) q x + bracket f (par i q) x:=by
  let L : G.Color→L[ℝ](G.Color→L[ℝ]G.Color):= (LinearMap.toContinuousLinearMap.toLinearMap.comp G.ad).toContinuousLinearMap
  have he:= ((L.hasFDerivAt.comp x (h.germ x).hasFDerivAt).clm_apply (hq.germ x).hasFDerivAt).fderiv
  apply (DFunLike.congr_fun he (basis i)).trans -- congrFun' maybe name
  exact add_comm _ _

def curvature (g:ℝ)(A:Connection G)(i j:Axis):Section G:= par i (A j) + -par j (A i) + g • bracket (A i) (A j)
def covariant (g:ℝ)(A:Connection G)(i:Axis)(f:Section G):Section G:= par i f+ g • bracket (A i) f

def nablas (g:ℝ)(A:Connection G):{j:ℕ}→(Fin j→Axis)→Section G→Section G
 | 0, _, f => f
 | _+1, w, f=> covariant g A (w 0) (nablas g A (Fin.tail w) f)

def word (g:ℝ)(A:Connection G)(w:List Axis)(f:Section G):Section G:= match w with
 | []=>f
 | i::s=>covariant g A i (word g A s f)
lemma as_nablas (g:ℝ)(A:Connection G)(j:ℕ)(w:Fin j→Axis)(f:Section G): word g A (List.ofFn w) f=nablas g A w f:=by
  induction j with
  | zero=>simp [word,nablas]
  | succ j H=>simp only [List.ofFn_succ,word,nablas,H];rfl

/-- `Curvature jets` used in the dictionary: ordered covariant derivatives, evaluated at x
and divided by `j!` (not the count-factorial; these are tensor Taylor conventions).
This convention matches the basis at g=0. -/
def covJet (g:ℝ)(A:Connection G){j:ℕ}(w:Fin j→Axis)(a b:Axis)(x:E4):G.Color:=
    ((j.factorial:ℝ)⁻¹) • nablas g A w (curvature g A a b) x

variable (g:ℝ)(A:Connection G)

lemma Smooth.F (h:Smooth A)(a b:Axis) : Good (curvature g A a b):=
  ContDiff.add (ContDiff.add ((h b).par a) (ContDiff.neg ((h a).par b))) (ContDiff.const_smul g (Good.mark (h a) (h b)))
lemma Smooth.connection (h:Smooth A)(i:Axis)(x:Section G)(hx:Good x): Good (covariant g A i x):=by
  exact ContDiff.add (hx.par i) (ContDiff.const_smul g ((h i).mark hx))
lemma Smooth.higherCov (h:Smooth A){j:ℕ}(w:Fin j→Axis)(x:Section G)(hx:Good x):Good (nablas g A w x):=by
  induction j with
  | zero=>exact hx
  | succ j H=>exact Smooth.connection g A h _ _ (H _)

lemma skew (a b:Axis)(x:E4): curvature g A b a x= -curvature g A a b x:=by simp only [curvature, bracket, Pi.add_apply,Pi.smul_apply,Pi.neg_apply, bracket_anti (A b _),smul_neg]; abel

-- `F=dA` at g=0 and **not** so at positive orders. Both identities below check required signs.
theorem commute (h:Smooth A)(f:Section G)(hf:Good f)(x:E4)(i j:Axis) :
    covariant g A i (covariant g A j f) x - covariant g A j (covariant g A i f) x = g • G.ad (curvature g A i j x) (f x) := by
  unfold covariant curvature
  have he a b: par a (g • bracket (A b) f) = _:= par_scale g ((h _).mark hf) a
  have H b : Good (g • bracket (A b) f):= ContDiff.const_smul g ((h b).mark hf)
  rw [par_add (hf.par _) (H j),par_add (hf.par _) (H i),he i, he j]
  simp only [Pi.add_apply,Pi.neg_apply,Pi.smul_apply, par_bracket (h _) hf,bracket,map_add,map_smul,map_neg,LinearMap.add_apply,LinearMap.neg_apply,LinearMap.smul_apply,
    par_cross hf i j,bracket_jacobi, smul_add,smul_sub,smul_neg]; abel

theorem bianchiJet (h:Smooth A)(x:E4)(a b c:Axis):
    covariant g A a (curvature g A b c) x + covariant g A b (curvature g A c a) x + covariant g A c (curvature g A a b) x = 0 := by
  have e (b c a): par a (fun y=> g • bracket (A b) (A c) y) = g • par a (bracket (A b) (A c)):= par_scale g ((h b).mark (h c)) a
  unfold covariant curvature
  have H i j:Good (par i (A j)+-par j (A i)):= ContDiff.add ((h _).par i) (ContDiff.neg ((h _).par j))
  have he(a b c:Axis):par a (par b (A c) + -par c (A b) + g • bracket (A b) (A c)) x = _:=
    congr_fun (par_add (H b c) (ContDiff.const_smul g ((h _).mark (h _))) a) x
  simp only [Pi.add_apply,Pi.smul_apply]
  simp only [he,show ∀ a b c:Axis, par a (par b (A c)+-par c (A b)) = _ from fun a b c=> par_add (g:=-par c (A b)) ((h _).par _) (ContDiff.neg ((h _).par _)) _,e,par_neg]
  simp only [Pi.add_apply,Pi.neg_apply,Pi.smul_apply, par_bracket (h _) (h _),smul_add]
  simp only [bracket,Pi.add_apply,Pi.smul_apply,Pi.neg_apply,map_smul,map_add,map_neg,smul_add,smul_neg]
  rw [par_cross (h c) a b, par_cross (h b) c a,par_cross (h a) b c]
  simp_rw [bracket_anti (par a (A b) x),bracket_anti (par b (A c) x),bracket_anti (par c (A a) x),smul_neg]
  -- last 3 use Jacobi
  rw [bracket_anti (A c x) (G.ad _ _), bracket_jacobi, bracket_anti (A c x) (A a x),map_neg]; simp_rw [smul_neg, smul_sub]; abel
end gauge
end YM.RG06.Continuum
