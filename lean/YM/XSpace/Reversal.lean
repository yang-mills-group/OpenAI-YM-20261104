import YM.XSpace.Bare

/-!
# Parity in the Wilson formal parameter

Without stopping at any fixed order. Includes dependence on all the external insertion
series (as opposed to a vacuum assertion). Real structure is handled separately.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Taylor
open MvPolynomial Next.Rank.Normal
variable {ι : Type*}

lemma reflected_slit (b : ι → ℂ) (p : Pol ι) : mirror ι (slit b p) = -slit b (mirror ι p) := by
  induction p using MvPolynomial.induction_on with
  | C a=> simp [mirror]
  | add p q hp hq=>simp only [map_add,hp,hq]; abel
  | mul_X p i hp=> rw [mul_comm p,slit_prod,map_mul (mirror ι),show mirror ι (X i)=_ from aeval_X _ _,neg_mul, map_neg (slit b),neg_neg]
                   simp only [slit_prod,map_add,map_mul,hp]; simp only [mirror,aeval_X, aeval_C,algebraMap_eq]; ring

lemma reflected_milk (Q : Next.Rank.Normal.Symmetric ι) (p : Pol ι) : milk Q (mirror ι p)=mirror ι (milk Q p):=by
  induction p using MvPolynomial.induction_on with
  | C a=> simp [mirror,algebraMap_eq]
  | add p q hp hq=> rw [map_add,map_add,hp,hq,map_add,map_add]
  | mul_X p i hp=> rw [mul_comm p,map_mul,show mirror ι (X i) = -(X i) from aeval_X ..,neg_mul,map_neg (milk Q), feeds, hp,feeds,map_add,map_mul,reflected_slit]; simp only [mirror,aeval_X]; ring
lemma mirror_blend (Q : Next.Rank.Normal.Symmetric ι) (p : Pol ι) : blend Q 0 (mirror ι p)=blend Q 0 p:=by
  rw [blend_components,reflected_milk,blend_components]; apply AlgHom.congr_fun (show (aeval (0:ι→ℂ)).comp (mirror ι)=aeval 0 from ?_); ext1 a; simp [mirror]

lemma slit_real (b : ι → ℝ) (p : Pol ι) : conjPol ι (slit (fun i=> (b i:ℂ)) p)=slit (fun i=> (b i:ℂ)) (conjPol ι p):=by
  induction p using MvPolynomial.induction_on with
  | C a=> simp [conjPol]
  | add p q hp hq=> simp only [map_add,hp,hq]
  | mul_X p i hp=> rw [mul_comm p,slit_prod,map_add,map_mul,map_mul,map_mul,_root_.mul_comm (conjPol ι (C _)),hp,show conjPol ι (X i)=_ from map_X (starRingEnd ℂ) _,slit_prod]; simp [conjPol,mul_comm]
lemma milk_real (Q : Next.Rank.Normal.Symmetric ι) (b : ι→ι→ℝ) (h : ∀ i, Q.cov i=fun j=> (b i j:ℂ)) (p : Pol ι) :
    milk Q (conjPol ι p)= conjPol ι (milk Q p) :=by
  induction p using MvPolynomial.induction_on with
  | C a=> simp [conjPol]
  | add p q hp hq=> simp only [map_add,hp,hq]
  | mul_X p i hp=> rw [mul_comm p,map_mul,show conjPol ι (X i)=_ from map_X (starRingEnd ℂ) _,feeds,hp,feeds,map_add,map_mul,h i,slit_real]; simp [conjPol]
lemma blend_real (Q : Next.Rank.Normal.Symmetric ι) (b : ι→ι→ℝ) (h : ∀ i,Q.cov i=fun j=> (b i j:ℂ)) (p : Pol ι) :
    blend Q 0 (conjPol ι p)=star (blend Q 0 p) := by
  rw [blend_components,blend_components,milk_real _ b h]; generalize milk Q p=z
  induction z using MvPolynomial.induction_on with
  | C a=> simp [conjPol]
  | add p q hp hq=> simp only [map_add,hp,hq,star_add]
  | mul_X p i hp=> simp [conjPol]
end YM.XSpace.Taylor

namespace YM.XSpace.Bare
open PowerSeries
open Next.Rank.Normal (blend)
variable {R : Period} {G : Gauge} (T : R.Tree)

def reverseArgs (G : Gauge) : Series T G →+* Series T G :=
  (rescale (-1 : Vertices T G)).comp (PowerSeries.map (Taylor.mirror (T.Key G)).toRingHom)

lemma reverse_coeff (F : Series T G) (n : ℕ) : coeff n (reverseArgs T G F)=(-1)^n * Taylor.mirror _ (coeff n F):=by rw [reverseArgs,RingHom.comp_apply,coeff_rescale,coeff_map]; rfl
lemma reverse_interaction (G : Gauge) : reverseArgs T G (interaction T G)=interaction T G := PowerSeries.ext fun n => by
  have h (f : Vertices T G) : (-1)^n * ((-1)^n * f)=f:=by rw [← mul_assoc, ← mul_pow,neg_one_mul,neg_neg,one_pow,one_mul]
  rw [reverse_coeff,interaction,coeff_mk]; split_ifs
  · simp
  rw [map_neg, Taylor.mirror_divided, pow_add]; norm_num; simp [h]
lemma reverse_haar (G : Gauge) : reverseArgs T G (haar T G)=haar T G:=PowerSeries.ext fun n=>by
  rw [reverse_coeff,haar,Taylor.expandTaylor,coeff_mk,Taylor.mirror_divided, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg,one_pow,one_mul]
lemma reverse_weight (G : Gauge) : reverseArgs T G (weight T G)=weight T G:=by
  rw [weight,map_mul,reverse_haar]; congr 1
  calc reverseArgs T G (interactionExp T G) = PowerSeries.subst (reverseArgs T G (interaction T G)) (PowerSeries.exp _) := ?_
       _ = interactionExp T G := by rw [reverse_interaction]; rfl
  rw [interactionExp,reverseArgs,RingHom.comp_apply,FPS.substitute_ringHom _ _ (interaction_initial T G), map_exp,FPS.rescale_substitute _ _ (FPS.mapped_zero _ (interaction_initial ..))]; rfl

lemma reverse_diagrams (F : Series T G) : diagrams T G (reverseArgs T G F)=rescale (-1 : ℂ) (diagrams T G F) := PowerSeries.ext fun n=>by
  have he := reverse_weight T G
  rw [diagram_coeff,← show reverseArgs T G (weight T G* F)=_ from (map_mul ..).trans (congr_arg (·*_) he),reverse_coeff]; rw [← show MvPolynomial.C ((-1:ℂ)^n) = (-1:Vertices T G)^n by simp]
  rw [MvPolynomial.C_mul',map_smul,Taylor.mirror_blend,coeff_rescale,diagram_coeff]; rfl

lemma reverse_normalized (F : Series T G) : normalized T G (reverseArgs T G F) = rescale (-1 : ℂ) (normalized T G F) := by
  symm; apply denominator_determines; rw [← show rescale (-1 : ℂ) (vacuum T G)=vacuum T G by rw [vacuum,← reverse_diagrams,map_one (reverseArgs T G)],← map_mul,normalize_denominator,reverse_diagrams]

lemma reverse_scalar (z : ℂ) (F : Series T G) : reverseArgs T G (z • F) = z • reverseArgs T G F:=by
  apply PowerSeries.ext; intro n; rw [reverse_coeff,coeff_smul,coeff_smul,map_smul,reverse_coeff,mul_smul_comm]

/-- This predicate holds for sources with the indicated slot parity. It suffices through
all formal orders at once. -/
def HasParity (d : ℕ) (F : Series T G) : Prop := reverseArgs T G F = ((-1:ℂ)^d) • F

lemma parity_mul (d a : ℕ) {F H : Series T G} (he : HasParity T d F) (hp : HasParity T a H) : HasParity T (d+a) (F*H):=by
  unfold HasParity; rw [pow_add,map_mul,he,hp,smul_mul_assoc,mul_smul_comm,smul_smul]
lemma parity_result {d : ℕ} {F : Series T G} (h : HasParity T d F) :
    rescale (-1 : ℂ) (normalized T G F) = ((-1:ℂ)^d) • normalized T G F:= by rw [← reverse_normalized,h,map_smul]

-- real structure
def conjugate (G : Gauge) : Series T G →+* Series T G:=PowerSeries.map (Taylor.conjPol (T.Key G))
lemma weight_real (G : Gauge) : conjugate T G (weight T G)=weight T G:=by
  have he : conjugate T G (interaction T G)=interaction T G := PowerSeries.ext fun n=> by
    rw [conjugate,coeff_map,interaction,coeff_mk]; split_ifs; rw [map_zero]
    rw [map_neg,Taylor.divided_real _ _ _ ((T.continuousJet G).of_le le_top)]
  have hp : conjugate T G (haar T G)=haar T G := PowerSeries.ext fun n=> by
    rw [conjugate,coeff_map,haar,Taylor.expandTaylor, coeff_mk, Taylor.divided_real _ _ _ ((relative_smooth T G).of_le le_top)]
  rw [weight,map_mul,hp,interactionExp]; unfold conjugate at *
  rw [FPS.substitute_ringHom _ _ (interaction_initial T G),map_exp,he]
lemma real_diagrams (F : Series T G) : diagrams T G (conjugate T G F) = PowerSeries.map (starRingEnd ℂ) (diagrams T G F):=PowerSeries.ext fun n=>by
  have he:=weight_real T G; rw [diagram_coeff,← show conjugate T G (weight T G* F)=_ from (map_mul ..).trans (congr_arg (· * _) he),conjugate,coeff_map,Taylor.blend_real _ _ (show ∀ i, (Q T G).cov i= _ from fun _=> rfl),coeff_map,diagram_coeff]; rfl

lemma normalize_real (F : Series T G) : normalized T G (conjugate T G F) = PowerSeries.map (starRingEnd ℂ) (normalized T G F) := by
  symm; apply denominator_determines; rw [← show PowerSeries.map (starRingEnd ℂ) (vacuum T G)=vacuum T G by rw [vacuum,← real_diagrams,map_one (conjugate T G)],← map_mul, normalize_denominator,real_diagrams]
end YM.XSpace.Bare
