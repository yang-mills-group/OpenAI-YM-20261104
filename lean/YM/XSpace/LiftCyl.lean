import YM.XSpace.Section
import YM.XSpace.Reversal
import YM.XSpace.VertexProducts
import YM.Work.F02

/-!
# Single insertion in formal bare variables (before self Wick subtraction)

Test-independent scalar/tensor fields. Read through order zero on linearized radial jets.
-/
set_option maxHeartbeats 400000
set_option autoImplicit false
noncomputable section
namespace YM.XSpace
open Filter Function Set Lattice RG Wilson Labels Source Source.Drops Bid MvPolynomial
open Work
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {R : Period} {H : Hol G} {d : ℕ}
namespace Survey
variable (A : Survey G H d)

def extract := fderiv ℝ A.recover 0

def glowing (x : Snap G d) : GaugePanel G A.size:= fun i=> glow x (A.looks i)
private lemma map_germ : AnalyticAt ℝ (bring H d A.looks) 0 := AnalyticAt.pi fun i=> (peg ..).shot (A.looks i)
private lemma brings_zero : bring H d A.looks 0=0:=funext fun i=> takes_zero H d (A.looks i)
lemma linear_jet (x : Snap G d) : A.extract (A.glowing x)=x:=by
  letI : CompleteSpace (Snap G d) := FiniteDimensional.complete ℝ _
  by_cases hd:1≤d
  · have he : fderiv ℝ A.recover 0=fderiv ℝ A.sees 0:=by
      have hc := G05.blockTaylor_jets (A.kit.1.contDiffAt.of_le (show (↑d:ℕ∞ω)≤ω from le_top)) 1 hd
      ext1 y; exact Eq.trans (iteratedFDeriv_one_apply (f:=A.recover) (x:=0) fun _=> y).symm
        ((congr_arg (fun M : _ [×1]→L[ℝ] _ => M fun _=> y) hc).trans (iteratedFDeriv_one_apply _))
    have hh : fderiv ℝ (A.sees ∘ (bring H d A.looks)) 0 = ContinuousLinearMap.id _ _:=
      (EventuallyEq.fderiv_eq (𝕜:=ℝ) (show _=ᶠ[𝓝 0] (id:Snap G d → Snap G d) from A.kit.2.2.1)).trans (fderiv_id ..)
    have hg : A.glowing x=fderiv ℝ (bring H d A.looks) 0 x := funext fun i=> by
      have hp : Blurb H d (A.looks i) = _:= fderiv_apply A.map_germ.differentiableAt i
      rw [glowing,← (peg ..).initial, hp]; rfl
    rw [fderiv_comp (𝕜:=ℝ) (g:=A.sees) (f:=bring H d A.looks) 0 (by rw [A.brings_zero]; exact A.kit.1.differentiableAt) A.map_germ.differentiableAt, A.brings_zero] at hh
    rw [extract,he,hg]; exact DFunLike.congr_fun hh x
  have he (i : Fin (d-1)) := i.isLt; funext i; specialize he i; omega
private lemma equiv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E→F) (hf : ContDiff ℝ ω f)
    (L : E→L[ℝ] E) (M : F→L[ℝ] F) (h : f ∘ L=M ∘ f) (x : E) : fderiv ℝ f 0 (L x)=M (fderiv ℝ f 0 x):=by
  have ht:= congr_arg (fun f:E→F=>fderiv ℝ f 0) h; rw [fderiv_comp _ (hf.differentiable (by simp) _) L.differentiableAt, fderiv_comp _ M.differentiableAt (hf.differentiable (by simp) _),ContinuousLinearMap.fderiv, ContinuousLinearMap.fderiv,map_zero] at ht
  exact DFunLike.congr_fun ht x
lemma extract_color (x : GaugePanel G A.size) (c : G.El) : A.extract (rotates c x)=snapColor c (A.extract x) := by
  let L:= LinearMap.toContinuousLinearMap (LinearMap.pi (fun i : Fin A.size=> G.adjoint c ∘ₗ LinearMap.proj i))
  have hp : A.recover ∘ L=snapColor c ∘ A.recover:=funext (recover_comm A c)
  exact equiv _ A.recover_smooth _ _ hp x
lemma extract_signed (x : GaugePanel G A.size) (s : Signed) : A.extract (A.roll s x)=snapTurn s.ortho⁻¹ (A.extract x):= by
  have hp : A.recover ∘ A.roll s=snapTurn s.ortho⁻¹ ∘ A.recover:=funext (recover_roll A s)
  exact equiv _ A.recover_smooth _ _ hp x
end Survey

namespace Bare
variable (T : R.Tree) (A : Survey G H d) (x : R.Sites)

def samples (v : T.Field G) : GaugePanel G A.size := mapped A.looks (expandAt x (T.links v))
lemma samples_at (v : T.Field G) (i : Fin A.size) : samples T A x v i=(A.looks i).atSite (T.links v) x:=rfl
@[simp] lemma samples_zero : samples T A x 0=0:= by
  funext i; rw [samples_at,← T.represent_eq, map_zero, F03.atSite_path,show faceValue (Precision.represent _) _=1 from Push.stroll_zero .., G.curvature_unit, map_zero]; rfl
lemma samples_smooth : ContDiffAt ℝ ω (samples T A x) 0:= by
  refine contDiffAt_pi.mpr (fun i=> ?_)
  have h (e : R.Bonds) : ContDiffAt ℝ ω (fun v:T.Field G => G.mat (T.links v e)) 0 := by
    simp_rw [← T.represent_eq]; exact (Work.F03.represent_smooth ..).contDiffAt.comp _ (LinearMap.toContinuousLinearMap (T.logdir (G:=G))).contDiff.contDiffAt
  simp_rw [samples_at,show ∀ u, (A.looks i).atSite (T.links u) x= F02.colorReal G (F02.slotExt (A.looks i) x (F02.physical (T.links u))) from fun u=> by rw [F02.slotExt_physical,F02.colorReal_up]]
  exact (F02.colorReal G).contDiff.contDiffAt.comp _ (((F02.slotExt_contDiff (G:=G) (A.looks i) x).restrict_scalars ℝ).contDiffAt.comp _ (F02.physical_contDiffAt h))
lemma samples_deriv (v : T.Field G) : fderiv ℝ (samples T A x) 0 v = fun i => T.linearCurl v (F03.slotFace (A.looks i) x) := by
  funext i; let f (v : T.Field G) := samples T A x v i
  have he : HasDerivAt (fun t : ℝ => f (t • v)) (T.linearCurl v (F03.slotFace (A.looks i) x)) 0:=by
    simp only [f,samples_at,← T.represent_eq,map_smul]; rw [Period.Tree.linearCurl,LinearMap.comp_apply, ← T.curl_eq]; exact F03.slot_deriv ..
  have hi := (samples_smooth T A x).differentiableAt (by simp)
  have hh : fderiv ℝ f 0 v=_ := (Push.side f ((contDiffAt_pi.mp (samples_smooth T A x) i).differentiableAt (by simp)) v).unique he
  rw [show fderiv ℝ f 0 = _ from fderiv_apply hi i] at hh; exact hh

/-- One energy grade key has always one slot. Give it the explicit bare factor
`g_N^{-1}`, i.e. shift the Taylor expansion. This yields a well-defined series. -/
def labelFunction (P : Labels.Pol G) (v : T.Field G) := read (expand d (A.recover (samples T A x v))) P
lemma label_smooth (P : Labels.Pol G) : ContDiffAt ℝ ω (labelFunction T A x P) 0 :=
  (G05.snap_read_smooth d P ω).contDiffAt.comp _ (A.recover_smooth.contDiffAt.comp _ (samples_smooth T A x))
lemma label_project (P : Labels.Pol G) (v : T.Field G) :
    labelFunction T A x P v=lumin (A.cyl P) (mapped A.looks (expandAt x (T.links v))):=(A.cylinder_at ..).symm

def factor (i : Labels.Key G) : Series T G := PowerSeries.mk fun n=> Taylor.divided (T.basis G) (n+1) (labelFunction T A x (X i))
private lemma lum (i : Labels.Key G) : labelFunction T A x (X i)=G05.snapCoord d i ∘ (A.recover ∘ samples T A x):=by funext v; simp only [labelFunction, Labels.read,aeval_X]; rfl
lemma factor_leading (i : Labels.Key G) (v : T.Field G) :
    Taylor.evalAt (T.basis G) v (PowerSeries.constantCoeff (factor T A x i)) =
      G05.snapCoord d i (A.extract (fun j=> T.linearCurl v (F03.slotFace (A.looks j) x))) := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, factor, PowerSeries.coeff_mk,Taylor.divided_one,lum,
    fderiv_comp (𝕜:=ℝ) _ (G05.snapCoord d i).differentiableAt ((A.recover_smooth.contDiffAt.comp _ (samples_smooth T A x)).differentiableAt (by simp)),
    fderiv_comp (g:= A.recover) (f:=samples T A x) _ (A.recover_smooth.differentiable (by simp) _) ((samples_smooth T A x).differentiableAt (by simp)), ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply, samples_zero, samples_deriv]; rfl
lemma factor_shifts (i : Labels.Key G) : PowerSeries.X*factor T A x i=Taylor.expandTaylor (T.basis G) (labelFunction T A x (X i)) :=by
  apply PowerSeries.ext; rintro (_|n)
  · simp only [Taylor.expand_coeff,Taylor.divided_zero]; simp [lum,A.recover_zero]
  rw [PowerSeries.coeff_succ_X_mul,factor,PowerSeries.coeff_mk,Taylor.expand_coeff]

def raw (P : Labels.Pol G) := aeval (factor T A x) P
lemma unshift (p : Labels.Pol G) :
    aeval (fun i=> PowerSeries.X*factor T A x i) p=Taylor.expandTaylor (T.basis G) (labelFunction T A x p) := by
  simp_rw [factor_shifts]
  induction p using MvPolynomial.induction_on with
  | C a => rw [aeval_C,PowerSeries.algebraMap_apply, MvPolynomial.algebraMap_eq,show labelFunction _ _ _ (C a)=fun _=> a by ext v; simp [labelFunction,Labels.read]]; exact (Taylor.expand_const ..).symm
  | add p q hp hq=> rw [map_add,hp,hq,show labelFunction T A x (p+q)=labelFunction T A x p+labelFunction T A x q from funext fun v=>map_add (read (expand d (A.recover (samples T A x v)))) p q,Taylor.expand_add _ (label_smooth T A x p) (label_smooth T A x q)]
  | mul_X p i hp=> rw [map_mul,aeval_X,hp, show labelFunction T A x (p* X i) = labelFunction T A x p*labelFunction T A x (X i) from funext fun v=> map_mul (read (expand d (A.recover (samples T A x v)))) p (X i),Taylor.expand_mul _ (label_smooth T A x p) (label_smooth T A x (X i))]

lemma coefficient_weight (n : ℕ) {P : Labels.Pol G} (h : ∀ i∈P.support,n=i.sum fun _ a=>a) :
    PowerSeries.X^n*raw T A x P = Taylor.expandTaylor (T.basis G) (labelFunction T A x P):=by
  classical
  rw [← unshift, raw,P.as_sum,map_sum,map_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i hi
  simp only [MvPolynomial.aeval_monomial,mul_pow,Finsupp.prod]; rw [Finset.prod_mul_distrib,h i hi,Finsupp.sum,Finset.prod_pow_eq_pow_sum]; ring
lemma raw_calculation (F : Labels.Frame G d) (T' : SectionData F) (h : A.Represents F T') {p : Labels.Label G d}
    (i n : ℕ) (hp : p∈ Labels.Grade (i,n)) : PowerSeries.X ^ n * raw T A x p.val =
    Taylor.expandTaylor (T.basis G) (fun v => T'.places (F.coords p) x (T.links v)) := by
  rw [show (fun v=> T'.places (F.coords p) x (T.links v))=labelFunction T A x p.val from funext fun v => h.2.2 p (expandAt x (T.links v))]
  refine coefficient_weight T A x _ (fun a ha=>?_)
  have ht := ((pure_grade _ p).mp hp) (MvPolynomial.mem_support_iff.mp ha); rw [weight_slot] at ht; exact congr_arg Prod.snd ht.symm
end Bare
end YM.XSpace
