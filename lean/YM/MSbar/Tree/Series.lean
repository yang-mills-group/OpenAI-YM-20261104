import YM.MSbar.Tree.Line

/-!
# Free MS correlation rule

Position dimensional subtraction at order in coupling **zero**, not counting
independent loops (e.g. pairs of quadratic fields have contributions).
Self pairs vanish by convention (scaleless; we're using uncut position
rules only for the Gaussian order). Compare on separated points; all
arities including constants. The actual answer is the MS finite part.
In this case there is a real analytic germ in epsilon and evaluation at
four is the finite part. No evanescent mixing is needed in this order.
Indeed we can use the DR formula for curl lines with all index slots open
and ordinary disjoint Wick products. Free physical labels are represented by
the basis from Lift, using jet components even at regulated d; this is enough
to specify all polynomials on the four-dimensional Maxwell on-shell and
Bianchi quotient. Includes the equation check, in four dimensions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Tree
open Function Set Filter Maxwell Tensor Analysis Wick
open scoped Classical Topology BigOperators ContDiff
open Wick.Occ
variable {G : Gauge} {n : ℕ}

def term (μ ε : ℝ) (x : Points n) (w : Wick.Powers G n) : ℂ :=
  ∑ p : Matching w, ∏ i∈ corners p, compiled μ ε i.probe (partner p i).probe
    (x i.label-x (partner p i).label)

def value (μ ε : ℝ) (x : Points n) : MultilinearMap ℂ (fun _ : Fin n => WickPol G) ℂ :=
  Multilabel.ofBasis (fun _ => Wick.monBasis G) (term μ ε x)

theorem expansion (μ ε : ℝ) (x : Points n) (f : Fin n → WickPol G) :
    value μ ε x f = ∑ i ∈ Fintype.piFinset (fun j => ((monBasis G).repr (f j)).support),
      (∏ j, (monBasis G).repr (f j) (i j)) • term μ ε x i := by
  rw [Multilabel.expansion (fun _ => monBasis G)]; congr! 4 with i
  exact Multilabel.applyBasis _ _ _

private theorem term_cd (μ ε : ℝ) (x : Points n) (hμ : 0<μ) (he : ε<1) (hx : x∈conf n) (w : Powers G n) :
    ContDiffAt ℝ ω (fun q : ℝ× Points n => term μ q.1 q.2 w) (ε,x) := by
  unfold term; apply ContDiffAt.sum; intro i _
  refine contDiffAt_prod fun j _ => ?_
  have hp (b : Fin n) : ContDiffAt ℝ ω (fun q : ℝ×Points n => q.2 b) (ε,x) := (PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin n => E4) b).contDiff.contDiffAt.comp _ contDiffAt_snd
  have hz : x j.label- x (partner i j).label ∈ Maxwell.away := sub_ne_zero.mpr ((show Injective x.ofLp from hx).ne (different i j).symm)
  exact (compiled_cd _ _ _ hμ he j.probe (partner i j).probe hz).comp _ (f:=fun q : ℝ×Points n => (q.1,q.2 _-q.2 _))
    (contDiffAt_fst.prodMk ((hp _).sub (hp _)))

lemma no_pole (μ ε : ℝ) (x : Points n) (hμ : 0<μ) (he : ε<1) (hx : x∈conf n) (v : Fin n → WickPol G) :
    AnalyticAt ℝ (fun q : ℝ× Points n => value μ q.1 q.2 v) (ε,x) := by
  simp_rw [expansion]
  refine ContDiffAt.analyticAt (ContDiffAt.sum ?_)
  intro i _
  exact (term_cd μ ε x hμ he hx i).const_smul _

def finitePart (μ : ℝ) (x : Points n) : MultilinearMap ℂ (fun _ : Fin n => WickPol G) ℂ :=
  value μ 0 x

theorem four (μ : ℝ) {x : Points n} (hx : x∈conf n) : finitePart μ x = Wick.moment G x := by
  apply Module.Basis.ext_multilinear (fun _ => monBasis G); intro i
  rw [moment_basis, show finitePart μ x (fun j=> _)=term μ 0 x i from Multilabel.applyBasis _ _ i]
  apply Finset.sum_congr rfl; intro p _; apply Finset.prod_congr rfl; intro q _
  exact compiled_four μ _ _ _ (show x q.label-x (partner p q).label∈Maxwell.away from sub_ne_zero.mpr ((show Injective x.ofLp from hx).ne (different p q).symm))

theorem eps_limit (μ : ℝ) (hμ : 0<μ) {x : Points n} (hx : x∈conf n) (p : Fin n → WickPol G) :
    Tendsto (fun ε : ℝ => value μ ε x p) (𝓝 0) (𝓝 (Wick.moment G x p)) := by
  rw [← four μ hx]
  exact (no_pole μ 0 x hμ zero_lt_one hx p).continuousAt.comp (f:=fun ε : ℝ=> (ε,x)) (show ContinuousAt (fun ε : ℝ => (ε,x)) 0 from (by fun_prop))

lemma on_shell (μ : ℝ) {x : Points n} (hx : x∈conf n) (d : Fin n → ℕ) (f : (i : Fin n)→ Labels.Label G (d i)) :
    finitePart μ x (fun i => observable G _ (f i)) = Wick.correlation G x d f := by rw [four μ hx]; rfl

lemma label_equations (μ : ℝ) {x : Points n} (hx : x∈conf n) (d : Fin n → ℕ) (f : (i : Fin n)→ Labels.Label G (d i)) (i : Fin n) (h : f i∈ equationIdeal G _) :
    finitePart μ x (fun i => observable G _ (f i))=0 := by rw [on_shell μ hx d f]; exact kills_equation _ _ f i h

end YM.MSbar.Tree
