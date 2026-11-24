import YM.Comparison.RG02.Normal.Felt
/-!
# Per-U marker and conditional expectation, higher-log exact identity

 Keep t among *inputs*. Actual conditioning at fixed coarse J. Even if watercolors admit
 nonlocal disagreements/forced corrections, all marker products pass through one joint
 probability. At any fixed period. Nothing here permits charging these table moments by
 declaring polynomials are uniform in volume or `W` globally regular analytic. Use the
 earlier disjoint-support cumulant and joint Wick rules on any auxiliary representative;
 must re-express exactly before switch to this or Fk. The overlap laws do not presume
 that tagged predictor noise factorizes on disjoint spatial subgraphs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Normal
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree YM.Push.SectorMeasure
open YM.Marker YM.Multi Order Integral Actual Cumulants
open YM.Extra.Trajectories (connected connected_quiet pass_connected)
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff ENNReal
variable {G : Gauge} {c f : Side} (S : StepData c f) (β : ℝ) (J : Config G c) (t : S.Choices)
  {V : Type} [DecidableEq V] {R : Census V}
  (X : Lit R (Config G f)) (Z : S.Choices→Lit R (Config G f)) (W : Config G f→ℝ)

def hue := charge (prior G f) (Actual.stack t J β X)
def scan := ∑ t:S.Choices,hue S β J t (Z t)
abbrev Clear (X : Lit R (Config G f)) := ∀ i,(X i).part R.quiet=(W i:ℂ)

variable (H : Strong f W) (ok : S.patch.Branches S.kernel G)
include H ok
omit H ok in
lemma hue_quiet (h : Clear W X) : (hue S β J t X).part R.quiet=mass S β J t W := by
   unfold hue mass; rw [components]; unfold Actual.stack atMark; simp_rw [Poly.part_smul,h,← Complex.ofReal_mul]; exact integral_ofReal
lemma scan_bare (h : ∀ t, Clear W (Z t)) : (scan S β J Z).part R.quiet=Complex.ofReal (total S β J W) := by unfold scan; rw [Poly.part_sum, ← mass_total S β J W H ok]; simp_rw [fun t=>hue_quiet S β J t _ _ (h t),Complex.ofReal_sum]
omit H in
lemma scan_actual (h : Leaf.All X) : scan S β J (fun _=>X)=Actual.Push S β X J := (agreed _ _ ok h).symm

def light := fun y:Config G f=>unitScale (X y)
omit ok in
lemma lit_up (v : Config G f) (h : Clear W X) : W v • light X v=X v := by
   rw [← Complex.coe_smul, ← h v]; exact scale_value (by rw [h v]; exact_mod_cast (H.positive v).ne')

-- `moment` ordinary. Exp packing at a pinned t only to read the actual probability;
-- marker cumulants in the full Actual are not a tag-wise log.
local notation "dμ" => index S β J t W
local notation "ρ"=>light X

omit ok in
lemma light_one (v : Config G f) (h : Clear W X) : (light X v).part R.quiet=1 := unitScore (by rw [h v]; exact_mod_cast (H.positive v).ne')

omit ok in
lemma light_env (h : Clear W X) (hm : Leaf.All X) : Leaf.All (light X) := by
  unfold light Order.unitScale; simp_rw [h,← Complex.ofReal_inv]; exact Leaf.smul (Envelope.ofReal_env H.inv_env) hm
lemma light_part (h : Clear W X) (hm : Leaf.All X) : Good dμ ρ := by
   letI := probability S β J t W H ok; exact Good.of_bound _ (light_env X W H h hm) -- include args?

private lemma of_effort (h : Clear W X) (hm : Leaf.All X) :
    Complex.ofReal (mass S β J t W) • charge dμ ρ= hue S β J t X := by
   have he := light_part S β J t X W H ok h hm
   ext i; unfold hue; rw [Poly.part_smul, components,components,← Complex.real_smul, at_mass S β J t W H ok _ (he i)]
   refine integral_congr_ae (Eventually.of_forall (fun x=>?_))
   dsimp only; unfold view; rw [mul_smul]; unfold Actual.stack atMark
   rw [Poly.part_smul]; simp_rw [Complex.real_smul]; exact congrArg ( (↑(taggedKernel S β t x J):ℂ) *·)
     ( show (↑(W x):ℂ)*(ρ x).part i=_ from Eq.trans (Poly.part_smul ..).symm (congrArg (Poly.part · i) (by rw [Complex.coe_smul]; exact lit_up X W H x h)))

lemma normalized_tag (h : Clear W X) (hm : Leaf.All X) : charge dμ ρ= Order.unitScale (hue S β J t X) := by
   rw [unitScale,hue_quiet S β J t X W h,← of_effort S β J t X W H ok h hm, smul_smul, inv_mul_cancel₀ (show (↑(mass S β J t W):ℂ)≠0 by exact_mod_cast (mass_pos S β J t W H ok).ne'),one_smul]
def tilted := fun v : S.Choices=> Complex.ofReal (sale S β J v W)
lemma tilted_sum : ∑ v, tilted S β J W v=1 := by unfold tilted; rw [← Complex.ofReal_sum, sale_lit S β J W H ok,Complex.ofReal_one]

lemma scans (h : ∀ t, Clear W (Z t)) (hm : ∀ t, Leaf.All (Z t)) :
    Order.unitScale (scan S β J Z)= Cumulants.mix (tilted S β J W) (fun t=>charge (index S β J t W) (light (Z t))) := by
   rw [Order.unitScale, scan_bare S β J Z W H ok h]; unfold mix scan
   rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro i _; rw [← of_effort S β J i _ W H ok (h i) (hm i),smul_smul]; unfold tilted sale; rw [Complex.ofReal_div,div_eq_mul_inv,mul_comm]

variable [Fintype V]
def symbol := fun a : Hot R=> fun y => (connected (light X y)).part a.val
omit ok in
lemma symbol_env (h : Clear W X) (hm : Leaf.All X) : ∀ a, Envelope (symbol X a) := by
   let e:=fun x:Config G f=> unipotentLog (light X x)
   have hi : Leaf.All e := by
       apply Leaf.sum; intro i; apply Leaf.smul (Leaf.atom ..); exact Leaf.pow (leaf_sub (Leaf.save _) (light_env X W H h hm)) _ -- unif args
   unfold symbol; simp_rw [fun i=> log_formula (light_one X W H i h)]; exact fun x=> hi x.val
lemma hue_driven (h : Clear W X) (hm : Leaf.All X) :
    charge dμ ρ=driven (fun g:Config G f→ℂ=> ∫ x,g x ∂dμ) (symbol X) := by
   letI := probability S β J t W H ok; ext i; rw [components, driven_part]
   have he := fun k=> pass_connected (light_one X W H k h)
   have hp (x : Config G f) := pass_partition (connected (light X x)) (connected_quiet (light_one X W H x h)) i
   simp_rw [he] at hp; simp_rw [Finset.prod_apply]
   unfold atMark; simp_rw [hp]; rw [integral_finsetSum]; rfl
   exact fun j _=> (Envelope.prodC j.val (symbol X) (fun i _=> symbol_env X W H h hm i)).integrableC _
lemma normalized_driven (h : ∀ t, Clear W (Z t)) (hm : ∀ t, Leaf.All (Z t)) :
    Order.unitScale (scan S β J Z) = driven (assign S β J W) (fun i v=>symbol (Z v) i) := by
   rw [scans S β J Z W H ok h hm]; simp_rw [fun t=>hue_driven S β J t _ W H ok (h t) (hm t)]
   rw [mix_driven]; congr 1
-- any products can be used above by virtue of this:
lemma colored_good (h : ∀ t, Clear W (Z t)) (hm : ∀ t, Leaf.All (Z t)) (A : Finset (Hot R)) :
    Integrable (fun x=> ∏ i∈A,symbol (Z t) i x) dμ := by
   letI:= probability S β J t W H ok
   exact (Envelope.prodC _ _ (fun i _=> symbol_env (Z t) W H (h t) (hm t) i)).integrableC _

-- joint connected log, may also use `Cumulants.total_log` on tagged mix expansion.
def normalized_connected := connected (Order.unitScale (scan S β J Z))
lemma higher_protocol (h : ∀ t, Clear W (Z t)) (hm : ∀ t, Leaf.All (Z t)) (q : R.Mode) :
    (normalized_connected S β J Z).part q=∑ i∈shards R q, (connected (moments (parts R) (assign S β J W)
      (fun i t=> symbol (Z t) i))).part i := by
   let q' := Order.unitScale (scan S β J Z)
   have he : (q').part R.quiet=1 := unitScore (by rw [scan_bare S β J Z W H ok h]; exact_mod_cast (total_pos S β J W H ok).ne')
   rw [normalized_connected, normalized_driven S β J Z W H ok h hm]
   apply log_driven; change (Order.unitScale _).part _=1 at he; rw [normalized_driven S β J Z W H ok h hm, driven_quiet] at he; exact he
end YM.Comparison.RG02.Normal
