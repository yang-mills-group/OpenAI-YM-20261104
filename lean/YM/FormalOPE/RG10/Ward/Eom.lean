import YM.FormalOPE.RG10.Ward.Meet

/-!
# Extend finite Ward identities to the inversion regulator

Unmasked orbit-Haar Ward tests in genuine `energy/2` normalization. In particular the variation
under the tree determinant isn't assumed to vanish nor do we use a gauge-fixed equation as if it
were the physical `energy` equation. `preExpectation` is ONLY the auxiliary inversion regulator
of the formal program.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.InversionWard
open Gauge Lattice RG Wilson MeasureTheory Metric Finset
open PertExtension PertExtension.Orb Function Filter
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {n : Side} (hn : Even n.val) (b : Edge (Site n))
    {f : Config G n → ℝ} {X : Config G n → G.Color} (hX : Proxy X)
local notation "dirs" => WardBin.dirs
local notation "μ" => Chart.physical G (OEdge n)

lemma proxy_density (g : ℝ) : Proxy (preDensity (G:=G) (n:=n) g) := by
  apply Proxy.after (f:=invoice (G:=G) (n:=n)) invoice_proxy (fun x : ℝ => Real.exp (-x/g^2))
  exact Real.contDiff_exp.comp (contDiff_id.neg.div_const _)

private lemma lift_tegrable (f : Config G n→ℝ) (h : Continuous f) : Integrable (fun A=> f (liftLinks A)) μ :=
  (h.comp liftlinks_cont).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma integrable_pre (hf : Proxy f) (g : ℝ) : Integrable (fun A=> f (liftLinks A) * preDensity g (liftLinks A)) μ :=
  lift_tegrable _ (hf.mul (proxy_density g)).cont
lemma pre_sum {I : Type*} (s : Finset I) (f : I → Config G n → ℝ) (hf : ∀ i∈s, Proxy (f i)) (g:ℝ) :
    preNum (∑ i∈s, f i) g = ∑ i∈s, preNum (f i) g := by
  unfold preNum; simp_rw [Finset.sum_apply, Finset.sum_mul]; apply integral_finsetSum; exact fun i hi => integrable_pre (hf i hi) _
lemma expectation_sum {I : Type*} (s : Finset I) (f : I → Config G n → ℝ) (hf : ∀ i∈s, Proxy (f i)) :
    preExpectation (∑ i∈s, f i) = ∑ i∈s, preExpectation (f i) := by
  funext g; unfold preExpectation; rw [pre_sum s f hf g, Finset.sum_apply, Finset.sum_div]

section ByParts

private lemma keeps (g : G.El) (h : Continuous f) (u : ∀ A : Antes G n, push b g (liftLinks A) = liftLinks (matchEdge b g A)) :
    ∫ A : Antes G n, f (push b g (liftLinks A)) ∂μ = ∫ A, f (liftLinks A) ∂μ := by
  simp_rw [u]
  let φ := matchEdge b g
  let F := f ∘ liftLinks
  have he : Measure.map φ μ = μ := (preserves b g).map_eq
  have hi := integral_map (preserves b g).measurable.aemeasurable (f:=F)
    (by rw [show Measure.map (matchEdge b g) μ = μ from he]; exact (h.comp liftlinks_cont).aestronglyMeasurable)
  rw [(preserves b g).map_eq] at hi
  exact hi.symm

lemma Proxy.reply (h : Proxy f) (a : G.Color) : Proxy fun U => vary b f U a := (h.proxy_vary b).after
  _ (ContinuousLinearMap.apply ℝ ℝ a).contDiff

include hn in
lemma beforeHaar (h : Proxy f) (a : G.Color) :
    (∫ A, vary b f (liftLinks A) a ∂μ) = 0 := by
  let q (t : ℝ) (A : Antes G n) := f (tilt b (liftLinks A) (t • a))
  let y : Config G n → ℝ := fun U => vary b f U a
  let D (t : ℝ) (A : Antes G n) := y (tilt b (liftLinks A) (t • a))
  have hq (t : ℝ) : Integrable (q t) μ := lift_tegrable _ (h.cont.comp (step_cont b _))
  have ht t : ∫ A : Antes G n, q t A ∂μ = ∫ A, f (liftLinks A) ∂μ :=
    keeps b (G.lieExp (t • a)) h.cont (fun _ => lift_pair hn ..)
  have hy : Continuous y := (h.reply b a).cont
  obtain ⟨C,hC⟩:= isCompact_univ (X:=Config G n) |>.exists_bound_of_continuousOn hy.continuousOn
  obtain ⟨hu,hd⟩:= hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F:=q) (s:=Set.univ) (F':=D) (x₀:=0) («μ»:=μ) (bound:=fun (_ : Antes G n) => C) univ_mem
    (.of_forall fun t => (hq t).1) (hq 0)
    ((hy.comp ((step_cont b _).comp liftlinks_cont)).aestronglyMeasurable)
    (.of_forall (fun U t _ => hC _ (Set.mem_univ _)))
    (integrable_const _) (.of_forall fun U t _ => h.tangent b (liftLinks U) a t)
  simp_rw [ht] at hd
  simpa only [D, y, zero_smul, home] using hd.unique (hasDerivAt_const ..)

private lemma dens_deriv (U : Config G n) (g : ℝ) (a : G.Color) :
    vary b (preDensity g) U a = preDensity g U * (-(vary b invoice U a)/g^2) := by
  have hi := (((invoice_proxy (G:=G)).derivative b U a).neg.div_const (g^2)).exp
  apply ((proxy_density g).derivative b U a).unique
  simpa only [preDensity, invoice, Pi.neg_apply, zero_smul, home] using hi

include hn in
lemma numHaar {g : ℝ} (hg : g ≠ 0) (h : Proxy f) (a : G.Color) :
    preNum (fun U => f U * vary b invoice U a) g = g^2 * preNum (fun U => vary b f U a) g := by
  have he (U : Config G n) : (vary b (f*preDensity g) U a) =
      (vary b f U a) * preDensity g U - (g^2)⁻¹ * (f U * (vary b invoice U a) * preDensity g U) := by
    have hv := leibniz b h (proxy_density g) U (fun _ => a)
    unfold coupled at hv; rw [hv, dens_deriv]; ring -- may need div_eq?
  have hi := beforeHaar hn b (h.mul (proxy_density g)) a
  simp_rw [he] at hi
  rw [integral_sub (integrable_pre (h.reply b a) g)
    ((integrable_pre (f:=fun U => f U * vary b invoice U a) (h.mul (invoice_proxy.reply b a)) g).const_mul (g^2)⁻¹), integral_const_mul] at hi
  have hi' : preNum (fun U => vary b f U a) g - (g^2)⁻¹ * preNum (fun U => f U * vary b invoice U a) g=0:=hi
  rw [sub_eq_zero] at hi'; rw [hi', mul_inv_cancel_left₀ (pow_ne_zero 2 hg)]

include hX hn

private lemma vertex (i : G.ColorIndex) {g : ℝ} (hg : g ≠ 0) (hf : Proxy f) :
    let x := dirs G i
    let L := fun U => Inner.inner ℝ x (X U)
    let C : G.Color := x
    preNum (fun U => L U * vary b invoice U C * f U) g =
      g^2 * (preNum (fun U => vary b L U C * f U) g + preNum (fun U => L U * vary b f U C) g) := by
  intro x L c
  have hp : Proxy L := hX.after _ (innerSL ℝ x).contDiff
  let j (U : Config G n) := vary b L U c * f U
  let k (U : Config G n) := L U * vary b f U c
  have he : (fun U => vary b (L*f) U c) = j+k := funext (fun U => leibniz b hp hf U (fun _=>c))
  have hr : preNum (j+k) g = preNum j g+preNum k g := by
    unfold preNum; simp_rw [Pi.add_apply,add_mul]
    exact integral_add (integrable_pre ((hp.reply b c).mul hf) g) (integrable_pre (hp.mul (hf.reply b c)) g)
  have hx := numHaar hn b hg (hp.mul hf) c
  rw [show (fun U => L U * vary b invoice U c * f U) = _ from
    funext (fun U => (show _ = (L*f) U * vary b invoice U c from mul_right_comm ..)), hx, he]; exact congr_arg _ hr

/-- Exact orbit Wilson Ward identity. The test on RHS is the contact mark on the whole product. -/
theorem orbit_IBP {g : ℝ} (hg : g ≠ 0) (hf : Proxy f) :
    preExpectation (effort b X * f) g = g^2 *
      (preExpectation (fallout b X * f) g + preExpectation (coupled b X f) g) := by
  let L := fun i U => Inner.inner ℝ (dirs G i) (X U)
  let u := fun i (U : Config G n) => L i U * vary b invoice U (dirs G i) * f U
  let v := fun i (U : Config G n) => vary b (L i) U (dirs G i) * f U
  let w := fun i (U : Config G n) => L i U * vary b f U (dirs G i)
  have hp (i : G.ColorIndex) : Proxy (L i) := hX.after _ (innerSL ℝ (dirs G i)).contDiff
  have hu : effort b X * f = ∑ i, u i := by
    funext U; rw [Finset.sum_apply, Pi.mul_apply, effort, coupled_components, Finset.sum_mul]; rfl
  have hv : fallout b X * f = ∑ i, v i := by
    funext U; rw [Finset.sum_apply, Pi.mul_apply, fallout_deriv b hX, Finset.sum_mul]
  have hw : coupled b X f = ∑ i, w i := by funext U; rw [Finset.sum_apply, coupled_components]; rfl
  have HH : ∑ i, preNum (u i) g = g^2 *((∑ i, preNum (v i) g)+ ∑ i, preNum (w i) g) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => vertex hn b hX i hg hf
  simp only [preExpectation]; rw [hu,hv,hw, pre_sum _ u (fun i _ => (Proxy.mul ((hp i).mul
    (invoice_proxy (G:=G) (n:=n) |>.reply b _)) hf : Proxy (u i))), pre_sum _ v (fun i _ =>
    (Proxy.mul ((hp i).reply b _) hf : Proxy (v i))), pre_sum _ w (fun i _ =>
      ((hp i).mul (hf.reply b _) : Proxy (w i))), HH]; ring
end ByParts
end YM.FormalOPE.RG10.InversionWard
