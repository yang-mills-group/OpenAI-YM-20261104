import YM.Work.A16
import YM.EveryPhase.DerivativeHelpers
import YM.Work.C16
import YM.Work.C17
import YM.Work.C19
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation
/-!
# Real Jost support chart over the entire spacelike-convex-relative-hull criterion

Path VALID on a single complex neighborhood (tubular portion) and endpoint
on an ambient complex neighborhood (including real tests). Chosen *before* phases
or scaling. Use back to the relative adaptation on the joint real Minkowski boundary.
No assumption about the test radius or time order of Euclidean cluster maps here.
Shares ideas and private lemmas (reproduced in part) with the Work.C17/C19 panes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GapsContact.Jost
open Function Filter Set Mink Mink.Poincare Boundary Boundary.Surface Bid
open scoped Topology ContDiff InnerProductSpace Classical Pointwise
variable {n:ℕ}

lemma northern_add {x y:E4}(hx:x∈cone)(hy:y∈cone) : x+y∈cone:=by
  change ‖spatial _‖≤YM.time _; rw [rest_add,clock_add]; exact (norm_add_le ..).trans (add_le_add hx hy)
lemma northern_mul {x:E4}{r:ℝ}(hx:x∈cone)(hr:0≤r): r • x∈cone:=by
  change ‖spatial _‖≤YM.time _; rw [rest_mul,clock_mul,norm_smul,Real.norm_of_nonneg hr]; exact mul_le_mul_of_nonneg_left hx hr
lemma convex_north : Convex ℝ cone:=fun _ ha _ hb _ _ hx hy _=> northern_add (northern_mul ha hx) (northern_mul hb hy)
private lemma add_into {x y : E4} {r : ℝ} (hx : x ∈ cone) (hy : y ∈ inside) (hr : 0 < r) :
    x + r • y ∈ inside := by
  change ‖spatial _‖ < time _
  rw [rest_add, clock_add, rest_mul, clock_mul]; refine lt_of_le_of_lt (norm_add_le _ _) ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]; exact add_lt_add_of_le_of_lt hx (mul_lt_mul_of_pos_left hy hr)
lemma convex_inside : Convex ℝ inside:=by
    intro u ha w hb r s hx hy he
    rcases lt_or_eq_of_le hy with hh | hh
    · exact add_into (northern_mul (x:=u) (show ‖spatial u‖ ≤ YM.time u from (show ‖spatial u‖ < _ from ha).le) hx) hb hh
    rw [← hh, zero_smul, add_zero]; simp only [←hh,add_zero] at he; rwa [he, one_smul]

lemma timelike_barrier {K : Set E4}(hc:IsCompact K) (hv:Convex ℝ K)(h:Disjoint K cone):
    ∃ b∈inside, ∀ x∈K, inner ℝ b x < 0 :=by
  obtain ⟨f,u,v,he,hu,ha⟩:= geometric_hahn_banach_compact_closed hv hc convex_north closed_cone h
  have hv0: v<0 := (ha _ (show (0:E4)∈cone from by simp[cone])).trans_eq (map_zero f)
  let b:= (InnerProductSpace.toDual ℝ E4).symm f; have hb (x:E4): inner ℝ b x=f x:=InnerProductSpace.toDual_symm_apply
  have h0 : b∈cone :=by
     rw [cone_test]; intro x hx; rw [hb]; by_contra! hh
     have hp:0<v/f x:=div_pos_of_neg_of_neg hv0 hh
     have H:=ha _ (northern_mul hx hp.le); rw [map_smul,smul_eq_mul,div_mul_cancel₀ _ hh.ne] at H; exact lt_irrefl _ H
  obtain ⟨T,hT⟩:= hc.bddAbove_image clock_cont.continuousOn
  have hx0:= hu.trans hv0
  let B:=|T|+1; have hB:0<B:=by unfold B; positivity
  let r:=-u/B; have hr:0<r:=div_pos (neg_pos.mpr hx0) hB
  refine ⟨b+r • basis timeAxis,add_into h0 (by simp[inside]) hr,fun x hx=>?_⟩
  rw [inner_add_left, real_inner_smul_left,basis_inner,hb]; change f x+r*YM.time x<0
  have hv : YM.time x ≤ B:= (hT (mem_image_of_mem _ hx)).trans ((le_abs_self _).trans (lt_add_one _).le)
  have hf:=he x hx; have hh:= mul_le_mul_of_nonneg_left hv hr.le; rw [show r*B=-u from div_mul_cancel₀ _ hB.ne'] at hh; linarith only [hh,hf]

lemma gate (K:Set E4) (ha:IsCompact K)(hc:Convex ℝ K)(h:Disjoint K cone)(hv:Disjoint K (-cone)):
    ∃ g:Lorentz,∃ e:Mink.Ray,∀ x∈ K,e.crossT (g.act x)∈ inside:=by
  by_cases he: K.Nonempty
  swap; exact ⟨1,Ray.fromAxis 0,fun x hx=> (he ⟨x,hx⟩).elim⟩
  obtain ⟨b,hb,hx⟩:=timelike_barrier ha hc h
  have hn: Disjoint (-K) cone:= Set.disjoint_left.mpr fun x hx hX=> Set.disjoint_left.mp hv hx (Set.mem_neg.mpr (by simpa using hX))
  obtain ⟨c,hc,hY⟩:=timelike_barrier ha.neg hc.neg hn
  obtain ⟨g,-,hg⟩:= Work.A16.exists_rest_finset b hb Finset.univ
  have hz:spatial (g.act b)=0:=PiLp.ext (fun i=> hg i (Finset.mem_univ i))
  let v:= g.dual.act; let a:=g.act b; let b:=g.act c
  have ht:0< YM.time a:= (strict_self a|>.mp ((g.stays ..).mpr hb)).1
  have h1: ‖spatial b‖< YM.time b:= (g.stays ..).mpr hc
  have hp(x:E4)(hs:x∈K): YM.time (v x)<0:=by
     have hh: inner ℝ a (v x)<0:= (g.dual_sent x _).trans_lt (hx x hs) -- args check
     rw [pairing, show spatial a=0 from hz, inner_zero_left,zero_add] at hh; exact neg_of_mul_neg_right hh ht.le
  have hm(x:E4)(hK:x∈K):0 < inner ℝ b (v x):=by
     have H:=hY (-x) (neg_mem_neg.mpr hK); rw [inner_neg_right, Left.neg_neg_iff] at H; exact H.trans_eq (g.dual_sent x _).symm
  have hB:0 < ‖spatial b‖:=by
     by_contra! H
     have hN:spatial b=0:= norm_eq_zero.mp (le_antisymm H (norm_nonneg _))
     obtain ⟨x,hX⟩:=he
     have hf:= hm x hX; rw [pairing,hN,inner_zero_left,zero_add] at hf
     exact hf.not_ge ((mul_neg_of_pos_of_neg ((norm_nonneg _).trans_lt h1) (hp x hX)).le)
  let e: Ray:=⟨‖spatial b‖⁻¹ • spatial b,by rw [norm_smul, Real.norm_of_nonneg (by positivity),inv_mul_cancel₀ hB.ne']⟩
  refine ⟨g.dual,e,fun x hX=>?_⟩
  change ‖spatial (e.crossT (v x))‖ < _; rw [e.liesT,e.ticksT,norm_smul,e.property,mul_one]
  have hh:= hp x hX; have hf:= hm x hX; rw [pairing] at hf
  change _ < inner ℝ (spatial (v x)) (‖spatial b‖⁻¹ • spatial b)
  rw [real_inner_smul_right,Real.norm_eq_abs,abs_of_neg hh, real_inner_comm,← div_eq_inv_mul,lt_div_iff₀ hB]; nlinarith only [mul_lt_mul_of_neg_right h1 hh,hf] -- nlin

abbrev Steps (n:ℕ):= {i: Fin n × Fin n // i.1.val+1=i.2.val}
def leg (p:Points n)(i:Steps n):E4:= p i.val.2-p i.val.1
def cusp (p:Points n):= convexHull ℝ (Set.range (leg p))
-- Disallow both nonfuture & nonpast failures, incl producing zero
-- Include arity 0-1: true.
def jost (n:ℕ):= {x:Points n| Disjoint (cusp x) cone ∧ Disjoint (cusp x) (-cone)}
lemma beam {x:Points n}(hx:x∈ jost n): ∃ g:Lorentz,∃ r:Ray,∀ i j:Fin n,i.val+1=j.val → r.crossT (g.act (x j-x i))∈inside :=by
  obtain ⟨g,e,h⟩:=gate (cusp x) ((Set.finite_range _).isCompact_convexHull ℝ) (convex_convexHull ..) hx.1 hx.2
  exact ⟨g,e,fun i j hi=> h _ (subset_convexHull _ _ (Set.mem_range.mpr ⟨⟨(i,j),hi⟩,rfl⟩))⟩ -- coercion h'?
-- reuse C17 neighbourhood factoring and C19 realizations of complex-linear rotations (private there)
open Complex
private lemma shade_at (x : Full n) (i a) : shade x i a = (x (i,a)).im := rfl
private lemma glow_at (x y : Points n) (i a) : glow x y (i,a) = ↑(x i a) + ↑(y i a)*I := rfl

private lemma shade_augment (e : Ray) (b : ℝ) (x : Full n) (i : Fin n) :
    shade (augment e (↑b*I) x) i = shade x i + (Real.sin b) • e.crossT (reality x i) +
      (Real.cos b-1) • e.scalesT (shade x i) := by
  ext a
  simp [shade_at, augment, glow_at, Complex.sinh_mul_I, Complex.cosh_mul_I, Complex.mul_im,
    Complex.sin_ofReal_re, Complex.cos_ofReal_re]

private lemma shade_diff_augment (e : Ray) (b : ℝ) (x : Full n) (i j : Fin n) :
    shade (augment e (↑b*I) x) j - shade (augment e (↑b*I) x) i =
      (shade x j - shade x i) + (Real.sin b) • e.crossT (reality x j - reality x i) +
      (Real.cos b-1) • e.scalesT (shade x j - shade x i) := by
  simp only [shade_augment, map_sub, smul_sub]
  abel

/-- Small-angle neighbourhood argument for ordered boost coordinates. At
least one of the height gap and the `sin` coefficient must already point
strictly in. In the second case factor OUT `sin b`; the remaining coefficient
of `W` is `-sin/(1+cos)`, continuous near zero and zero there. So we even enter from
nearby points with merely *closed* cone gaps, for b strictly positive. Using
a single product neighbourhood keeps this uniform all the way down to zero.
-/
private lemma enters (q : Full n) (A : ℝ → Full n → Full n)
    (Y V W : Fin n → Fin n → Full n → E4) (hy : ∀ i j, Continuous (Y i j))
    (hv : ∀ i j, Continuous (V i j)) (hw : ∀ i j, Continuous (W i j))
    (hf : ∀ b p i j, shade (A b p) j - shade (A b p) i =
      (Y i j p + Real.sin b • V i j p) + (Real.cos b-1) • W i j p)
    (h0 : ∀ i j : Fin n, i.val+1=j.val → Y i j q ∈ inside ∨ V i j q ∈ inside) :
    ∀ᶠ p : ℝ × Full n in 𝓝 (0,q), 0<p.1 → shade (A 0 p.2) ∈ shores n → A p.1 p.2 ∈ tube n := by
  let a : ℝ × Full n := (0,q)
  have He : ∀ᶠ p in 𝓝 a, ∀ i j : Fin n, i.val+1=j.val → 0<p.1 → Y i j p.2 ∈ cone →
      shade (A p.1 p.2) j - shade (A p.1 p.2) i ∈ inside := by
    refine eventually_all.mpr fun i => eventually_all.mpr fun j => ?_
    by_cases hij : i.val+1=j.val
    · rcases h0 i j hij with hh|hh
      · let d (p : ℝ × Full n) := shade (A p.1 p.2) j - shade (A p.1 p.2) i
        have hd : Continuous d := by
          unfold d; simp_rw [hf]; fun_prop
        have hn : d a ∈ inside := by simpa [d,a,hf] using hh
        filter_upwards [(hd.tendsto a).eventually (open_inside.mem_nhds hn)] with p hp using
          fun _ _ _ => hp
      · let D (p : ℝ × Full n) := 1+Real.cos p.1
        let d (p : ℝ × Full n) := V i j p.2 + (-Real.sin p.1 / D p) • W i j p.2
        have hD : D a ≠ 0 := by norm_num [D,a]
        have hC : Continuous D := by unfold D; fun_prop
        have hd : ContinuousAt d a := by
          unfold d; fun_prop (disch := assumption)
        have hn : d a ∈ inside := by simpa [a,d] using hh
        have ht : a.1 < Real.pi := Real.pi_pos
        filter_upwards [hd.eventually (open_inside.mem_nhds hn),
          (continuous_fst.tendsto a).eventually (gt_mem_nhds ht),
          (hC.tendsto a).eventually (eventually_ne_nhds hD)] with p hp ht' hD'
        intro _ hb hy'
        have hr : 0 < Real.sin p.1 := Real.sin_pos_of_pos_of_lt_pi hb ht'
        have hw' : Real.sin p.1 * (-Real.sin p.1 / D p) = Real.cos p.1 - 1 := by
          change D p ≠ 0 at hD'
          rw [← mul_div_assoc, div_eq_iff hD']
          unfold D
          linarith [Real.sin_sq_add_cos_sq p.1]
        have h := add_into hy' (show d p ∈ inside from hp) hr
        rwa [hf, ← hw', mul_smul, add_assoc, ← smul_add]
    exact Eventually.of_forall (fun _ h => False.elim (hij h))
  filter_upwards [He] with p hp
  intro hh hj
  simp only [tube, mem_preimage, shores, fields, mem_iInter, mem_setOf] at hj ⊢
  intro i j hij
  apply hp i j hij hh
  simpa only [hf, Real.sin_zero, Real.cos_zero, sub_self, zero_smul, add_zero] using hj i j hij
/- Complex-linear maps on Full, including the complex boost at *fixed*
rapidity and the change of names. Careful: `reality` and `shade`
individually are only real-linear. -/

private lemma reality_add (x y : Full n) :
    reality (x + y) = reality x + reality y := by
  apply Points.flatten.injective
  ext i
  simp [reality]

private lemma shade_add (x y : Full n) :
    shade (x + y) = shade x + shade y := by
  apply Points.flatten.injective
  ext i
  simp [shade]

private lemma reality_smul (c : ℂ) (x : Full n) :
    reality (c • x) = c.re • reality x - c.im • shade x := by
  apply Points.flatten.injective
  ext i
  simp [shade, reality]

private lemma shade_smul (c : ℂ) (x : Full n) :
    shade (c • x) = c.re • shade x + c.im • reality x := by
  apply Points.flatten.injective
  ext i
  simp [shade, reality]

private lemma glow_ext {x y : Full n} (h : reality x = reality y)
    (k : shade x = shade y) : x = y :=
  (valley x).symm.trans (by rw [h, k, valley])

private def complexMap (A : Points n →ₗ[ℝ] Points n) : Full n →L[ℂ] Full n :=
  LinearMap.toContinuousLinearMap
    { toFun x := glow (A (reality x)) (A (shade x))
      map_add' x y := by
        apply glow_ext <;> simp [reality_add, shade_add]
      map_smul' c x := by
        apply glow_ext <;> simp [reality_smul, shade_smul] }

private def blocks (A : E4 →L[ℝ] E4) : Points n →ₗ[ℝ] Points n where
  toFun x := points fun i => A (x i)
  map_add' x y := PiLp.ext fun i => map_add A (x i) (y i)
  map_smul' c x := PiLp.ext fun i => map_smul A c (x i)

lemma analytic_augment (e : Ray) (z : ℂ) (x : Full n) :
    AnalyticAt ℂ (augment e z) x := by
  let U : Full n →L[ℂ] Full n := ContinuousLinearMap.id ℂ _ +
    Complex.sinh z • complexMap (blocks e.crossT) +
    (Complex.cosh z - 1) • complexMap (blocks e.scalesT)
  have h : augment e z = ⇑U := rfl
  rw [h]
  exact U.analyticAt x

lemma analytic_boost_path (e : Ray) (x : Full n) (z : ℂ) :
    AnalyticAt ℂ (fun w => augment e w x) z :=
  (analyticAt_const.add (Complex.analyticAt_sinh.smul analyticAt_const)).add
    ((Complex.analyticAt_cosh.sub analyticAt_const).smul analyticAt_const)

/- The change of names must intertwine the action also for the *tilted*
pane. We need this identity only at real rapidities. -/

lemma augment_real (e : Ray) (t : ℝ) (x : Full n) :
    augment e (↑t) x = rect (e.boost t) x := by
  apply glow_ext
  · simp only [augment, reality_add, reality_smul, sinh_ofReal_im, sinh_ofReal_re,
      sub_im, sub_re, cosh_ofReal_im, cosh_ofReal_re, one_re, one_im, sub_zero,
      zero_smul, rect, re_glow]
    ext1 i
    simp [Ray.shift]
  · simp only [augment, shade_add, shade_smul, sinh_ofReal_im, sinh_ofReal_re,
      sub_im, sub_re, cosh_ofReal_im, cosh_ofReal_re, one_re, one_im, sub_zero,
      zero_smul, add_zero, rect, im_glow]
    ext1 i
    simp [Ray.shift]

def straighten (g:Lorentz) :Full n →L[ℂ] Full n := complexMap (togetherL g n).toLinearEquiv.toLinearMap
@[simp] lemma straighten_rect (g:Lorentz)(x:Full n):straighten g x=rect g x:=rfl
@[simp] lemma shade_scale (z:Full n)(r:ℝ):shade ((r:ℂ) • z)=r • shade z:=by rw [shade_smul]; simp
def curve (g:Ray)(p:ℂ):Full n →L[ℂ] Full n := ContinuousLinearMap.id ℂ _ +
    Complex.sinh p • complexMap (blocks g.crossT) +
    (Complex.cosh p - 1) • complexMap (blocks g.scalesT)
@[simp] lemma curve_augments (g:Ray)(p:ℂ)(x:Full n) : curve g p x=augment g p x:=rfl
lemma rect_open (g:Lorentz)(l:Full n)(hl:l∈tube n):rect g l∈tube n:=by
  exact Work.C16.rect_mem_tube g hl
lemma convex_tube (n): Convex ℝ (tube n):=by
  let L : Full n →ₗ[ℝ] Points n :=
    { toFun := shade
      map_add' := shade_add
      map_smul' := fun r x=> by simpa only [RingHom.id_apply,Complex.coe_smul] using shade_scale x r }
  apply Convex.linear_preimage (s:=fields n) _ L
  apply convex_iInter; intro i; apply convex_iInter; intro j; apply convex_iInter; intro _
  exact convex_inside.linear_preimage
      ((PiLp.projₗ (𝕜:=ℝ) 2 (fun _ : Fin n => E4) j)-(PiLp.projₗ (𝕜:=ℝ) 2 (fun _ : Fin n => E4) i))

def reach (g:Lorentz)(r:Ray)(b:ℝ) : Full n →L[ℂ] Full n := (curve r ((b:ℂ)*I)).comp (straighten g)

structure Scheme (n:ℕ) where
  g : Lorentz
  e : Ray
  speed : ℝ
  armed : 0<speed
  zone : Set (Full n)
  clear : IsOpen zone
  arch : Convex ℝ zone
  fits : MapsTo (reach g e speed) zone (tube n)
  onto : ∀ z, z∈ zone → z ∈ tube n → ∀ b∈ Icc 0 speed, reach g e b z∈tube n
  starts : (zone∩tube n).Nonempty
lemma closure_tube (z:Full n)(h:shade z∈shores n) : z∈closure (tube n):=by
   -- towards_shore imported? easier restrict z real
   haveI := YM.Next.BOUNDARY.towards_shore h
   apply mem_closure_of_tendsto (x:=z) (f:=fun i=>glow (reality z) i) (b:=(𝓝[fields n] shade z)) ?_
   · filter_upwards [self_mem_nhdsWithin] with t ht; exact show shade _∈fields n from im_glow _ _ ▸ ht
   exact (Continuous.tendsto' (show Continuous (fun i=>glow (reality z) i) from (home n).comp (continuous_const.prodMk continuous_id)) _ _ (valley z)).mono_left nhdsWithin_le_nhds

lemma Scheme.find (x:Points n)(hx:x∈ jost n):∃ Z:Scheme n,glow x 0∈ Z.zone:=by
   obtain ⟨g,e,hg⟩:= beam hx
   let p:=glow x 0
   let A (b:ℝ)(w:Full n):= reach g e b w
   have he (p:Full n):A 0 p=rect g p:=by simp [A,reach,augment]
   let Y (i j : Fin n) (w:Full n):=shade (straighten g w) j - shade (straighten g w) i
   have h:=enters p A Y (fun i j w=> e.crossT (reality (straighten g w) j - reality (straighten g w) i))
      (fun i j w=>e.scalesT (Y i j w)) (fun i j=>by unfold Y; fun_prop) (fun i j=>by fun_prop) (fun i j=>by unfold Y; fun_prop)
      (fun b z i j=> shade_diff_augment ..) (fun i j hi=> Or.inr (?_ : _ ∈ inside))
   rotate_left
   · simpa [straighten_rect,rect,p] using hg i j hi
   obtain ⟨u,hu,V,hV,hA⟩:=mem_nhds_prod_iff.mp h
   obtain ⟨r,hr,hB⟩:=Metric.mem_nhds_iff.mp hu
   let b:= r/2; have ht : 0<b:=half_pos hr; have heq:b<r:=half_lt_self hr
   have hh (t:ℝ)(hp: t∈ Ioc 0 b)(w:Full n)(hw:w∈V)(hW:shade (rect g w)∈shores n):A t w∈tube n:=by
      apply (hA (Set.mk_mem_prod (hB (?_ : t∈ Metric.ball (0:ℝ) r)) hw)) hp.1
      · rwa [he];
      simpa [Metric.mem_ball,Real.dist_eq,abs_of_pos hp.1] using hp.2.trans_lt heq
   have hp: A b p∈tube n:= hh b ⟨ht,le_rfl⟩ p (mem_of_mem_nhds hV) (by simp [rect,p])
   obtain ⟨R,hR,hᵣ⟩:= Metric.mem_nhds_iff.mp (inter_mem (((reach g e b).continuous.tendsto p).eventually ((south n).mem_nhds hp)) hV)
   have hu (z:Full n) (hz:z∈ Metric.ball p R):A b z∈tube n∧ z ∈ V:=hᵣ hz
   have hᵤ:p∈Metric.ball p R:=Metric.mem_ball_self hR
   have hm: p∈closure (tube n):=closure_tube p (by simp[p])
   refine ⟨⟨g,e,b,ht,Metric.ball p R,Metric.isOpen_ball,convex_ball p R,fun z hz=>(hu z hz).1, ?_, mem_closure_iff.mp hm _ Metric.isOpen_ball hᵤ⟩, hᵤ⟩
   intro z hz hZ k hk
   rcases hk.1.eq_or_lt with hf|hk'
   · change A k _∈_; rw [← hf,he]; exact rect_open g z hZ
   exact hh k ⟨hk',hk.2⟩ z (hu z hz).2 (total_south n (rect_open g z hZ))
end YM.GapsContact.Jost
