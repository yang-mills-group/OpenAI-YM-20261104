import YM.FVAAlt2.Land
import YM.MS.Tone.Basis

/-! Real comparison of unscaled bare Wilson and ghost generators in Landau gauge.

No diagram estimates here. All radii can depend on the (admissible) inversion
torus. We prove equality on a germ so that we can then use **MS.ink**.
This also avoids making a global claim about a gauge deformation from a linear slice.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2
open Lattice Finset Pert.Orb PertExtension GaussianScore SchemeRG11.Sway Function
open MS MS.Native MS.Koszul MS.Cylinder MS.Bare MS.Native.Chart
open Filter Topology Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}

local notation "X" => Land G n
local notation "U" => ScalarGhost G n
local notation "⟪" x "," y "⟫" => inner ℝ x y

/-- Analytic tangent inclusion -/
abbrev spread (G:Gauge)(n:Side) : Land G n →L[ℝ] Chart.City G (Site n) :=
  (LinkP G n).subtypeL ∘L g0 G n
lemma spread_eq (x:X) : spread G n x=x.val.val:=rfl

lemma spread_zero (G:Gauge)(n:Side): Tendsto (spread G n) (𝓝 0) (𝓝 0) := by
  simpa using ((spread G n).continuous.continuousAt (x:=0)).tendsto

lemma rent_land (x:X): MS.Native.Chart.rent (drive n) (spread G n x) = (-2:ℝ)* LAND x:= by
  rw [original_W, show nation (spread G n x)= positiveLinks x.val from rfl, LAND,←energy_at]; ring

lemma jac_log (hn: Admissible n) :
    (fun x : Land G n=> Real.log (Jacob x.val))=ᶠ[𝓝 0] (fun x=> totalH (spread G n x)/2):= by
  filter_upwards [eventually_all.mpr (fun i:Pert.Orb.Links n=> ((continuous_apply i).continuousAt (x:=(0:Chart.City G (Site n)))).tendsto.comp (spread_zero G n) |>.eventually ((Maurer.lives G).and Maurer.opposite))] with x h
  let f(l:Pert.Orb.Links n):ℝ:=Maurer.lac (spread G n x l)
  have hu (i:Pert.Orb.Links n): f (Pert.Orb.image i)=f i:= by
    unfold f; rw [spread_eq,x.1.property i]; exact (h i).2
  rw [Jacob, Real.log_prod (s:=positive n) (fun i _=>(show 0 < LocalH.spin G (x.1.1 i) from (h i).1).ne')]
  let g:= positive n; change ∑ i∈g,f i = (∑ i,f i)/2
  rw [←Finset.sum_sdiff (Finset.subset_univ g)]
  have he: ∑ i ∈univ\g,f i = ∑ i ∈g,f i := by
    let q := Pert.Orb.image (n:=n)
    have hq(i): i∈univ\g↔ q i∈g:= by rw [Finset.mem_sdiff, and_iff_right (Finset.mem_univ _)]; exact (switches i hn).symm
    apply sum_bij (fun i _=> q i) (fun i hi=>(hq i).mp hi)
      (fun _ _ _ _ hh=>(LeftInverse.injective Pert.Orb.image_image) hh) _ (fun i _=>(hu i).symm)
    intro i hi; exact ⟨q i, (hq (q i)).mpr (by unfold q; rwa [Pert.Orb.image_image]), Pert.Orb.image_image i⟩
  rw [he]; ring

/-- Integration by parts *before* frequency inversion. Also fixes our ghost sign. -/
lemma by_grad (f : Chart.City G (Site n))(u: ScalarGhost G n) :
    ∑ i, ⟪(gM u).val i,f i⟫ = ∑ x, ⟪u.val x,divB f x⟫ := by
  simp_rw [divB,inner_sum, inner_sub_right]
  rw [Fintype.sum_prod_type]
  generalize hX:u.val = a -- maybe not
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs=> rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _=> ?_
  simp_rw [show ∀ x, (gM u).val (x,i)=a x-a (x+step i) from fun x=> by rw [← hX]; rfl, inner_sub_left, Finset.sum_sub_distrib]
  congr 1
  symm
  have h:= Equiv.sum_comp (Equiv.addRight (step i)) (fun x:Site n=> ⟪a x, f (x-step i,i)⟫)
  simpa using h.symm

def fpWeight (v u:ScalarGhost G n)(a:Land G n):ℝ := (∑ l, ⟪(gM v).val l, roam (drive n) (spread G n a) u.val l⟫)/2

set_option maxHeartbeats 450000 in
lemma roam_transforms (v : ScalarGhost G n)(l:Pert.Orb.Links n): ∀ᶠ a:X in 𝓝 0,
    roam (drive n) (spread G n a) v.val (Pert.Orb.image l)= -(roam (drive n) (spread G n a) v.val l) := by
  filter_upwards [((continuous_apply l).continuousAt (x:=(0:Chart.City G (Site n)))).tendsto.comp (spread_zero G n)|>.eventually (Maurer.volt_back (route (drive n) l v.val))] with a ha
  have he: route (drive n) (Pert.Orb.image l) v.val=(route (drive n) l v.val).swap:= by
    change (v.val (-l.1-step l.2),v.val (-l.1-step l.2+step l.2))=(v.val _,v.val l.1)
    have h (x:Site n): v.val (-x) = v.val x:= (show _∧_ from v.property).1 x
    rw [sub_add_cancel,h,show -l.1-step l.2= -(l.1+step l.2) by abel,h]; rfl
  change Maurer.volts (Chart.route (drive n) (Pert.Orb.image l) v.val) (spread G n a (Pert.Orb.image l)) = _
  rw [he,spread_eq,a.val.property l]; exact ha

lemma path_turn (l:Pert.Orb.Links n)(a:X)(u:U)(t:ℝ):
    roughM a.val (shoreL (- (t • u))) l = G.plog (G.mat (Maurer.step (route (drive n) l u.val) (a.val.val l) t)):= by
  unfold roughM Lattice.gauge positiveLinks Maurer.step
  have he (i:Site n): (shoreL (- (t • u))).val i= -(t • u.val i):=rfl
  dsimp only
  rw [he,he, Work.F03.exp_neg_color (t • u.val (l.1+Lattice.step l.2)),inv_inv]; rfl

lemma fp_germ(v u:ScalarGhost G n): ∀ᶠ a:X in 𝓝 0,
    fpWeight v u a = -siteTest v (paneGhost G n a u):= by
  obtain ⟨r,hr,h⟩:= LocalH.geom_patch G
  have ha: Tendsto (fun a:Land G n=>(a.val,(0: AllSite G n))) (𝓝 0) (𝓝 0):=(g0 G n).continuous.continuousAt (x:=0)|>.tendsto.prodMk_nhds tendsto_const_nhds
  filter_upwards [ha.eventually ((DivM_slick (G:=G) (n:=n)).eventually (by simp)), eventually_all.mpr (fun i:Pert.Orb.Links n=> (roam_transforms u i).and (((continuous_apply i).continuousAt (x:=(0:Chart.City G (Site n)))).tendsto.comp (spread_zero G n) |>.eventually (ball_mem_nhds (0:G.Color) hr)))] with a hd hU
  let R : Potential G n:= ⟨roam (drive n) (spread G n a) u.val,fun l=>(hU l).1⟩
  have hu: HasDerivAt (fun t:ℝ=> roughM a.val (shoreL (- (t • u)))) R.val 0:= by
    refine hasDerivAt_pi.mpr fun l=> ?_
    simp_rw [path_turn]; exact Maurer.amp (route (drive n) l u.val) (h r le_rfl) (hU l).2
  have hv: HasDerivAt (fun t:ℝ=> DivM a.val (shoreL (- (t • u)))) (dLin R) 0:= by
    let L:=divL G n ∘L (Pert.Orb.balance G n).toContinuousLinearMap
    exact Eq.subst (motive:=fun y=> HasDerivAt _ y _) (show L R.val=dLin R from congrArg dLin (balance_same R)) (L.hasFDerivAt.comp_hasDerivAt (f:=fun t:ℝ=> roughM a.val (shoreL (- (t • u)))) 0 hu)
  let S:=shoreL (G:=G) (n:=n)
  have hc: ContDiffAt ℝ ω (DivM a.val ∘ S) 0 := by
    apply ContDiffAt.comp
    rw [map_zero]; exact hd.comp (f:=fun z=>(a.val,z)) 0 (contDiffAt_const.prodMk contDiffAt_id)
    exact S.contDiff.contDiffAt
  have hT: HasDerivAt (fun t:ℝ=> -(t • u)) (-u) 0 := by simpa only [one_smul] using! (((hasDerivAt_id' (0:ℝ)).smul_const u).neg)
  have he := hc.differentiableAt (by simp)|>.hasFDerivAt.comp_hasDerivAt_of_eq (f:=fun t:ℝ=>-(t • u)) (x:=(0:ℝ)) hT (by simp)
  rw [map_neg] at he
  replace he : dLin R= -paneGhost G n a u:= hv.unique he
  unfold fpWeight; rw [by_grad]
  have hx: divB (roam (drive n) (spread G n a) u.val)=(-paneGhost G n a u).val:= congrArg Subtype.val he
  simp_rw [hx,Submodule.coe_neg, Pi.neg_apply,inner_neg_right,sum_neg_distrib]; simp only [neg_div,siteTest,Finset.sum_div]
end YM.FVAAlt2
