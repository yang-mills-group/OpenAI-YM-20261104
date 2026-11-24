import YM.RegulatorIR.Binding.Curve

/-!
Connection gradient jets. For zero-mode issue only. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Binding
open PertExtension Laplace Chart Lattice Geometry Geometry.End Geometry.Field Orb Gauge MeasureTheory Filter Function Set Metric Exterior Wilson RG Precision Tree
open scoped ContDiff Topology NNReal ENNReal BigOperators Classical Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {f c: Side}{G:Gauge}

lemma anyWalk {X:Type*}[Group X](y:Site f)(w:Walk): travel (1:Links _ X) y w=1:=by induction w generalizing y <;> simp_all [travel,Step.read]
lemma gauge_base_neutral (k:Site f → G.El)(h:compatible k)(hv:goat k 1=1)(x): k x=k 0 := by
 have he:Lattice.gauge k (1: Config G f)=1:=by
   have hk:= goat_lift k 1 h; rw [hv,Geometry.lift_one] at hk; exact hk.symm
 have hf:=Lattice.travel_gauge k (1: Config G f) 0 (Orb.arrival x)
 rw [he,anyWalk,mul_one, Orb.arrival_end] at hf
 exact (mul_inv_eq_one.mp hf.symm).symm
-- colors

def EvenSite (k:Site f → G.Color):Prop:= ∀ x,k (-x)=k x
def Gauge0 (G:Gauge)(f:Side):Submodule ℝ (Site f→G.Color) where
 carrier:={k|EvenSite k}
 add_mem' hf hg x:=congr_arg₂ (·+·) (hf x) (hg x)
 zero_mem':=fun _=>rfl
 smul_mem' l _ hh x:=congr_arg (l • ·) (hh x)

def gradie (k:Site f→G.Color): Horizon G f:= fun x=> k x.val.1-k (x.val.1+step x.val.2)
-- sign suited to Lattice.gauge; x=head? actually tail

def GradientSite (u:Horizon G f):Prop:=∃ k:Site f→G.Color,EvenSite k∧u=gradie k
lemma site_orbs {k:Site f→G.Color}(h:EvenSite k)(t:ℝ): compatible (fun i=> G.lieExp (t • k i)):= fun i=>congr_arg G.lieExp (congr_arg (t • ·) (h i))
def siteCurve (k:Site f→G.Color) (t:ℝ):= goat (fun i=> G.lieExp (t • k i)) 1
lemma site_origin (k: Site f → G.Color): siteCurve k 0=1:=by unfold siteCurve;simp only [zero_smul,mat_lieExp_zero];exact goat_one _
lemma site_mat (k:Site f→G.Color)(i:OEdge f): HasDerivAt (fun t:ℝ=> G.mat (siteCurve k t i)) (G.colorMat (gradie k i)) 0:=by
 have h:= (vertical_deriv (k i.val.1)).mul ((vertical_deriv (k (i.val.1+step i.val.2))).star)
 simp_rw [siteCurve,goat_at, Pi.one_apply,mul_one, mat_mul,mat_inv]
 apply h.congr_deriv;rw [gradie, map_sub];simp [G.colorMat_skew,sub_eq_add_neg]
lemma site_log (k:Site f→G.Color): HasDerivAt (fun t:ℝ=>lower G (OEdge f) (siteCurve k t)) (gradie k) 0:=by
 refine (hasDerivAt_pi ..).mpr fun i=>?_
 have ht:G.mat (siteCurve k 0 i)=1:=by rw [site_origin]; rfl
 have he : HasFDerivAt G.plog (fderiv ℝ G.plog 1) (G.mat (siteCurve k 0 i)):=by rw [ht];exact (G.plog_diff.differentiableAt (by simp)).hasFDerivAt
 exact (he.comp_hasDerivAt 0 (site_mat k i)).congr_deriv (plog_rotate ..)
lemma site_cont (k:Site f → G.Color): Tendsto (siteCurve k) (𝓝 0) (𝓝 1):=by
 have hp : Continuous (siteCurve k):= by
    apply continuous_pi;intro i
    simp_rw [siteCurve,goat_at]; fun_prop
 convert hp.tendsto 0 using 1; rw [site_origin]
lemma slopes (S:StepData c f)(H:S.patch.Branches S.kernel G)(k:Site f → G.Color)(h:EvenSite k): rod G S (gradie k)=gradie (k ∘ S.ratio.embed):= by
 have hx (t:ℝ): predictor S (siteCurve k t)= siteCurve (k ∘ S.ratio.embed) t:= by rw [siteCurve,prediction_flow S H _ _ (site_orbs h _), predict_zero S H]; rfl
 let X:=siteCurve k; let Y (t:ℝ):= lower G _ (X t)
 have hy: Y 0=0:=by unfold Y X; rw [site_origin];exact lower_zero ..
 have hg :HasFDerivAt (slope G S) (rod G S) (Y 0):=hy.symm ▸ ((smooth S H).differentiableAt (by simp)).hasFDerivAt
 have Hs: ∀ᶠ t in 𝓝 0, lower G (OEdge c) (siteCurve (k ∘ S.ratio.embed) t)=slope G S (Y t) := by
    filter_upwards [(site_cont k).eventually (upper_lower ..)] with t ht
    rw [slope, ← hx, show climb (Y t)=siteCurve k t from ht]
 exact ((hg.comp_hasDerivAt 0 (site_log k)).congr_of_eventuallyEq Hs).unique (site_log ..)

lemma gradie_zone (S:StepData c f)(H:S.patch.Branches S.kernel G) {x:Horizon G f} (h: GradientSite x) : GradientSite (rod G S x):=by
 obtain ⟨k,hk,hx⟩:= h; refine ⟨k ∘ S.ratio.embed,fun i=> ?_, by rw [hx]; exact slopes S H k hk⟩
 change k (S.ratio.embed (-i))=_; rw [show S.ratio.embed (-i)=-(S.ratio.embed i) from S.ratio.root.map_neg _]
 exact hk _
lemma gradie_uses (k:Site f → G.Color)(hK:EvenSite k)(he:Even f.val)(i : Edge (Site f)): fire (gradie k) i=k i.1-k (i.1+ step i.2):=by
 let x:= index i
 rcases eR_spec i with h|h
 · rw [show i=(index i).val from h.symm,fire_at (gradie k) (index i)]; rfl -- rew all?
 have hp:= fire_at (gradie k) x
 have hh: x.val=reflect i:=h
 rw [hh,fire_swaps _ he] at hp
 rw [← neg_inj, hp, gradie,hh]; dsimp only [Orb.reflect]; rw [show -i.1-step i.2+step i.2=-i.1 by abel, show -i.1-step i.2=-(i.1+step i.2) by abel,hK,hK]; abel
lemma pays_gradient (k:Site f→G.Color)(h:EvenSite k)(he:Even f.val) (v:Step)(x:Site f): cash (fire (gradie k)) v x=k x-k (x+v.vec):=by
 unfold cash; rcases v with ⟨i,hb|hb⟩
 · exact gradie_uses k h he _
 change -(fire (gradie k) (x-step i,i))= k x-k (x+-step i); rw [gradie_uses k h he]; simp [sub_eq_add_neg,add_comm]
lemma anchored (k:Site f→G.Color)(h:EvenSite k) (he:Even f.val){x:Site f}(w:Walk): line (fire (gradie k)) x w=k x-k (stop x w):=by
 induction w generalizing x with
 | nil=>simp [stop,line]
 | cons a b ih=>rw [line, pays_gradient k h he,ih,stop]; abel
lemma gradie_still (k:Site f→G.Color)(h:EvenSite k)(hp:Even f.val)(he:gradie k=0)(x): k x = k 0 := by
 have he' (x:Site f) (w:Walk):line (fire (gradie k)) x w=0:= by
    rw [he]; induction w generalizing x with
    | nil=>rfl
    | cons d u ih=>rw [line,ih]; simp [cash,fire]
 exact (sub_eq_zero.mp (show k 0-k x=0 from (by
    have ht:= anchored k h hp (x:=0) (arrival x); rw [he',arrival_end] at ht; exact ht.symm))).symm
end YM.RegulatorIR.Binding
