import YM.MS.ScaleForest.Fueled
/-!
# A disk-price extension, uniform in time and all other tested parameters

Use Cauchy integral from nonzero z. Need this because `Stay` is pointwise in log length. Want
to keep that
subtracted amplitude, and use a *continuation estimate* on the whole
quotient/summed forest, not choose Laurent representatives with no uniform
control. Require estimates controlling all times.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Filter Function Real Arc MeasureTheory Rock Path Shine Metric
open scoped Topology ContDiff
variable {I E F J:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
   {R T W a b r : ℝ} {z:ℂ}

abbrev sphereT (T:ℝ) := Metric.sphere (0:ℂ) T
def CauchyK (T:ℝ)(z:ℂ)(t:ℝ) : ℂ := deriv (circleMap 0 T) t*(circleMap 0 T t - z)⁻¹

theorem Ucont (hT:0≤T) [TopologicalSpace I] {Z:I→ℂ} {u:I→ℝ} (hz:Continuous Z)(h:∀i, Z i∈disc T)(hu:Continuous u):
    Continuous (fun i=> CauchyK T (Z i) (u i)) := by
   unfold CauchyK; simp_rw [deriv_circleMap]; apply Continuous.mul (by fun_prop) (( ( (continuous_circleMap ..).comp hu ).sub hz).inv₀ _); intro i; apply sub_ne_zero.mpr; exact fun he=> sphere_disjoint_ball.notMem_of_mem_left (circleMap_mem_sphere 0 hT (u i)) ((show Z i=circleMap 0 T (u i) from he.symm) ▸ h i)

theorem Uright (hz : z∈disc W) (he : W<T) (hs:0≤T) (x:ℝ) : ‖CauchyK T z x‖ ≤ T/(T-W) := by
   let c:= circleMap 0 T;
   have hZ: T-W≤ ‖c x-z‖:= by
       have hh:= norm_sub_norm_le (c x) z; rw [ show ‖c x‖=T from by simp only [c,norm_circleMap_zero,abs_of_nonneg hs]] at hh; have ht: ‖z‖< W:= mem_ball_zero_iff.mp hz; linarith
   unfold CauchyK; rw [norm_mul,norm_inv,deriv_circleMap,norm_mul,Complex.norm_I,norm_circleMap_zero,abs_of_nonneg hs,mul_one,← div_eq_mul_inv]; exact div_le_div_of_nonneg_left hs (sub_pos.mpr he) hZ

abbrev Cauchyv : ℂ:= (2*↑π*Complex.I:ℂ)⁻¹

theorem Cauchy_here {f:ℂ→ℂ}(hv:Forest (disc R) f) (h : T < R)(hp:0<T)(hZ:z∈disc T) :
    f z = Cauchyv • ∫ s in (0:ℝ)..(2*π), CauchyK T z s * f (circleMap 0 T s) := by
   have hP := Metric.closedBall_subset_ball (x:=(0:ℂ)) h; have ht : DiffContOnCl ℂ f (disc T) := ⟨fun z hz=> (hv z (hP (Metric.ball_subset_closedBall hz))).differentiableWithinAt,by unfold disc; rw [closure_ball _ hp.ne']; exact fun z hz=>(hv z (hP hz)).continuousAt.continuousWithinAt ⟩
   obtain he' := ht.two_pi_i_inv_smul_circleIntegral_sub_inv_smul (show z∈disc T from by assumption)
   rw [circleIntegral] at he'; unfold Cauchyv CauchyK; simp_rw [ mul_assoc _ _ (f _) ]; exact he'.symm

-- push estimates through Cauchy formula. Normalize all exterior factors to bound 1 first.
variable (hT:0<T)(he:T<R)(hW:W<T) {f:J→ℂ→E→ℂ} {F:J→ℂ→ℂ}
include hT he hW
local notation "Zτ" => circleMap (0:ℂ) T

theorem Cauchy_uniform (hf:∀ j, Arc.keys (disc R) (f j)) (hu:veg 0 (fun i:J×sphereT T=>f i.1 i.2) 1) (z:J→disc W):
    veg 0 (fun j=> f j (z j)) 1 := by
   let μ:= MeasureTheory.volume.restrict (Ioc (0:ℝ) (2*π)); let g(i:J)(t:ℝ)(p:E):= CauchyK T (z i) t * f i (Zτ t) p
   have hz (i:J): (z i:ℂ)∈disc T:= Metric.ball_subset_ball hW.le (z i).property
   have hℓ(s:ℝ): Zτ s∈ sphereT T:= circleMap_mem_sphere _ hT.le s
   have hX: (fun i=> f i (z i)) = fun i p=> Cauchyv • ∫ t:ℝ,g i t p ∂μ := by funext i p; simpa only [intervalIntegral.integral_of_le (show 0≤2*π by positivity)] using Cauchy_here (hf i p) he hT (hz i)
   have hg: veg 0 (fun i:J×ℝ=>g i.1 i.2) 1 := uWore (price_veg_shift hu (fun i:J×ℝ=>(i.1,(⟨ Zτ i.2,hℓ i.2⟩:sphereT T)))) (x:=fun i:J×ℝ=> CauchyK T (z i.1) i.2) (div_pos hT (sub_pos.mpr hW)) (fun i=> Uright (z i.1).property hW hT.le _)
   haveI : IsFiniteMeasure μ:= inferInstanceAs (IsFiniteMeasure (MeasureTheory.volume.restrict (Ioc (0:ℝ) (2*π))))
   have h_u: veg 0 (fun i p=> ∫ t,g i t p ∂μ) 1:= by
      apply plush (g:=g) (μ:=μ) (integrable_const (μ:=μ) (1:ℝ)) (fun i=> Eventually.of_forall fun x=> hg.smooth (i,x))
      · intro i p; apply Continuous.aestronglyMeasurable; exact (Ucont hT.le continuous_const (fun _=> hz i) continuous_id).mul (continuous_iff_continuousAt.mpr (fun p:ℝ=> (hf i _ _ (Metric.closedBall_subset_ball he (Metric.sphere_subset_closedBall (hℓ p)))).continuousAt.comp ((continuous_circleMap ..).continuousAt (x:=p))))
      intro j; obtain ⟨C,hC,k,hP⟩:= Arc.ride hg j; exact ⟨ C,hC,k,fun i=>Eventually.of_forall (fun t p=>by simpa only [Pi.one_apply,Pi.zero_apply,abs_zero,add_zero,mul_one,one_mul] using hP (i,t) p)⟩
   rw [hX]; exact uWore h_u (T:=max 1 ‖Cauchyv‖) (lt_max_of_lt_left zero_lt_one) (x:=fun _=> Cauchyv) (fun _=>le_max_right ..)

theorem Cauchy_dual [TopologicalSpace J] (hf:∀ j, Forest (disc R) (F j)) (hC:Continuous (fun i:J×sphereT T=> F i.1 i.2)) (z:J→disc W) (hz : Continuous z) : Continuous (fun j=> F j (z j)):= by
   let p(s:ℝ):sphereT T:= ⟨ Zτ s,circleMap_mem_sphere _ hT.le s⟩; have hm:Continuous p:= Continuous.subtype_mk (continuous_circleMap ..) (fun s=> (p s).property); have ht (i:J): (z i).val ∈disc T:= Metric.ball_subset_ball hW.le (z i).property
   let U(i:J)(s:ℝ):= CauchyK T (z i) s * F i (p s); have hu:Continuous (uncurry U):= ((Ucont hT.le ( continuous_subtype_val.comp (hz.comp continuous_fst) ) (fun _=> ht _) continuous_snd)).mul (hC.comp (continuous_fst.prodMk (hm.comp continuous_snd)))
   rw [show (fun i=> F i (z i))=(fun i => Cauchyv • ∫ s in (0:ℝ)..(2*π), U i s) from funext (fun i=> Cauchy_here (hf i) he hT (ht i))]; exact ( intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ:=MeasureTheory.volume) hu _ _ ).const_smul Cauchyv

open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum
open Detect Tone Momentum Osc Fiddle Metric
variable {G:Gauge} {U:Curtain G I}

def sphereBudget (F:Curtain G I)(a b R:ℝ) := ∀ (J:Type) (z:J→sphereT R)(s:J→ℝ)(v:J→I), fell 0 (fun i=> levy a b (s i)) (fun i=>F (z i) (s i) (v i))

theorem restoreEnvelope (ht:∀ t i,hill (disc R) (fun z=> U z t i)) (hp:sphereBudget U a b T) : Envelope W a b U:= by
   intro J z s v m E _ _ _ w; let V(i:J):= levy a b (s i); let Y(i:J)(z:ℂ):Mob G := U z (s i) (v i); let F(i:J)(z:ℂ):Mob G:= ((V i : ℂ)⁻¹) • Y i z; have hV(i:J):0<V i:=posLevy ..; have h_F(h:J): Arc.keys (disc R) (fun z=> fieldVal (F h z m) w):= fun p i hi=> (ht (s h) (v h) m _ i hi).const_mul _
   let T':= sphereT T; have h : fell 0 (fun i:J×T'=>V i.1) (fun i=>Y i.1 i.2) := hp (J×T') Prod.snd (s∘Prod.fst) (v∘Prod.fst);
   have he' : fell 0 1 (fun i:J×T'=> F i.1 i.2) := by
      obtain hv:= fall_scale (U:=fun i:J×T'=>((V i.1:ℂ)⁻¹)) h (b:=fun i=> (V i.1)⁻¹) ⟨1,zero_lt_one,0,fun i p h=> by simp only [norm_inv,Complex.norm_real,pow_zero,one_mul]; rw [norm_of_nonneg (hV _|>.le)]⟩
      convert! hv using 1; ext i; rw [Pi.one_apply, inv_mul_cancel₀ (hV _).ne']
   obtain hc:= Cauchy_uniform hT he hW (f:=fun i z=> fieldVal (F i z m) w) h_F (he' m E w) z;
   have hm: scaleC 0 V (fun i:J=> ‖(V i:ℂ)‖) := ⟨1,zero_lt_one,0,fun i p h=>by simp [abs_of_pos (hV i)]⟩;
   have hh (i:J) (p:E) : fieldVal (U (z i) (s i) (v i) m) w p=(V i:ℂ)*fieldVal (F i (z i) m) w p := by unfold fieldVal F; simp only [Pi.smul_apply,smul_eq_mul,← mul_assoc,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (hV i).ne'),one_mul]; rfl
   change veg 0 (fun i=>fieldVal _ w) V; simp_rw [fun i=> funext (hh i)]; convert! Costs.mul (at_rate hm) hc using 1; ext; simp
end YM.MS.ScaleForest
