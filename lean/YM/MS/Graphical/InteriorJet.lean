import YangMills.WilsonProof.NativeSupport.YM.MS.Graphical.Registered

/-!
# Dividing by z with **uniform time** prices

Keep time estimates for functions holomorphic in the regulator z by working on
the rim of one disc. `scaleDown` is used on assembling a regular group given prices
on pole-cleared pages (`RemovingFactor.lean`).
-/

noncomputable section
namespace YM.MS.Graphical
open Set Filter Function Finset MeasureTheory Real Metric Complex
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color
open _root_.YM.MS.Shine Hem Mell Pearl Train Signal Book Convolve Garment.Wick Dock
open scoped Topology ContDiff Interval
variable {J E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : J → ℂ → E → ℂ} {u a R T W : ℝ} {z : J → ℂ}
variable {G : Gauge} {F : Schedule G}

/-- Version of `Shine.Rim` for a family with common pricing. -/
lemma within_disk (hT : T<R) (hp : W<T) (hW : 0≤W) (h : ∀ i, keys (disc R) (f i))
    (hf : veg 0 (fun x : J× (sphere (0:ℂ) T)=> f x.1 x.2) 1) (hx : ∀ i, z i∈ closedBall 0 W) :
    veg 0 (fun i=> f i (z i)) 1:= by
  let G:= ball (0:ℂ) T; have hc:0<T:=hW.trans_lt hp
  let c:= circleMap 0 T; let d:=(2*π*Complex.I : ℂ)⁻¹
  have hm s : c s∈ sphere (0:ℂ) T:= circleMap_mem_sphere _ hc.le s
  let μ:=volume.restrict (Set.Icc (0:ℝ) (2*π)); letI : IsFiniteMeasure μ:= by unfold μ; infer_instance
  let U(x:J)(s:ℝ):=deriv c s*(c s-z x)⁻¹; let H(i:J)(s:ℝ)(p:E):= U i s • f i (c s) p
  have hP:=closedBall_subset_ball (x:=(0:ℂ)) hT; have hB i: z i∈G:=closedBall_subset_ball hp (hx i)
  have hu (i:J)(p:E): DiffContOnCl ℂ (fun z=> f i z p) G:= ⟨fun z hz=> (h i p z (hP (ball_subset_closedBall hz))).differentiableWithinAt,
    by unfold G; rw [closure_ball _ hc.ne']; exact fun z hz=> (h i p z (hP hz)).continuousAt.continuousWithinAt⟩
  have hU: veg 0 (fun i:J×ℝ=>H i.1 i.2) 1:= by
    apply uWore (x:=fun i:J×ℝ=> U i.1 i.2) (uGrab hf fun i:J × ℝ=>(i.1,(⟨c i.2,hm _⟩:sphere (0:ℂ) T)))
       (div_pos hc (sub_pos.mpr hp));
    intro ⟨i,t⟩; unfold U c; rw [norm_mul,norm_inv,deriv_circleMap,norm_mul,norm_I,norm_circleMap_zero,
       abs_of_pos hc,mul_one,← div_eq_mul_inv]; have hv : T-W≤‖c t-z i‖:= by
      obtain hZ:= norm_sub_norm_le (c t) (z i); rw [show ‖c t‖=T by simp [c,norm_circleMap_zero,abs_of_pos hc] ] at hZ;
      have ht:‖z i‖≤W:=by simpa only [mem_closedBall,dist_zero_right] using hx i;
      linarith
    exact div_le_div_of_nonneg_left hc.le (sub_pos.mpr hp) hv
  have he : veg 0 (fun i p=>∫ s,H i s p ∂μ) 1:= by
    apply plush (integrable_const (μ:=μ) (1:ℝ)) (g:=H) (fun i=>Eventually.of_forall fun t=>hU.smooth (i,t))
    · intro i p
      have he: Continuous fun t=> U i t:= by
        simp_rw [U,c,deriv_circleMap]; apply Continuous.mul (by fun_prop)
        apply (Continuous.sub (continuous_circleMap ..) continuous_const).inv₀; intro s
        exact sub_ne_zero.mpr fun h=> (sphere_disjoint_ball.notMem_of_mem_left (hm s))
              ((show _=c s from h.symm) ▸ hB i)
      exact (he.smul (((hu i p).2).comp_continuous (continuous_circleMap ..)
          (fun x=> by rw [show closure G=closedBall 0 T by unfold G; rw [closure_ball _ hc.ne'] ]; exact sphere_subset_closedBall (hm x)))).aestronglyMeasurable
    intro j; obtain ⟨C,hC,b,hb⟩:=ride hU j; exact ⟨C,hC,b,fun i=> Eventually.of_forall fun t p=>by simpa using hb (i,t) p⟩
  rw [show (fun i=>f i (z i))= (fun i p=>d • ∫ s,H i s p ∂μ) from ?_];
  · exact uWore he (T:=max 1 ‖d‖) (lt_max_of_lt_left zero_lt_one) (fun _=>le_max_right ..)
  funext i p; obtain ht:= (hu i p).two_pi_i_inv_smul_circleIntegral_sub_inv_smul (hB i); rw [circleIntegral_def_Icc] at ht;
  unfold μ H U; simp only [mul_smul]; exact ht.symm

def scaleDown (F : Schedule G) : Schedule G := fun t=> Golden (F t)

lemma inherit_pay (h : Pays R F a) (hp : ∀ t, F t 0=0) (hR : ∀ t, Hol (disc R) (F t)) (hr : 0<R) :
    Pays (R/2) (scaleDown F) a := by
  intro J t Z B hv K HK hK hZ
  let T:=3*R/4; have ht:T<R:= by unfold T; linarith
  have hx:R/2<T:= by unfold T; linarith
  have he:0<T:= (half_pos hr).trans hx
  let S:= sphere (0:ℂ) T; let X t z:=plow 0 (-t) (scaleDown F t z)
  let u(i:J) :ℝ:= Real.exp (-a*t i); have hu(i:J):0<u i:= Real.exp_pos _
  have h'(i:S): ‖(i:ℂ)‖=T:= by simp
  have hy : fell 0 (fun _=>1) (fun i:J=> (u i:ℂ) • X (t i) (Z i)):= by
    have HZ : fell 0 1 (fun i:J×S=> (u i.1:ℂ) • X (t i.1) i.2) := by
      let Y(i:J×S):ℂ:= (u i.1:ℂ)*i.2.val⁻¹
      have hV : scaleC 0 (fun i:J×S=> u i.1) fun i=>‖Y i‖:= by
        refine ⟨T⁻¹,inv_pos.mpr he,0,fun i _ _=>?_⟩; dsimp only; rw [show ‖Y i‖=u i.1*T⁻¹ from ?_,mul_comm,pow_zero,mul_one];
        unfold Y; rw [norm_mul,norm_inv,h' i.2,norm_real, norm_of_nonneg (hu i.1).le]
      convert fall_scale (U:=Y) (h (J×S) (t∘Prod.fst) (fun i=>i.2) B (fun i=>hv _) S (isCompact_sphere ..)
             (sphere_subset_closedBall.trans (closedBall_subset_ball ht)) (fun i=>i.2.property)) hV using 1;
      · funext i;
        simp only [u,Function.comp_apply,← Real.exp_add]; rw [show -a*t i.1+a*t i.1=0 from by ring,Real.exp_zero]; rfl
      funext i; have hx:i.2.val≠0:=norm_pos_iff.mp (by simpa only [h' i.2] using he)
      rw [show X (t i.1) i.2=(i.2.val:ℂ)⁻¹ • plow 0 (-t i.1) (F (t i.1) i.2) from ?_,smul_smul]; rfl
      unfold X scaleDown; rw [hung hx,hp,sub_zero, ← cert,map_smul,cert]
    intro m E _ _ _ w
    let V (i:J) (z:ℂ):= (u i:ℂ) • X (t i) z
    apply within_disk ht hx (half_pos hr).le (f:=fun i z=> fieldVal (V i z m) w) _ (HZ m E w)
        (fun i=> ball_subset_closedBall (hK (hZ i)))
    exact fun i p => (((HolG (hR (t i)) hr).grazes (-t i) 0).smul (u i:ℂ)).top m (sail w p)
  have he (i:J): u i= (Real.exp (a*t i))⁻¹:= by unfold u; rw [neg_mul,Real.exp_neg]
  have ht : scaleC 0 (fun i=> Real.exp (a*t i)) (fun i:J=> ‖(u i:ℂ)⁻¹‖) := by
    refine ⟨1,zero_lt_one,0,fun i p _=>?_⟩; simp_rw [pow_zero,one_mul,norm_inv,norm_real, Real.norm_of_nonneg (hu i).le,he,inv_inv]; exact le_rfl
  convert fall_scale hy ht using 1
  · ext; exact (mul_one _).symm
  funext i; rw [inv_smul_smul₀]; exact ofReal_ne_zero.mpr (hu i).ne'
end YM.MS.Graphical
