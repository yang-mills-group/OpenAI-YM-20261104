import YM.MSbar.Bout.Sears
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Tilt
open Function Filter Whisk Lis Measuring Cacao Push Uniform Lattice RG Tonic Aqua Bout
open Precision Gauge Midpoint Rolling Exterior Wilson Wave Native.Chart
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable (G:Gauge){n:Side}
local notation "V"=>G.Color
local notation "A"=>Native.Chart.Rail G
noncomputable def wah (y:A×V):= Native.Chart.head G y.1 (1,y.2)
local notation "K"=>wah G
lemma up (v:A)(x:V)(t:ℝ): K (t • v,x)=Native.Chart.head G v (t,x):=by unfold wah Native.Chart.head Native.Chart.hit; simp
lemma hold : ∀ᶠ x:G.Color in 𝓝 0, K (0,x)=x:=by
    have hp:=Native.Chart.enters G (0:A); unfold wah; simpa only [Native.Chart.head,Native.Chart.hit,Prod.fst_zero,Prod.snd_zero,neg_zero,zero_smul,smul_zero] using hp
lemma costX: ContDiffAt ℝ ω (wah G) 0:=by
    let f(x:A ×V):=G.mat (hit G x.1 1 x.2); have ht(z: A× V): f z= Up G (-z.1.1)*Up G z.2 * Up G z.1.2:=by simp only [Up, f,Function.comp_apply,Native.Chart.hit,one_smul, G.mat_mul]
    have hF:ContDiff ℝ ω f:=by rw [funext ht]; exact ContDiff.mul (ContDiff.mul (G.exp_jet.comp ((contDiff_fst.comp (f:=Prod.fst) contDiff_fst).neg)) (G.exp_jet.comp contDiff_snd)) (G.exp_jet.comp (contDiff_snd.comp (f:= Prod.fst) contDiff_fst))
    apply (show ContDiffAt ℝ ω _ (f 0) from (by rw [ht]; change ContDiffAt ℝ ω G.plog (Up G (-(0:V))* Up G 0*Up G (0:V)); simp only [Up, Function.comp_apply, G.mat_lieExp_zero,G.mat_one,mul_one,neg_zero]; exact G.plog_diff)).comp 0 (f:=f) (hF.contDiffAt)
lemma touchV : fderiv ℝ (wah G) (0:A ×V) = ((ContinuousLinearMap.snd ℝ _ _)+(ContinuousLinearMap.snd ℝ V V).comp (ContinuousLinearMap.fst ℝ _ _)-(ContinuousLinearMap.fst ℝ V V).comp (ContinuousLinearMap.fst ℝ _ _)):=by
   let H:=fderiv ℝ K (0:A×V); apply ContinuousLinearMap.ext; intro x; let v:=x.1; let g:=x.2; have hx : H (v,0)=v.2-v.1:=by
        have ht : HasDerivAt (fun t:ℝ=> (t • v,(0:V))) (v,(0:V)) 0:=by have h' := ((hasDerivAt_id' (0:ℝ)).smul_const v).prodMk (hasDerivAt_const _ (0:V)); simpa using! h'
        have hh:= ((show DifferentiableAt ℝ K ((0:ℝ) • v, (0:V)) from by rw [zero_smul]; exact (costX _).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt (0:ℝ) ht); change HasDerivAt (fun t:ℝ=> K (t • v,0)) _ 0 at hh; simp_rw [up,zero_smul] at hh; exact (hh.unique (Native.Chart.breeze G v 0 (Native.Chart.jet ..))).trans (Native.Chart.begins ..)
   have hV : H (0,g)=g:=by
        let L:V→L[ℝ] (A×V):= (0:V→L[ℝ]A).prod (ContinuousLinearMap.id ..); have he : K ∘ L=ᶠ[𝓝 0] id:=Tilt.hold G; have hx:=he.fderiv_eq (𝕜:=ℝ); rw [fderiv_comp _ (by rw [map_zero]; exact (costX G).differentiableAt (by simp)) L.differentiableAt,map_zero,L.fderiv,fderiv_id] at hx; exact DFunLike.congr_fun hx g
   change H x= g+v.2-v.1; rw [show x= (v,(0:V)) + ((0:A),g) by cases x; simp [v,g], _root_.map_add,hx,hV]; abel
lemma prime :∃ r C:ℝ,0<r∧0≤ C∧ ∀ z:A× V,‖z‖<r→ ‖K z-(z.2+z.1.2-z.1.1)‖≤ C*‖z‖^2∧ G.lieExp (K z)=hit G z.1 1 z.2 :=by
    obtain ⟨r,C,hr,hC,hp⟩:= Rolling.taylorQuote ((costX G).of_le (m:=↑(1+1:ℕ)) le_top); let H(y:A × V):=hit G y.1 1 y.2; have he: Continuous H :=by unfold H Native.Chart.hit; fun_prop (disch := first|apply G.lieExp_cont|exact G.lieExp_cont); -- syntax
    have hz:H 0=1:=by unfold H Native.Chart.hit; simp; -- simp ports
    obtain ⟨d,hd,hV⟩:= Metric.nhds_basis_ball.eventually_iff.mp ((show Tendsto H (𝓝 0) (𝓝 1) from hz ▸ he.continuousAt.tendsto).eventually G.plog_right)
    refine ⟨min r d,C,lt_min hr hd,hC,fun z hj=>⟨?_,hV (mem_ball_zero_iff.mpr (hj.trans_le (min_le_right ..)))⟩⟩
    have hx : blockTaylor 1 K z= z.2+z.1.2-z.1.1:=by
        unfold blockTaylor; rw [Finset.sum_range_succ,Pi.add_apply, Finset.sum_apply,sum_range_succ,sum_range_zero,zero_add]; unfold Tensor.diagonal; rw [Tensor.coeff_apply_zero,show K 0=0 from (Tilt.hold G).self_of_nhds,zero_add]; unfold Tensor.coeff; rw [_root_.smul_apply,iteratedFDeriv_one_apply,touchV]; simp
    have he' := hp z (mem_closedBall_zero_iff.mpr ((hj.trans_le (min_le_left ..)).le)); rw [hx] at he'; exact he'
lemma loopsX (v:A)(x:V){t:ℝ}(hp:G.lieExp (Native.Chart.head G v (t,x)) = hit G v t x ) : ∀ a:ℝ,Native.Chart.head G v (t+a,x)= Native.Chart.head G v (a,Native.Chart.head G v (t,x)):=by -- fix x
    have hf (a s:ℝ)(x:V): G.lieExp ((a+s)•x)= G.lieExp (a•x)* G.lieExp (s•x):=by apply G.mat_injective; rw [G.mat_mul,G.mat_lieExp,G.mat_lieExp,G.mat_lieExp,map_smul,map_smul,map_smul,add_smul]; exact NormedSpace.exp_add_of_commute (((Commute.refl (G.colorMat x)).smul_left a).smul_right s)
    intro a; apply (congr_arg G.plog) ∘ (congr_arg G.mat) -- syntax?
    unfold Native.Chart.hit; rw [hp]; unfold Native.Chart.hit; rw [add_comm t a,hf,add_comm a t,hf]; group -- order wrong first rewrite first occurrence=left.G.left should new*a then. swap.
lemma speedK (v:A)(x:V){t D:ℝ}(hx:Beam G D)(ht:‖Native.Chart.head G v (t,x)‖<D)(hp:G.lieExp (Native.Chart.head G v (t,x))=hit G v t x) : HasDerivAt (fun z:ℝ=>Native.Chart.head G v (z,x)) (Native.Chart.speed G v (Native.Chart.head G v (t,x))) t:=by
    let X:=Native.Chart.head G v (t,x); let H(s:ℝ):= Native.Chart.head G v (s,X); have he : HasDerivAt H (Native.Chart.speed G v X) (t-t):=(sub_self t).symm ▸ Native.Chart.breeze G v X (hx X ht v).1
    let g(s:ℝ):= s-t; have hG:HasDerivAt g 1 t:=(hasDerivAt_id' t).sub_const _; have hh:= ((show HasDerivAt H (Native.Chart.speed G v X) (g t) from he).scomp t hG); rw [one_smul] at hh; refine hh.congr_of_eventuallyEq (Eventually.of_forall (fun y=> ?_)); change Native.Chart.head _ _ (y,_)=Native.Chart.head _ _ (_,X); nth_rw 1 [show y=t+(y-t) by abel]; exact loopsX G _ x hp _
end YM.MSbar.Tilt
