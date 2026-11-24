import YM.Contacts.Lintel.Cradle
namespace YM.Contacts.Lintel
set_option linter.unusedSectionVars false
open Function Set Finset Filter Metric RG Wilson Lattice Precision Exterior MeasureTheory
open Bloch Milling Milling.Steam Pulse Spine MergeProof Milling.Forge Laurent Stationary Matrix Work.F05
open Milling.Garf Form House PertExtension.Series Tree Larch FreeResolvent PhysicalNext.RankCovariance
open PertExtension.Chart Radial
open scoped Topology BigOperators Matrix Classical NNReal ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}{c f m: Side}{α:ℕ→Type}{n k:ℕ}
variable {V X Y E:Type}[NormedAddCommGroup V][NormedSpace ℝ V][FiniteDimensional ℝ V]
   [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable {t:E} {a b:E→ ℝ}
namespace Crag
open Wire
variable {M F K J: E×V→ℝ}
open Tested
variable [MeasurableSpace E][MeasurableSpace V][BorelSpace E][BorelSpace V]
variable (μ: Measure V)[μ.IsNegInvariant][μ.HasTemperateGrowth]
def alone (K:E×V→ℝ) := fun p:E×V=> K (p.1,0)
def radial (F:E×V→ℝ) := fun p:E×V=> jet (fun y=> F (p.1,y)) 2 p.2
lemma aloneA (h:AnalyticAt ℝ K 0): AnalyticAt ℝ (alone K) 0:= ContDiffAt.analyticAt (ContDiffAt.comp _ h.contDiffAt (f:=fun p:E×V=>(p.1,(0:V))) (contDiffAt_fst.prodMk contDiffAt_const))
section
private def bentQ (F:E×V→ℝ)(x:E): V→L[ℝ] V→L[ℝ] ℝ := fderiv ℝ (fderiv ℝ (fun y=> F (x,y))) 0
lemma cost_bent (F:E×V→ℝ)(x:E)(v:V): radial F (x,v)= bentQ F x v v/2:= by unfold radial jet; erw [iteratedFDeriv_two_apply]; unfold bentQ; norm_num; ring
lemma model_bent (F:E×V→ℝ)(he:AnalyticAt ℝ F 0): AnalyticAt ℝ (bentQ F) 0:= by
    have ht : ContDiffAt ℝ ω (Function.uncurry fun x:E=> fderiv ℝ fun y=>F (x,y)) 0 := by
       let g(x:E×V)(y:V):= F (x.1,y); refine ContDiffAt.fderiv (f:=g) ?_ contDiffAt_snd (by simp : (ω:WithTop ℕ∞)+1 ≤ ω); exact ContDiffAt.comp _ he.contDiffAt ((contDiffAt_fst.comp _ contDiffAt_fst).prodMk contDiffAt_snd)
    exact ContDiffAt.analyticAt (ContDiffAt.fderiv (f:=fun x:E=> fderiv ℝ fun y=> F (x,y)) (g:=fun _=>0) ht contDiffAt_const le_top)
lemma radialA (h:AnalyticAt ℝ F 0): AnalyticAt ℝ (radial F) 0:= by
    rw [show radial F=fun p:E×V=> bentQ F p.1 p.2 p.2/2 from funext (fun p=> cost_bent ..)]; exact ContDiffAt.analyticAt ((((((model_bent F h).contDiffAt.comp (f:=Prod.fst) (0:E×V) contDiffAt_fst).clm_apply contDiffAt_snd).clm_apply contDiffAt_snd)).div_const _)
-- need MOVE theorem construct at graph
lemma based_bent {c:ℝ}(hc:0<c)(hf:AnalyticAt ℝ F 0)(h:∀ v,c*‖v‖^2≤ radial F (0,v)):
    ∃ d:ℝ,0<d ∧ ∀ᶠ x:E in 𝓝 0,∀ v,d*‖v‖^2 ≤ radial F (x,v):= by
   refine ⟨c/2,half_pos hc,?_⟩; filter_upwards [(model_bent F hf).continuousAt.tendsto.eventually (Metric.ball_mem_nhds _ hc)] with x hx v; set P:=bentQ F x; set V' :=bentQ F 0; have hy : ‖P - V'‖ ≤ c:=(show ‖P-V'‖<c from by simpa only [mem_ball, dist_eq_norm_sub] using hx).le; have hv : ‖(P - V') v v‖ ≤ c*‖v‖^2:= (((P-V') v).le_opNorm _).trans (le_trans (mul_le_mul_of_nonneg_right (((P-V').le_opNorm v).trans (mul_le_mul_of_nonneg_right hy (norm_nonneg _))) (norm_nonneg _)) (by rw [pow_two]; exact (mul_assoc ..).le)); rw [cost_bent]; change _ ≤ P _ _/2; change |P v v- V' v v|≤_ at hv; have h:= h v; rw [cost_bent] at h; change _ ≤ V' _ _/2 at h; linarith only [abs_le.mp hv|>.1,h]
end
private lemma vertical (h:AnalyticAt ℝ F (x,(0:V)))(i:ℕ)(y:V): tack (vx y) F i (x,0) = (i.factorial:ℝ)*jet (fun y=>F (x,y)) i y:= by
    let u(y:V):= F (x,y); have ht : AnalyticAt ℝ u 0:= ContDiffAt.analyticAt (ContDiffAt.comp _ h.contDiffAt (contDiffAt_const.prodMk (f:=fun _:V=>x) contDiffAt_id)) -- see
    rw [tack_vert _ h,jet_tack u ht]; exact (mul_inv_cancel_left₀ (by positivity : (i.factorial:ℝ) ≠ 0) _).symm
lemma coupled (h:AnalyticAt ℝ F 0)(hz:∀ᶠ x:E in 𝓝 0,F (x,0)=0∧fderiv ℝ (fun y=>F (x,y)) 0=0) (he:AnalyticAt ℝ K 0)(hp : ∃ c:ℝ,0<c ∧ ∀ v,c*‖v‖^2 ≤ radial F (0,v)) : Paired F (radial F) K (alone K):= by
    let N: E×V→ℝ:= radial F; let T:=alone K; have hx:(∀ (x:E)(v:V)(t:ℝ),N (x,t•v)=t^2*N (x,v)):= fun _ _ _=> jet_smul ..; have hn:= radialA h; have hu:= aloneA he; have hl {F:E×V→ℝ}(h:AnalyticAt ℝ F 0): ∀ᶠ x:E in 𝓝 0,AnalyticAt ℝ F (x,0):=(tendsto_id.prodMk_nhds tendsto_const_nhds).eventually h.eventually_analyticAt
    have hK (V': E×V→ℝ) (x:E) (he:AnalyticAt ℝ V' (x,0)): AnalyticAt ℝ (fun y=>V' (x,y)) (0:V):= ContDiffAt.analyticAt (ContDiffAt.comp _ he.contDiffAt (f:=fun y:V=>(x,y)) (contDiffAt_const.prodMk contDiffAt_id))
    have hb (x:E)(he:AnalyticAt ℝ N (x,0))(v:V)(j:ℕ): jet (fun v=> N (x,v)) j v=if j=2 then N (x,v) else 0:= radiant (hK N _ he) 2 _ (hx x) _ -- may order
    have hM (v:V): avoid N v 2:= fun i hi=> (hl hn).mono fun x ht=> by rw [vertical ht,hb x ht, if_neg (by omega),mul_zero]
    refine ⟨h,hn,he,hu,funext fun ⟨x,y⟩=>?_, rfl,hM,fun v i hi => ?_,fun v i hi => ?_,?_⟩
    · change N _=N _; rw [←neg_one_smul ℝ y,hx]; ring
    · filter_upwards [hl h,hl hn,hz] with x ht he hz; rw [vertical (ht.sub he) i v, show (fun y:V=>(F-radial F) (x,y))=(fun y=>F (x,y))-(fun y => N (x,y)) from rfl,Ion.jet_minus _ _ _ _ (hK F x ht) (hK N x he),hb _ he]; interval_cases i
      · rw [jet_zero,if_neg (by decide),hz.1]; simp
      · unfold jet; rw [iteratedFDeriv_one_apply,hz.2]; simp
      rw [if_pos rfl]; change _*(N (x,v)-N (x,v))=0; rw [sub_self,mul_zero]
    · interval_cases i; exact Eventually.of_forall fun i=> sub_self _
    obtain ⟨c,hc,hp⟩:=hp; refine ⟨c,hc,fun v=>?_⟩; erw [jet_tack _ hn,vertical (x:=(0:E)) (y:=v) (i:=2) (F:=radial F) hn] -- possible zero pair
    erw [hb 0 hn,if_pos rfl]; norm_num; unfold N; linarith only [hp v]
-- Generic phase rule approximation with canonical signed χ.cost
lemma radial_earn (h:AnalyticAt ℝ F 0)(ht:∀ᶠ x:E in 𝓝 0,F (x,0)=0∧ fderiv ℝ (fun y=>F (x,y)) 0=0)(he:AnalyticAt ℝ K 0)(hc:0<(c':ℝ))(hp:∀ v,c'*‖v‖^2≤radial F (0,v)): ∃ z:ℝ,∀ R:ℝ,∃ q>0,∀ r>0,r< q→∀ x∈closedBall (0:E) R, Bill 3 (fun t=>ash μ K F t (disc t r) x - K (t•x,0)*(∫ y:V,Real.exp (-radial F (t•x,y)) ∂μ)-t^2*z):= by
    refine ⟨_,fun R=>lantern μ (coupled h ht he ⟨_,hc,hp⟩) (Eventually.of_forall fun x=> ⟨?_,fun y=>⟨fun t=> jet_smul .., rfl⟩⟩) (based_bent hc h hp) R⟩; exact (Smooth.continuousJet (fun y=>F (x,y)) 2).measurable
end Crag
end
end YM.Contacts.Lintel
