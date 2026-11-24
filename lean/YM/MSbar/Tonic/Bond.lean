import YM.MSbar.Tonic.MeterK
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Tonic
open Function Filter Whisk Lis Measuring Cacao Push Uniform Lattice RG
open Precision Gauge Midpoint Rolling Exterior Wilson Wave
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}{c f:Side}{S:StepData c f}
local notation "J"=> Positions (Primary c G)
local notation "X"=> Primary c G
local notation "Q"=> Config G f
variable (β t:ℝ)(U:Config G f)(M:Config G c)(v:S.Choices)
local notation "B₀"=> tribe S β t U v
local notation "Φ"=> wing S U v
variable (x:Positions (Primary c G))(L:List (Primary c G))(i j:Primary c G)(e:Bond c)
variable (hc:S.patch.Branches S.kernel G)
local notation "H"=>prior G f
include hc
variable (R: Rep G f)(τ A B C D:ℝ)(hR:R.Lawful τ A B C D)
-- density old milk U-term derivative `S likelihood`.
local notation "W"=> fun x:J=> postcard G c t x
local notation "i!"=>R.eval
local notation "q!"=> lid S β t G R v
include hR
-- sum-axis all t.R scaled numerator pieces. Need integral l rule
noncomputable def railV (S:StepData c f)(β t:ℝ)(R:Rep G f)(U:Config G f)(x:Positions (Primary c G)):=∑ v:S.Choices,lid S β t G R v U x
local notation "V"=>railV S β t R
lemma blend (U:Q)(x:J) : V U x= nut S β G*(S.density β U (W x)* R.eval U):=by
    unfold railV; unfold StepData.density; simp_rw [Heath.toward]; rw [Finset.sum_mul,Finset.mul_sum]; have hp: nut S β G ≠0:=(nut_pos ..).ne'; have h:S.penaltyZ β G≠0:=(S.penaltyZ_pos ..).ne'; apply Finset.sum_congr rfl; intro i _; unfold lid crew nut tribe;rw [inv_pow]; field_simp
lemma cruise (k:List J)(U:Q)(x:J): roc (V U) k x=∑ i:S.Choices, S.likelihood U i * R.eval U* roc (crew S β t U i) k x:=by
     let n:= k.length; let f(i):= lid S β t G R i U; have ht(i:S.Choices): ContDiffAt ℝ n (crew S β t U i) x:= (bean ..).exp.contDiffAt.of_le le_top
     rw [show roc (V U) k x= ∑ i:S.Choices,_ from Lis.tot n k _ f (fun i _=> (ht i).const_smul (S.likelihood U i * R.eval U)) le_rfl]; apply Finset.sum_congr rfl; intro i _; exact Lis.wed n k (S.likelihood U i * R.eval U) (crew S β t U i) (ht i) le_rfl
lemma bond (k:List J)(r:Set J)(hr:IsCompact r):(∀ x:Positions (Primary c G),Measurable (fun U:Config G f=>roc (railV S β t R U) k x)) ∧ ∃ c:ℝ,∀ x∈r,∀ U:Config G f,|roc (railV S β t R U) k x|≤ c:=by
     choose T c' h using fun v:S.Choices=> current_s β t hc R τ A B C D hR v r hr k
     have he(U:Q)(x:J): roc (railV S β t R U) k x= ∑ i:S.Choices, roc (lid S β t G R i U) k x:=by refine Lis.tot k.length k _ _ (fun i (_:i∈(univ:Finset S.Choices))=> ((bean β t U i).exp.contDiffAt.of_le le_top).const_smul (S.likelihood U i*R.eval U)) le_rfl
     simp_rw [he]; refine ⟨fun y=> Finset.measurable_fun_sum _ fun i _=>T i y,∑ i:S.Choices,c' i,fun x hx U=>?_⟩; exact (Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum (fun i _=> h i x hx U))
variable (k: List (Positions (Primary c G)))
lemma bounds : Integrable (fun U: Config G f=>roc (railV S β t R U) k x) H:=by
   obtain ⟨f,c,h⟩:=bond β t hc R τ A B C D hR k {x} (isCompact_singleton); exact Integrable.of_bound ((f x).aestronglyMeasurable) c (Eventually.of_forall (h x (Set.mem_singleton _))) -- H norm
lemma entry : let p:=fderiv ℝ (fun x=> ∫ U,roc (railV S β t R U) k x ∂prior G f) x
              HasFDerivAt (fun x=> ∫ U,roc (railV S β t R U) k x ∂prior G f) p x∧∀ a:Positions (Primary c G), p a = ∫ U, roc (railV S β t R U) (a::k) x ∂prior G f:=by
   let K(x:J)(U:Q):=fderiv ℝ (roc (railV S β t R U) k) x; let fK(U):= roc (V U) k; let Θ:= Metric.closedBall x 1; have hv:= (mem_closedBall_self (by norm_num : (0:ℝ)≤1) : x∈Θ)
   choose F c' hh using fun i:Primary c G=> bond β t hc R τ A B C D hR (bolt i::k) (closedBall x 1) (isCompact_closedBall _ _)
   let e:=∑ i,c' i; let s:Measure Q:=H; have he :0≤e:= Finset.sum_nonneg fun i _=> (abs_nonneg _).trans (hh i x hv (1:Config G f)); have ht(y:Positions (Primary c G))(hy:y∈ Θ)(U: Config G f) : ‖K y U‖≤ e:=by
       apply (K y U).opNorm_le_bound he; intro v; nth_rw 1 [spiral v]; unfold e; rw [_root_.map_sum,Finset.sum_mul]; refine (norm_sum_le ..).trans (Finset.sum_le_sum (fun i _=>?_)); rw [_root_.map_smul,norm_smul,mul_comm]; exact mul_le_mul (hh i y hy _) (norm_le_pi_norm _ _) (norm_nonneg _) ((abs_nonneg _).trans (hh i y hy U))
   have hp: Measurable (K x):=by
       let L(i:X):J→L[ℝ]ℝ:=ContinuousLinearMap.proj i; have he : K x= fun U=> ∑ i:X,(K x U (bolt i)) • L i:= by funext U; ext1 v; rw [ContinuousLinearMap.sum_apply]; nth_rw 1 [spiral v]; rw [_root_.map_sum]; apply sum_congr rfl; intro i _; rw [_root_.map_smul]; exact mul_comm ..
       nth_rw 1 [he]; exact Finset.measurable_fun_sum _ (fun i _=> (show Measurable _ from F i x)|>.smul measurable_const)
   have hg:Integrable (K x) s:= Integrable.of_bound hp.aestronglyMeasurable e (ae_of_all _ (ht x hv))
   intro p; let L:=∫ i,K x i∂s; have hK:HasFDerivAt (fun x=>∫ U,roc (V U) k x∂s) L x:=by
      refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F':=K) (μ:=s) (s:=Θ) (Metric.closedBall_mem_nhds x (by norm_num)) (Eventually.of_forall (fun x=>(bounds β t x hc R τ A B C D hR k).aestronglyMeasurable)) (bounds β t x hc R τ A B C D hR k) hg.aestronglyMeasurable (ae_of_all _ (fun a y hy=> ht y hy a)) (integrable_const _) (ae_of_all _ (fun a y hy=>?_))
      have hp: ContDiffAt ℝ (↑(1+k.length:ℕ)) (V a) y:= ContDiffAt.sum (fun i _=> ((bean β t a i).exp.contDiffAt.of_le le_top).const_smul (S.likelihood a i*R.eval a)); exact ((Lis.smooth _ 1 k hp le_rfl).differentiableAt (by simp)).hasFDerivAt
   rw [show p=L from hK.fderiv]; exact ⟨hK,fun i=> ContinuousLinearMap.integral_apply hg i⟩
end YM.MSbar.Tonic
