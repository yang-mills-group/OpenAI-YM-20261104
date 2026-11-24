import YM.MSbar.Tonic.Grove
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
-- normalised response.Pl.Ψ. costs.
-- ∂ S.push exactly ratio.E normalized weighted.; envelope meas + arbitrary ∆`p.Prove by dominating even F envelop, fderiv under Integral.S.G.C intercept. technical params mat norm use auxiliary param lemma.
variable {E F Z:Type}[NormedAddCommGroup E][NormedAddCommGroup F][NormedSpace ℝ E][NormedSpace ℝ F]
lemma contour (f:E× F→ℝ)(z:E)(l:List E)(x:F) (he:ContDiff ℝ ω f) : roc (fun y=>f (y,x)) l z=roc f (l.map fun i=>(i,(0:F))) (z,x):=by
    induction l generalizing z with |nil=>rfl|cons a L ih=>
         let u(y:E):=(y,x); let g:=L.map fun i=>(i,(0:F)); let V:= (ContinuousLinearMap.id ℝ E).prod (0:E→L[ℝ] F); have hv: HasFDerivAt u V z:= (hasFDerivAt_id ..).prodMk (hasFDerivAt_const x z); have hh:DifferentiableAt ℝ (roc f g) (z,x):= (Lis.smooth (1+g.length) 1 g (he.contDiffAt.of_le le_top) le_rfl).differentiableAt (by simp)
         let F(y:E):=f (y,x); rw [roc, List.map_cons,Lis.roc]; rw [show roc F L=_ from (show roc F L=roc f g ∘ u from funext ih)]; rw [fderiv_comp _ (show DifferentiableAt ℝ _ (u z) from hh) hv.differentiableAt,hv.fderiv];rfl
lemma cotton (f:E×F→ℝ)(l:List E)(he:ContDiff ℝ ω f) : Continuous (fun z:E× F=> roc (fun y=>f (y,z.2)) l z.1) :=by simp_rw [fun z x=> contour f z l x he,Prod.mk.eta]; exact continuous_iff_continuousAt.mpr fun x=> (Lis.smooth ((l.map fun i=>(i,(0:F))).length) 0 _ (he.contDiffAt.of_le le_top) (by omega)).continuousAt
noncomputable def meterK (U:Config G f)(v:S.Choices)(r:ℝ)(x:Positions (Primary c G))(l:List (Primary c G)):= buoy (crew S β r U v) x l
variable (hc:S.patch.Branches S.kernel G)
local notation "H"=>prior G f
include hc
-- continuous in M.Shear. estimate comp sensor normal.C. `powers.R.Pos`.Need region open.
lemma senses (s:Set J)(hg:IsCompact s) (v:S.Choices) (p:List (Positions (Primary c G))) : (∀ x:J, Measurable (fun U:Config G f=> roc (crew S β t U v) p x))∧∃ C:ℝ,∀ x∈s,∀ U:Q,|roc (crew S β t U v) p x|≤ C:=by
     let f'(x:J × (Bond c→ G.Mat)):= Real.exp (plateV S β t x.2 x.1); let g(x:J × (Bond c→G.Mat)):=roc (fun y=>f' (y,x.2)) p x.1; have he(U:Q): crew S β t U v= fun x=>f' (x,wing S U v):=by unfold crew; rw [lines]; -- defeq
     have hx(U:Q)(x:J): roc (crew S β t U v) p x=g (x, wing S U v):=by rw [he]; -- syntax
     have hp:Continuous g:= cotton f' p ((river β t S).exp)
     let T:=s ×ˢ (Set.univ.pi (fun _ : Bond c => Set.range G.mat)); obtain ⟨C,hC⟩:= ((hg.prod (isCompact_univ_pi (fun i=> isCompact_range G.continuous_mat))).image hp.abs|>.bddAbove)
     let L(q: Config G c):=(fun i=>G.mat ((q i)⁻¹)); have hL:Continuous L:= continuous_pi (fun i=>G.continuous_mat.comp ((continuous_apply i).inv)); have hQ(x:J):Continuous (fun u:Config G c=> g (x,L u)):=by apply hp.comp (f:=fun u: Config G c=>(x,L u)) (continuous_const.prodMk hL); -- syntax
     simp_rw [hx]; exact ⟨fun x=> (hQ x).measurable.comp (S.prediction_meas hc v),C,fun z hz U=> hC ⟨(z,wing S U v),⟨hz,fun i _=>⟨(S.prediction U v i)⁻¹,rfl⟩⟩,rfl⟩⟩
variable (R: Rep G f)(τ A B C D:ℝ)(hR:R.Lawful τ A B C D)
-- density old milk U-term derivative `S likelihood`.
local notation "W"=> fun x:J=> postcard G c t x
local notation "i!"=>R.eval
noncomputable def lid (S :StepData c f)(β t:ℝ)(G:Gauge)(R : Rep G f)(v:S.Choices)(U:Config G f)(y:Positions (Primary c G)) := (S.likelihood U v * R.eval U)*crew S β t U v y
local notation "q!"=> lid S β t G R v
include hR
lemma current_s (v:S.Choices)(k:Set J)(hk:IsCompact k)(p:List (Positions (Primary c G))) : (∀ x:Positions (Primary c G),Measurable (fun U:Config G f=>roc (lid S β t G R v U) p x))∧ ∃ C:ℝ,∀ x∈ k,∀ U:Config G f, |roc (lid S β t G R v U) p x| ≤ C :=by
    let L(U:Q):= S.likelihood U v; have hp(U:Q): |L U| ≤ 1 :=by rw [abs_of_nonneg (S.likelihood_pos ..), ← S.chosen hc U]; exact Finset.single_le_sum (f:=S.likelihood U) (fun z _=> S.likelihood_pos ..) (mem_univ _)
    have hv:Envelope R.eval:= R.envelope hR; obtain ⟨b,hb⟩:=hv.cost; obtain ⟨T,t',hT⟩:=senses (t:=t) β hc k hk v p -- shadow t
    have he(U:Q)(x:J): roc (lid S β t G R v U) p x= L U*R.eval U*roc (crew S β t U v) p x:=by apply Lis.wed p.length p (L U *R.eval U) (crew S β t U v) ((bean ..).exp.contDiffAt.of_le le_top) le_rfl
    simp_rw [he]; refine ⟨fun x=> ((S.likelihood_meas hc v).mul hv.meas).mul (T x), b *t', fun x hx U=>?_⟩; rw [abs_mul,abs_mul]; exact mul_le_mul ((mul_le_mul (hp U) (hb U) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)) (hT x hx U) (abs_nonneg _) ((abs_nonneg _).trans (hb U))
end YM.MSbar.Tonic
