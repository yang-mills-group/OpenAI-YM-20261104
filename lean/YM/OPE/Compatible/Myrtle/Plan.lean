import YM.OPE.Compatible.Myrtle.Poss
/-! # Staging clock. Identity directions.Travellers -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Raucous.Host
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge Tree Push Push.AbsoluteSums Precision Matrix Exterior
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius ENNReal
open PertExtension Series Libra GaussianScore Metric Limn Cinders
variable {G:Gauge}{c f:Side}{I:Type}
attribute [local instance] Gauge.frobInner
open Radial Flume.Virgin
open PhysicalNext.Repeat.Aroma
open YM.AnalyticNext.QuarticMatch Radius Radius.Articles Radius.Polish Radius.Fetch Radius.Showroom Estimate Sheets Radius.Model
open Woody Next.Free Finset Work.F03 Progress.StationaryScenes AnalyticNext.QuarticMatch.Local Cascade Rill Glass Coin Votive Stationary
variable {i m j:ℕ} {s t r R e d b b' v u z x a C:ℝ}
open Zeph Dew
variable {K:Sponsor G}{T:Seasons K}
variable (L:Host K T)(X:Seats L.ForestQ)
set_option quotPrecheck false
noncomputable abbrev Jure := quart (PatchM L.Z L.H L.A L.U L.k L.F X) (Chart.tangent G (X:Type))
local notation "μ"=>Jure L X
namespace Rich
variable {X L}
variable (h:L.Rich s b e b' u C)(ht:0<s)(hb:0 ≤ b)(he:0<e)(X:Seats L.ForestQ)
include h ht hb he
local notation "Vk"=>Keys G (X:Type)
lemma takeK(i:Rubric G X): (PatchM L.Z L.H L.A L.U L.k L.F X).wick (castAt (Tip G (↥X)) i) (castAt (Tip G (↥X)) i) ≤ C:=by
      have hp:=h.Cov_E ht hb he X i i; simp [Green.wt] at hp; exact (le_abs_self _).trans hp
lemma DustK (x:ℝ)(hx:0 ≤ x): (Jure L X).real {p: Vk | crestPrice G x < ‖p‖} ≤ ((X.card:ℝ)*(Fintype.card G.ColorIndex))* (2*Real.exp (C/2)*Real.exp (-x)):=by
      let w(i:Rubric G X):= castAt (Tip G (↥X)) i; let A(i:Rubric G X): Set Vk:= {p|x < ‖w i p‖}; have hz(i:Rubric G X): (Jure L X).real (A i)≤ 2*Real.exp (C/2)*Real.exp (-x):= (defeat _ _ (w i) x).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.exp_monotone (div_le_div_of_nonneg_right (h.takeK ht hb he X i) (by norm_num))) (by norm_num)) (Real.exp_nonneg _)); have he:{p: Vk|crestPrice G x < ‖p‖} ⊆ ⋃ i,A i:=by
           intro p hp; rw [mem_iUnion]; by_contra h'; push Not at h'; exact hp.not_ge (Tip_T p hx (fun i=>(not_lt.mp (h' i)))) -- hp.not_ge explicit?
      refine (measureReal_mono he).trans ((measureReal_iUnion_fintype_le A).trans ?_); apply (sum_le_sum (fun i _=>hz i)).trans_eq; rw [sum_const,card_univ,nsmul_eq_mul,Fintype.card_prod,Fintype.card_coe,Nat.cast_mul]
lemma DustP (j:ℕ)(hj:0 < j): Fault (Jure L X) j (fun p: Keys G (↥X)=>‖p‖) ( (X.card*(Fintype.card G.ColorIndex):ℝ)*(Real.sqrt C*ampleP j)) :=by
       let D:=Tip G (↥X); let a(i:Rubric G X):= castAt D i; have hP(i:Rubric G X): Fault (Jure L X) j (fun p:Vk=> ‖a i p‖) (Real.sqrt C*ampleP j):= by
            refine Fault.NormT (Lal _ _ _ (Real.sqrt_nonneg _) ?_ hj); rw [Real.sq_sqrt h.vein.broad.le]; exact h.takeK ht hb he X i
       let f(i:Rubric G X)(p:Vk):=‖a i p‖
       have hQ(p:Vk): ‖p‖≤ ∑ i, f i p:=by
            refine (pi_norm_le_iff_of_nonneg (sum_nonneg (f:=fun j:Rubric G X=>f j p) (fun j _=>norm_nonneg _))).2 ?_; intro i; let T:= EuclideanSpace.basisFun G.ColorIndex ℝ; rw [←T.sum_repr (p i)]; apply (norm_sum_le ..).trans; rw [Fintype.sum_prod_type]; refine le_trans (le_of_eq (Finset.sum_congr rfl (g:=fun j=>f (i,j) p) fun j _=>?_)) (single_le_sum (f:=fun j:(X:Type)=>∑ y:G.ColorIndex,f (j,y) p) (a:=i) (fun j hj=>sum_nonneg (fun _ _=>norm_nonneg _)) (mem_univ _)); unfold f; change ‖_‖=‖cash (Tip G (↥X)) p (i,j)‖; rw [Tip_ψ,norm_smul,OrthonormalBasis.norm_eq_one,mul_one];rfl
       have hv:=(Fault.sum Finset.univ f _ (fun i _=> hP i) hj).ofLe (continuous_norm.aestronglyMeasurable) (Eventually.of_forall (fun (p:Vk)=>by rw[Finset.sum_apply,norm_norm]; exact (hQ p).trans (Real.le_norm_self _)))
       rw [sum_const,nsmul_eq_mul,card_univ,Fintype.card_prod,Fintype.card_coe,Nat.cast_mul] at hv; exact hv
end Rich
end YM.OPE.Raucous.Host
