import YM.OPE.Compatible.Porch.Love
/-! # sparse tail budget in R -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Zeph
open Function Filter Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Matrix Bloch Precision Exterior Tree
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra GaussianScore Metric Push Push.AbsoluteSums
variable {G:Gauge}{c f:Side}
attribute [local instance] Gauge.frobInner
open Radial Flume.Virgin Set
open PhysicalNext.Repeat.Aroma
open YM.AnalyticNext.QuarticMatch Radius Radius.Articles Radius.Polish Radius.Fetch Radius.Showroom Estimate Sheets Radius.Model
open Woody Next.Free Finset Work.F03 Progress.StationaryScenes AnalyticNext.QuarticMatch.Local
variable {t r R B b ε:ℝ}{m:ℕ}
variable (S:StepData c f) (F: Forest S.ratio) {k:S.Choices}
local notation "Q" =>(Bid.Dir G c × AxisChart G F)
namespace Dew
open Green(wt)
structure ShadeQ (x:Q)(X:Finset (Site f)) :Prop where
      shore : ∀ i, S.ratio.embed (i.1)∉X→ x.1 i=0
      lilac : ∀ i:F.Free, i.val.1∉ X → x.2 i=0
abbrev Glans (A:Finset (Site f))(B t:ℝ)(i:Site f):ℝ:=∑ j∈A,B*(wt t i j)⁻¹
variable {S F}
lemma glansHi {A:Finset (Site f)}(ht:0≤B):0 ≤ Glans A B t:=fun i=>sum_nonneg fun j _=> mul_nonneg ht (inv_nonneg.mpr (Green.wt_pos t i j).le)
lemma glansM {x:Q}{A: Finset (Site f)} (hp:ShadeQ S F x A)(hx:‖x‖≤ B) (i: Site f): On S F G t i x (Glans A B t i):=by
       have h:0≤ B:=(norm_nonneg _).trans hx
       have he(j:Site f)(hj:j∈A):B≤ Glans A B t i*wt t j i:=by
            let a:=wt t i j; have he :0<a:=Green.wt_pos ..; rw [Green.wt_symm]; refine (le_of_eq ?_).trans (mul_le_mul_of_nonneg_right (single_le_sum (fun j (hh:j∈A)=>mul_nonneg h (inv_nonneg.mpr (Green.wt_pos t i j|>.le))) hj) he.le); rw[mul_assoc,inv_mul_cancel₀ he.ne',mul_one]
       constructor
       · intro j; by_cases h': S.ratio.embed j.1∈A; · exact (norm_le_pi_norm ..).trans (((le_max_left ..).trans hx).trans (he _ h'))
         rw [hp.shore j h', norm_zero]; exact mul_nonneg (glansHi h _) (Green.wt_pos ..).le
       intro j; by_cases h':j.val.1∈A; · exact (norm_le_pi_norm ..).trans (((le_max_right ..).trans hx).trans (he _ h'))
       rw [hp.lilac j h', norm_zero]; exact mul_nonneg (glansHi h _) (Green.wt_pos ..).le
lemma sumGlans (X:Finset (Site f))(ht:0<t)(hB:0≤B): ∑ i, Glans X B t i≤ (X.card:ℝ)*(B*Premium.overall t):=by
       have hx(j:Site f):(∑ i:Site f,(wt t i j)⁻¹)≤ Premium.overall t:=by simpa using Premium.lives 1 ht j
       unfold Glans; rw [sum_comm, show (X.card:ℝ)*(B*Premium.overall t)=∑ _∈X,(B*Premium.overall t) from by rw [sum_const,nsmul_eq_mul]]; apply sum_le_sum; intro i _; rw [←mul_sum]; exact mul_le_mul_of_nonneg_left (hx i) hB
abbrev paying (X:Finset (Site f))(B t:ℝ):=(X.card:ℝ)*(B*Premium.overall t)
lemma fundGlans (X:Finset (Site f))(ht:0<t)(hB:0≤B)(n:ℕ)(hn:0 < n): ∑ i: Site f,(Glans X B t i)^n≤paying X B t ^n:=by
       obtain ⟨n,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn); let p:=Glans X B t; let b:= paying X B t; have he(i:Site f):0 ≤ p i:=glansHi hB _; have hp(i:Site f): p i ≤ b:=(single_le_sum (f:=p) (fun i _=> he _) (mem_univ i)).trans (sumGlans X ht hB); change ∑ i,(p i)^(n+1) ≤ b^(n+1); simp_rw [pow_succ]; refine (sum_le_sum (fun i _=> mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (he i) (hp i) _) (he i))).trans ?_; rw[← mul_sum]; exact mul_le_mul_of_nonneg_left (sumGlans X ht hB) (pow_nonneg ((he 0).trans (hp 0)) _)
variable {Y: (Bid.Dir G c × AxisChart G F)→ℝ} {f': Site f → (Bid.Dir G c × AxisChart G F)→ℝ}
-- key pay.S
lemma sparsity (H:Pile S F r R t m Y f')(ht:0<t)(hr:0 ≤ R)(x:Q)(X:Finset (Site f))(hX: ShadeQ S F x X)(hx:‖x‖ ≤ B)(hε:0<ε)(hf:ε*B < r)(k:ℕ)(hk:k+1 ≤ m):
        (‖Y (ε • x)-∑ i∈ range (k+1), ε^i*jet Y i x‖ ≤ R*(paying X B t)^(k+1)*ε^(k+1)) ∧ ∀ i : ℕ, 0 < i → i ≤ m → ‖jet Y i x‖ ≤ R*(paying X B t)^i:=by
              have hz : ε*‖x‖ < r := (mul_le_mul_of_nonneg_left hx hε.le).trans_lt hf; have he :0 ≤ B:=(norm_nonneg _).trans hx; let p:= Glans X B t; have hy(i):= glansM (t:=t) hX hx i; have hp:0 ≤ p:= glansHi he; exact ⟨(H.SignedLaw hr x hε hz p hp hy k hk).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (fundGlans X ht he (k+1) (by omega)) hr) (pow_nonneg hε.le _)),fun i hi hM=> (H.atX x ((mul_nonneg hε.le he).trans_lt hf) p hp hy i hM).trans (mul_le_mul_of_nonneg_left (fundGlans X ht he i hi) hr)⟩
end Dew
end YM.OPE.Zeph
