import YM.MSbar.Ruby.Plate
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.MSbar.Spruce
open Function Filter Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Precision Gauge Midpoint Rolling Exterior Wilson Wave Lapaz
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal Kelvin Further.GaussianScalar
variable {ι σ τ: Type} [Fintype σ][DecidableEq σ] [Fintype ι][DecidableEq ι][Fintype τ][DecidableEq τ]
variable (P:Matrix σ ι ℝ)(L:Matrix σ τ ℝ){C:Matrix τ τ ℝ}{D:Matrix ι ι ℝ} {x t y a b u c r α:ℝ}
local notation "V"=> View σ
variable {Q S F G:SpringK σ}{n p k j:ℕ}{X Y:View σ}(hQ:Kind Q)
variable (hc:C.PosDef)(hD:D.PosDef)
local notation "h"=>PowerSeries.coeff
include hQ hD
lemma grant (H: Lap p Q F)(he:Lap p S G) : Lap p (owes P D Q S X p) (owes P D F G X p) :=by
     let v(Q:SpringK σ):= picture X (Spring (confect (P*D*P.transpose) Q)); let w(Q S:SpringK σ):=owes P D Q S X p
     have hF : Kind F := by rw [Kind, ← H _ (Nat.zero_le _),hQ]
     have hu : Lap p (v Q) (v F):=by
         intro i hi; unfold v picture; rw [PowerSeries.coeff_map,PowerSeries.coeff_map,Cacao.goodie P X hD hQ,Cacao.goodie P X hD hF,H.boots i hi]
     have hv:Lap p (w Q S *v Q) (w F G *v F) := by
          intro i hi; unfold w v owes picture; rw [← map_mul, ← map_mul,PowerSeries.coeff_map, PowerSeries.coeff_map,Cacao.aromaEval P X hD Q S hQ (by omega), Cacao.aromaEval P X hD F G hF (by omega),he.rises H.boots i hi]
     let v':=Spring (picture X (confect (P*D*P.transpose) Q)); have hz:v Q=v':=by unfold v v'; rw [show picture _ _=PowerSeries.map (aeval (R:=ℝ) X).toRingHom (Spring _) from rfl]; exact (sunshine (aeval (R:=ℝ) X)).symm
     have hI : Kind (picture X (confect (P*D*P.transpose) Q)):=by rw [Kind, picture, PowerSeries.coeff_map,Cacao.sugar _ hQ, map_zero]
     obtain ⟨A,hA⟩:=Cacao.solitary _ hI
     have he : Lap p (w Q S *v Q) (w F G *v Q):= fun i hi=>(hv i hi).trans ((Lap.rises (k:=p) (f:=(w F G)) (g:=w F G) (fun i _=> rfl) hu i hi).symm)
     have hξ: Lap p ((w Q S * v Q) * (↑(A⁻¹:(PowerSeries ℝ)ˣ):PowerSeries ℝ)) ((w F G *v Q)* (↑(A⁻¹:(PowerSeries ℝ)ˣ):PowerSeries ℝ)):= Lap.rises he (fun i _=> rfl)
     simp_rw [show v Q =↑A from hz.trans hA.symm,mul_assoc,Units.mul_inv,mul_one] at hξ; exact hξ
omit hQ hD
noncomputable def vestal (p:ℕ)(f:SpringK σ):SpringK σ:= PowerSeries.mk fun i=> if i ≤ p then PowerSeries.coeff i f else 0
private lemma last (A:SpringK σ): Lap p A (vestal p A):= fun i hi=>by rw [vestal,PowerSeries.coeff_mk,if_pos hi]
noncomputable def cardK(p j:ℕ)(u t:ℝ):=Whisk.driver j (p+1+p) 1 u (t+t)
variable {n':Side}{l:σ→Site n'}{z: Site n'} {δ:ℝ}
local notation "Q!"=>vestal p Q
local notation "S!"=>vestal p S
include hQ hD hc
variable (hg :Gain l z a b k (P*D*P.transpose) (L*C*L.transpose) u δ) (hm: ‖X‖ ≤ x)(hk:‖Y‖ ≤ x)
include hm hk hg
lemma joker (hy:0 ≤ y)(hY:∀ i,|X i-Y i|≤ y*Eve b z (l i))(hX :∀ i ≤ p, Tokew l (a+b) k j 0 (PowerSeries.coeff i Q) t ∧ (PowerSeries.coeff i Q).totalDegree ≤ j)(hS:∀ i≤p,Vault l {z} (a+b) k j 0 (PowerSeries.coeff i S) t ∧ (PowerSeries.coeff i S).totalDegree ≤ j)(ht:0 ≤ r)(he:r ≤1):
       |taste p (owes P D Q S X p) r - taste p (owes L C Q S Y p) r|≤ (p+1:ℕ)*(cardK p j u (t*(1+x)^(j+1))*(δ+y)):=by
     let Q':=Q!; let S':=S!; let U:= t*(1+x)^(j+1); have hz:0 ≤ x:= (norm_nonneg X).trans hm; have hp : Kind Q':=(last (p:=p) Q _ (Nat.zero_le _)).symm.trans hQ
     let A:=Metric.closedBall (0:V) x; let V' (w :V)(m:ℕ)(f: Pot σ) := Vault l {z} (a+b) k m w f U; let D' (w:V)(m:ℕ)(f:Pot σ):= Tokew l (a+b) k m w f U; have he' : 0 ≤ a+b :=add_nonneg hg.sober hg.green; have ht':0 ≤ t:= (hX 0 (Nat.zero_le ..)).1.1; have hU:0≤ U:=by unfold U; positivity
     have hS' (w:V)(he:w∈ A)(m i:ℕ) : V' w m (h i S') ∧(h i S').totalDegree≤ j:=by
           dsimp only [S',vestal]; rw [PowerSeries.coeff_mk]; split_ifs with ht; exact ⟨Bout.across _ (hS _ ht|>.1) he' (by simpa only [sub_zero,dist_zero_right] using Metric.mem_closedBall.mp he) ((hS _ ht).2) m,(hS _ ht).2⟩ -- simp norm
           exact ⟨Quote.nill hU,(MvPolynomial.totalDegree_zero|>.trans_le (Nat.zero_le _))⟩
     have hT (w:V)(he:w∈ A)(m i:ℕ) : D' w m (h i Q') ∧(h i Q').totalDegree≤ j:=by
           unfold Q' vestal; rw [PowerSeries.coeff_mk];split_ifs with hh
           · obtain ⟨hp,hb⟩:=hX i hh; refine ⟨⟨hU,fun i=>?_⟩, hb⟩; exact Bout.across _ (hp.2 i) he' (by simpa only [sub_zero,dist_zero_right] using Metric.mem_closedBall.mp he) (pdeg i (hb.trans (Nat.le_succ _))) _
           exact ⟨⟨hU,fun i=> by rw [_root_.map_zero]; exact Quote.nill hU⟩,MvPolynomial.totalDegree_zero.trans_le (Nat.zero_le _)⟩ -- rw map zero
     let d:=p+1+p; have h1:X∈A:=by simpa only [A,Metric.mem_closedBall,dist_zero_right]
     have h2:Y∈A:=by simpa only [A,Metric.mem_closedBall,dist_zero_right]
     have hw : Expanse Q' j d:=by
           refine ⟨fun i hi=> ?_⟩; by_cases hz:i=0; subst i; rw [hp,totalDegree_zero];omega
           have hu:= hT X h1 i i|>.2; exact hu.trans (le_trans (le_mul_of_one_le_right (Nat.zero_le _) (show 1≤ i by omega)) (by omega))
     have hv :Expanse (Q'+PowerSeries.X^(p+1)*S') j d:=by
           constructor; intro i hi; rw [map_add]; apply (totalDegree_add ..).trans; refine max_le (hw.profile i hi) ?_; rw [PowerSeries.coeff_X_pow_mul'];split
           · expose_names; have hi':1 ≤ i:=by omega
             exact le_trans ((hS' X h1 i _).2) (le_trans (le_mul_of_one_le_right (Nat.zero_le _) hi') (by omega))
           rw [totalDegree_zero];omega
     let O:=owes P D Q S X p; let E:= owes L C Q S Y p; let v:= cardK p j u U*(δ+y); have hV(i:ℕ)(hi:i≤p): |PowerSeries.coeff i O-PowerSeries.coeff i E|≤ v:=by
           rw [show PowerSeries.coeff i O= _ from (grant (X:=X) P hQ hD (last (p:=p) Q) (last S) i hi), (show PowerSeries.coeff i E= _ from grant L (X:=Y) hQ hc (last (p:=p) Q) (last S) i hi)]; unfold owes picture; rw [PowerSeries.coeff_map,PowerSeries.coeff_map]; exact transferPin hp hg hw (Nat.zero_lt_succ _) hv (fun i hi a ha=> (hS' i hi _ a).1) (fun i hi a ha=> (hT i hi _ a).1) (by omega) h1 h2 (convex_closedBall ..) hy hY
     unfold taste; rw [←sum_sub_distrib]; refine (abs_sum_le_sum_abs ..).trans ((sum_le_sum (g:=fun _=>v) (fun i hi=>?_)).trans_eq ?_); · rw [←mul_sub,abs_mul]; rw [← one_mul v]; exact mul_le_mul (by rw [abs_of_nonneg (pow_nonneg ht _)]; exact pow_le_one₀ ht he) (hV i (Nat.le_of_lt_succ (mem_range.mp hi))) (abs_nonneg _) zero_le_one
     rw [sum_const,card_range,nsmul_eq_mul]
end YM.MSbar.Spruce
