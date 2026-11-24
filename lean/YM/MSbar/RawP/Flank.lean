import YM.MSbar.RawP.KernelC
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.RawP
open Function Filter Whisk Lis Measuring Cacao Aqua Push Uniform Lattice RG
open Precision Gauge Midpoint Rolling Exterior Wilson Wave Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}{n:Side} {a b C Z B w K r:ℝ}{p k:ℕ}
open Metric Pressure AnalyticBridge.SectorAffine.Offset
local notation "W₀"=>Positions (Primary n G)
variable (R:Rep G n) {W K ξ δ:ℝ}{Θ:Set (Positions (Primary n G))}
variable {P:BudgetPoint}{F:Activities G n}(hF:F.Valid P δ ξ)(hS:IsOpen Θ)(hA:Bash Θ P)(hc:Convex ℝ Θ)(x:Positions (Primary n G))(hx:x∈Θ)(hp:p≤ P.order)
variable (hb:0<b)(hw: 3*b*p*(4*P.B+2:ℕ) ≤ P.supportExponent)
local notation "I"=> Measuring.chart n G
noncomputable def flank (g:RegularAddress n)(P:BudgetPoint):= coverNumber P.B g.support*(4*P.B+2)+2*P.B
noncomputable def cork (G:Gauge)(P:BudgetPoint)(p:ℕ)(b:ℝ) := Real.exp (3*b*p*(2*P.B:ℕ))*earnE P G p
local notation "γ"=> cork G P p b
include hb hw hF hS hA hc hx hp
lemma arcs : Roil (arc F P) p b x (γ*(δ*countCost b)):=by
   obtain ⟨T,hT,ht⟩:= hF.boundE; have hi(i):=(hF.regular.smooth i)
   have he:= heir hF hS hc hA x hx p hp; let y:= arc F P; let W(i):= Program (F.E i)
   have hh(i):Requests Set.univ (W i) (Measuring.chart n G) (F.reg i).site (flank (F.reg i) P):=by
        intro a _ b _ h; apply (hi i).sites; intro v hh' he
        change _=palace b v; apply Eq.trans (Work.F03.represent_link ((tint G _) a) v); refine Eq.trans (congr_arg G.lieExp (?_: tint G _ a (v.1, Exterior.coord v.2)= tint G _ b (v.1, Exterior.coord v.2))) (Work.F03.represent_link ((tint G _) b) v|>.symm); ext k; apply h; exact Corona.extent (F.reg i).support P.B (F.reg i).anchor hh'
   let C (i):= P.mass (F.reg i).support (T i); let f(z:Site n)(i:ℕ):= if (F.reg i).site=z then C i else 0
   have hV(i) :Through p (W i) x (earnE P G p*T i):= fluxP (hi i) (hT i) (d:= F.reg i) (show Healthy P.threshold _ (palace x) from (by unfold Healthy; rw [(hA x hx).2];simp)) hp (hA x hx|>.1)
   have hY := floorP G P p; have hv:0 ≤ γ:=by unfold cork; positivity
   have hD :0 ≤ δ:= (tsum_nonneg (fun i=> (ht (0:Site n)).1 i)).trans ((ht (0:Site n)).2.2)
   refine ⟨he.1,mul_nonneg hv (mul_nonneg hD (count_pos hb|>.le)),fun v L hl=>?_⟩
   let q:=L.length+1; have hk:(v::L).length ≤ p:=by rw [List.length_cons]; omega
   let g(z:Site n):= Decay b (I v) z; -- ψ means local `I` fix
   have hg:= decay_count hb (I v); let v':=raiseQ I b (v::L); have hP₀:0≤v':=(Real.exp_pos _|>.le)
   let fL(i:ℕ):= buoy (W i) x (v::L); have hn:HasSum fL (buoy y x (v::L)):=by
       have hv:= (ContinuousMultilinearMap.apply ℝ (fun _ :Fin (v::L).length=> Positions (Primary n G)) ℝ (fun j=> Uniform.bolt ((v::L).get j))).hasSum (he.2 (v::L).length hk); unfold buoy; rw [fEntry he.1 _ hk]; apply hv.congr_fun; intro i; unfold fL buoy; rw [fEntry (hV i|>.1) _ hk]; rfl
   let X(i:ℕ):=∑ p:Site n,g p*f p i; have hx:Summable X:= summable_sum fun i _=> (show Summable (f i) from (ht i).2.1).mul_left _
   let Y(i:ℕ):= γ * X i *v'
   have hU(i:ℕ) : ‖fL i‖≤ Y i:=by
       let k':=(F.reg i).site; have ht:= riseA (hV i) (hh i) (show 0 ≤ 3*b from (by positivity)); have hA := ht _ hk ((v::L).get); have h₀ : earnE P G p*T i* Real.exp ((3*b:ℝ)*(p*flank (F.reg i) P:ℕ)) ≤ γ*C i:=by
            unfold cork C BudgetPoint.mass flank; push_cast; rw [show Real.exp _ * earnE P G p * _= earnE P G p*T i*(Real.exp (3*b*p*(2*(P.B:ℝ))) *Real.exp (P.supportExponent* coverNumber P.B (F.reg i).support)) from by ring, ← Real.exp_add]; refine mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) (mul_nonneg hY (hT i).1); have hh:= mul_le_mul_of_nonneg_right hw (Nat.cast_nonneg (α:=ℝ) (coverNumber P.B (F.reg i).support)); push_cast at hh; linarith only [hh]
       have hu:0 ≤ γ*C i:=mul_nonneg hv ((hT i).1.trans (P.loMass (F.reg i).support (T i) (hT i).1)); unfold fL buoy; rw [fEntry (hV i|>.1) _ hk]; refine hA.trans ((mul_le_mul h₀ (ropeCost v L hb.le) (Real.exp_pos _|>.le) hu).trans_eq ?_); unfold Y X; have he:(∑ p:Site n,g p*f p i)=g k'*C i:=by unfold f;simp [mul_ite,k']
       rw [he]; unfold g k' v'; ring
   have hv := (hx.mul_left γ).mul_right v'; have hp:=hv.of_nonneg_of_le (fun i=> norm_nonneg (fL i)) hU
   rw [←hn.tsum_eq]; refine le_trans ((norm_tsum_le_tsum_norm hp).trans (hp.tsum_le_tsum hU hv)) ?_; unfold Y; rw [tsum_mul_right,tsum_mul_left]; refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (mul_nonneg (Real.exp_pos _|>.le) hY)) hP₀
   unfold X; rw [Summable.tsum_finsetSum (fun i _=>(show Summable (fun j=>g i*f i j) from ((ht i).2.1.mul_left _)))]; simp_rw [tsum_mul_left]; apply le_trans (Finset.sum_le_sum (g:=fun i=>g i*δ) _); · rw [← Finset.sum_mul]; exact (mul_le_mul_of_nonneg_right hg hD).trans_eq (mul_comm ..)
   exact fun z _=> mul_le_mul_of_nonneg_left (ht z|>.2.2) (decay_pos ..|>.le)
end YM.MSbar.RawP
