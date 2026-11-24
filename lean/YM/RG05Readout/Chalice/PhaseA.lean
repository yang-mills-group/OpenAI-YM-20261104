import YM.RG05Readout.Chalice.Span
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Chalice
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Cells Overlay
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons
open Records Basket Halls Shadow Flatten
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}
    {b k l:ℕ}{Q:ℝ}(h:C.Makes){D: Address.Rail C}{B:ℕ→ℕ→ℝ}
set_option quotPrecheck false
open Pulse Extraction Extraction.Lease
open Push.RelayDifference
variable {D:Address.Rail C}

variable {f: Extraction.Order}

/-! A transcription at common origin: affordable → vetted literal against calibrated matrices, absorb a finite bank then same at ALL higher SBP orders on-demand. For low-weight planes repaint them further. -/
open Petals Petals.Kernel Bay Dash
/-! Pass regulators. Manifest erasures with every stencil estimate
 first keep the exact witnesses, can sum in actual volume. Then FD weak
 limit at all orders needed for the reading, no collision costs. -/
variable {v:ℕ}
local notation "V"=> Fin v
local notation "U"=> Fin n
local notation "Z"=> C.side N p
variable (F':Test (v+n))(s:Fin v→ℕ)(F:(i:Fin v)→Leafage C (s i))
-- norm on multi.C continuously.Thin.Sigma
lemma touchS (p':Wave V): Continuous ((multi C m N p s (fun i=> F i (N,p))) p'):=by
    unfold multi; rw [LinearMap.smul_apply,LinearMap.sum_apply]; apply Continuous.const_smul; simp_rw [Finset.sum_fn]; apply continuous_finsetSum; intro i _; let y:= fun a:V=> F a (N,p); let a₀:=fork (C.S.a N) (fun j=>C.S.place (i j)) p'
    have he (j:V)(k:Mark C (s j)) : Continuous (Pulse.key C N p (s j) (y j) k (i j)):=by
        unfold Pulse.key; apply Continuous.const_smul; unfold stepUp Motion.scalar; simp only [Bool.false_eq_true, ↓reduceIte]; exact ((C.localSection (kept k.fst)).continuous_places _ _).comp (continuous_pull ..)
    change Continuous (fun U₀=>∑ j':((j:V)→Mark C (s j)), (perform _ _ a₀).val 0*∏ j:V, Pulse.key C N p (s j) (y j) (j' j) (i j) U₀); apply continuous_finsetSum; intro j _; exact continuous_const.mul (continuous_finsetProd _ fun i _=> he i _)
lemma touch_sheet (u:V→Trial C)(ht:∀ i z, Continuous (u i N p z))(p':Wave V) : Continuous (sheet p' C u N p) := continuous_const.mul (continuous_finsetSum _ (fun _ _ => continuous_const.mul (continuous_finsetProd _ fun i _=> ht i _)))
-- Height load for spec
variable (p₀: Fin n→ C.book.Token)
include h
lemma truth_sober {d:ℕ} (x:C.label d): Reveals C f (visits C d x) (d:=d) (fun _=> x):=by
    let z:Rowe C d:=fun _=>x; let v:= Bid.visits C d x; apply And.intro (Stencilled.visits h _); refine ⟨⟨‖x‖,Eventually.of_forall fun i=> Eventually.of_forall (fun _=>le_rfl)⟩,0, UVExt.Slots.manifest_zero C, ⟨∅, Eventually.of_forall fun i=> ⟨fun _ _=>rfl,fun x=>Interior.constant _ _⟩⟩,?_⟩
    change Bid.close C f (v-0-v); rw [sub_zero,sub_self]; refine ⟨(fun _ _=>0),tendsto_const_nhds,fun i m=> ⟨m,le_rfl,Eventually.of_forall (fun p=> ?_)⟩⟩
    filter_upwards [f.mesh.cofinal.eventually_ge_atTop m] with j hj; refine ⟨hj,fun T hT hv x hx=>?_⟩; refine ⟨Interior.constant (G:=G) _ 0,?_⟩; have H:=Next.Extract.root_smul T (C.beta (f.mesh j) (f.per p)) (G:=G) 0 0; simp only [zero_smul, norm_zero,zero_mul] at H; exact H.le
variable {w:Worth}{r:ℕ→ℕ}(Y:OPE.Package C w r D)(hG:G.Simple)(W:CenterPort C f) (hf:∀ i:Fin v,Slow C f (F i))
local notation "I!"=> Cutoffs
local notation "Ω"=> f.fuse
local notation "κ"=> (∑ i:U,(p₀ i).1)
local notation "g"=> Fin.append s (fun i=>(p₀ i).1)
def outfits (F:∀ i:Fin v,Rowe C (s i)) (j: Fin (v+n)) : Rowe C (Fin.append s (fun i=> (p₀ i).1) j):=
    Fin.addCases (motive:=fun j => Rowe C (Fin.append s (fun i=> (p₀ i).1) j)) (fun i=>fun u=> Dash.Shot.Tilt C.book _ _ ((Fin.append_left ..).symm) (F i u)) (fun i _=> Dash.Shot.Tilt C.book _ _ ((Fin.append_right ..).symm) (p₀ i).2) j
local notation "Z₁"=> fun i:V=> code m k (F i)
local notation "Z'"=> Fin.append (Z₁) (fun i=>Bid.visits C (p₀ i).1 (p₀ i).2)
include Y hf hG
lemma entry_test (_ht:(∑ i:V,s i)+ ∑ i:U,(p₀ i).1≤ k): Tendsto (fun u:Cutoffs=> certificate (Fin.append (fun i=>code m k (F i)) (fun i=> Bid.visits C (p₀ i).1 (p₀ i).2)) F' u-jointS F' s F p₀ m u.1 u.2) f.fuse (𝓝 0):=by
   have hh:(∑ i:V,s i)≤k:=by omega
   obtain ⟨M,hM,hQ⟩:= branched F' (k+1); obtain ⟨B',hB,hV⟩:= spanStays F'; obtain ⟨b,hb,hq,hP⟩:= all_envelopes (m:=m) h s F hG hf (κ+1) hh (by omega) M B' hM
   choose c hc hC hz using fun i:U=> stays (RawProtected.visits (f:=f) h hG (show C.label (p₀ i).1 from (p₀ i).2) le_rfl)
   have hK(i:V): ∀ N p:ℕ,∀ z,Continuous (code m k (F i) N p z):=((bids h (F i) Y hG (le_refl _) (by simpa only [Nat.sub_self,pow_zero,inv_one,one_smul] using hf i)).1).root
   let a (j:Cutoffs):= (Extraction.length C.S j.2)^(4*n); have hJ:Slow C f a:=by intro ε h'; rw [Order.fused,Order.late]; refine Eventually.of_forall fun t=> ?_; unfold a; exact (show Tendsto (fun N=> Real.exp (ε*C.S.scale (f.mesh N))) atTop atTop from Real.tendsto_exp_atTop.comp ((C.S.divergent.comp f.mesh.cofinal).const_mul_atTop h')).eventually_ge_atTop ‖a (0,f.per t)‖
   let w(t):= ∏ i:U,c i t; have hx:= (hJ.mul (hq.mul (productC hC Finset.univ))).sink (show (1/2:ℝ)< 1 from by norm_num)
   refine tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall fun i=> norm_nonneg _) ?_ (flight_lands (C:=C) (f:=f) (ε:=1/2) (by positivity))); filter_upwards [hx,hP,eventually_all.mpr hz] with i hv hPx hZ; rcases i with ⟨n',p'⟩
   let N:=n';let p:=p'; let b':= b (N,p); let t:= C.S.a N; let a':= a (N,p); let w':= w (N,p); let u:=fun (i: Fin n→Site (C.side N p))=> sees (C:=C) (p:=p) (N:=N) F' i
   let R':=fun i:V=> F i (N,p); let x:=(fun i:V=> code m k (F i));
   change ‖certificate _ _ (n',p')-jointS F' s F p₀ m n' p'‖≤ _; rw [witness_column F' p₀ _ (fun i z=>hK i n' p' z)]; unfold jointS; rw [← mul_sub,← Finset.sum_sub_distrib]; let P':=p₀
   refine le_trans ((Work.D03.period_cost C.S _ (t*(b'*w')) ?_)) ((le_of_eq ?_).trans hv); swap
   · change a' * _= _* Push.RelayDifference.flight _ _ _; unfold Push.RelayDifference.flight Schedule.scale; dsimp only; rw [Real.log_inv,neg_one_mul,neg_neg,Real.exp_log (C.S.a_pos n')]; change a' * (t*(b'*w')) = a'*(b'*w')*t;ring
   intro i; let y:= u i; let g':= multi C m N p s R' y; let Y':= sheet y C x N p; let e':= spect p₀ i; have hy': Continuous e':=continuous_finsetProd _ fun _ _=> C.continuousO ..
   change ‖(∫ z,Y' z*e' z∂law G _ (C.beta _ _))-(∫ z,g' z*e' z∂law G _ (C.beta _ _))‖≤_
   let μ:= law G (C.side N p) (C.beta N p); have hZi:Integrable (fun z=> Y' z*e' z) μ:=continuous_integrable _ ((touch_sheet x (fun i z=>hK i N p z) y).mul hy'); have hG':Integrable (fun z=>g' z*e' z) μ:= continuous_integrable _ ((touchS s F y (m:=m) (p:=p) (N:=N)).mul hy'); change ‖(∫ z,Y' z*e' z∂μ)-(∫ z,g' z*e' z∂μ)‖≤_; rw [← integral_sub hZi hG']; refine (norm_integral_le_of_norm_le_const (μ:=law G (C.side N p) (C.beta N p)) (C:=t*(b'*w')) (Eventually.of_forall (fun z=>?_))).trans_eq (by simp) -- C binder?
   have he(z:Config G (C.side N p)): ‖e' z‖≤ w'* (t^κ)⁻¹:=by
       unfold e' spect; rw [norm_prod]; refine (Finset.prod_le_prod (fun _ _=> norm_nonneg _) (fun i _=> hZ i _ _)).trans_eq ?_; rw [Finset.prod_mul_distrib,Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum]
   let T:= t^κ; have hz:= C.S.a_pos N; have hf':‖Y' z-g' z‖≤ t^(κ+1)*b':= hPx y (hQ _) (hV _) z
   rw [← sub_mul]; exact (norm_mul_le ..).trans ((mul_le_mul hf' (he z) (norm_nonneg _) (by have h₀:0≤ b':=(hb _); have hx:0 < t:= hz; positivity)).trans_eq (by rw [pow_succ]; have hz:0<t:=hz;field_simp))
end YM.RG05Readout.Chalice
