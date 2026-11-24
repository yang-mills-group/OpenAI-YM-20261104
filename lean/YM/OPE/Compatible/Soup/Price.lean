import YM.OPE.Compatible.Soup.Yen
/-!
# Sparse absolute costs. b+2 supports post.Trajectory.Preservation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Merchant.Aloof
set_option maxHeartbeats 200000
open Function Filter MeasureTheory Lattice Laurent Wilson Matrix RG Gauge Set
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ENNReal
open Eyrie Push.Mark Cascade Pilot PhysicalNext.Repeat.Aroma Finset PathData
variable {G:Gauge}{b i j k r:ℕ}{n:Side}
local notation "F!"=>Config G n
variable (U:Config G n)(h:Toss U b) {p:BudgetPoint}{C:Clip} {c s a t ε d:ℝ} {R:PathData G} {A:Activities G n}
include h
lemma extraE (hc:A.Valid p a t)(hb:0<ε)(hp:ε ≤ p.supportExponent): ‖A.additive p U‖ ≤ (↑(((b+b+1)^4):ℕ):ℝ)*(est p ε * a):=by
       obtain ⟨z,hz,H⟩:=hc.boundE; let f(i:ℕ):=A.regularOccurrence p i U
       let v(x:Site n) (i:ℕ):= if x∈ (A.reg i).support then z i else 0; have he:= perceive (u:=A.reg) hb (show 0+ε ≤ p.supportExponent from by simpa using hp) (fun i=>(hz i).1) H; have hh(x:Site n):SumBudget (v x) (est p ε*a):=(by simpa only [v,zero_mul,Real.exp_zero,mul_one] using he x)
       have hf := Activities.ESeries hc|>.absolute U; apply (norm_tsum_le_tsum_norm hf).trans; let S:= berth (n:=n) b; apply le_trans (b:=∑' i,∑ j∈S,v j i) _ _; swap
       · rw [Summable.tsum_finsetSum ?_]; exact (sum_le_sum (fun i _=>(hh i).2.2)).trans (by rw[sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (cardinal_B n)) ((tsum_nonneg (hh 0).1).trans (hh 0).2.2)); exact fun i _=>(hh i).2.1
       refine hf.tsum_le_tsum (fun i=> ?_) (summable_sum fun i _=>(hh i).2.1); change ‖f i‖≤_
       by_cases Z: f i=0; · rw[Z,norm_zero]; exact sum_nonneg fun j _=>(hh j).1 i
       have hY: Healthy p.threshold (A.reg i).support U:=of_not_not (fun h=> Z (masked_ne _ _ _ _ h)); have hq: f i=A.E i U:= masked_eq _ _ _ _ hY
       have hB: ¬ Disjoint (A.reg i).support S:=fun H=> Z (hq.trans (((hc.regular.smooth i).sites _ _ (h.card _ H)).trans (hc.regular.at_flat i)))
       obtain ⟨x,hx,hW⟩:=Finset.not_disjoint_iff.mp hB; rw [hq]; exact ((hz i).2 U hY [] (by simp) (by simp)).trans ((show z i=v x i from (if_pos hx).symm).trans_le (Finset.single_le_sum (f:=fun j=>v j i) (fun j _=>(hh j).1 i) hW))
lemma atom_sparse (p:BudgetPoint) (x:ℕ→Atom G k) (hz:SumBudget (fun i=> (x i).budget s) a)(hk:0<k)(hs:0<s): ∑ i:Site n, ‖atomSeries x p U i‖ ≤ Shoal b*a*p.threshold^k:=by
        let F(i:ℕ)(j:Site n):= (x i).placed p U j; let t:=p.threshold; let c(i):= (x i).budget s
        have hh(i:ℕ)(a':Site n): ‖F i a'‖≤ c i*t^k:= (healthy_atom (x i) ..).trans (mul_le_mul_of_nonneg_right (Atom.lower_budget (x i) _ hs) (pow_nonneg p.threshold_pos.le _))
        let B:= Shoal b; have hZ: 0 ≤ B:=zero_le_one.trans (Shoal.one b); let j:Fin k:=⟨0,hk⟩
        have hu(i): ∑ x:Site n, ‖F i x‖ ≤ B*(c i*t^k):=by
             apply shore (wrap n ((x i).leg j).offset) _ (c i*t^k) (hh i); intro y hy; refine h.seeds (x i) y j ?_; by_cases P: Healthy t ((x i).footprint y) U; · exact ((show F i y= _ from (show F i y=(x i).unmasked U y from masked_eq _ _ _ _ P)) ▸ hy)
             exact False.elim (hy (masked_ne _ _ _ _ P))
        have he(i:Site n):Summable (fun j=> ‖F j i‖):= (atom_dominated _ _ _ hs hz).absolute U; calc
             _ ≤ ∑ i:Site n, ∑' j, ‖F j i‖:= sum_le_sum fun i _=>norm_tsum_le_tsum_norm (he i)
             _ = ∑' j,∑ i:Site n, ‖F j i‖:= (Summable.tsum_finsetSum (fun i _=>he i)).symm
             _ ≤ ∑' j, B*(c j*t^k):= Summable.tsum_le_tsum hu (summable_sum (fun i _=>he i)) ((hz.2.1.mul_right _).mul_left _)
             _ ≤ B*a*t^k:=by rw[tsum_mul_left,tsum_mul_right,mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hz.2.2 (pow_nonneg p.threshold_pos.le _)) hZ
lemma price_loop (p:BudgetPoint)(X:R.Bounds C s a t)(hb:0 ≤ c):
       ‖R.principal C p c U-c*∑ x,R.baseTerm C p U x‖ ≤ Shoal b*PathData.loopsPrice p c a t:=by
       unfold PathData.principal; rw[mul_add,add_assoc,add_sub_cancel_left]; apply (norm_add_le ..).trans; rw[norm_mul,Real.norm_of_nonneg hb]; let B:= Shoal b; let z:=p.threshold
       apply le_trans (b:=c*(B*a*z^3+B*a*z^4)+B*t*z^2) _ (by unfold PathData.loopsPrice; exact le_of_eq (by unfold B z; ring)); apply add_le_add _ ((norm_sum_le ..).trans (atom_sparse U h _ _ X.two two_pos X.width)); apply mul_le_mul_of_nonneg_left _ hb; apply (norm_sum_le ..).trans; refine le_trans (c:=B*a*z^3+B*a*z^4) (sum_le_sum fun i _=>norm_add_le _ _) ?_; rw [sum_add_distrib]; exact add_le_add (atom_sparse U h _ _ X.three (by decide) X.width) (atom_sparse U h _ _ X.four (by decide) X.width)
omit h
lemma clippedB (C:Clip)(p:BudgetPoint):  ∀ t:ℝ,0≤t→t ≤ p.threshold →∀ z:ℝ,t≤z→ C.linear*t^2/2 ≤ clipped C p.threshold z:=by
       intro t ht hT z hz; unfold clipped; have hs:=C.tail_pos; have hv:=C.quadratic_pos; have hp:=C.kink
       have he:C.linear*t^2 ≤ C.linear*z^2:=mul_le_mul_of_nonneg_left (by gcongr) hs.le; split_ifs; · gcongr;linarith
       have hh:C.linear*t^2/2 ≤ C.linear*t^2:=(by have h:=mul_nonneg hs.le (sq_nonneg t); linarith); apply hh.trans; rw[sq,mul_assoc];gcongr; exact p.threshold_pos.le
-- absolute negative action all sparse cases. invariant channels catch large face in raw basis
noncomputable abbrev τRG (C:Clip):ℝ:= C.linear/(↑(Fintype.card Signed)*2)
lemma τRGP :0 < τRG C:=by unfold τRG; exact div_pos C.tail_pos (by positivity)
include h
lemma chop (X:R.Bounds C s a t)(hb:0 ≤ c) (hd: 0 ≤ d) (hp:d ≤ p.threshold)(F: Face (Per n))(hF:d ≤ G.chord (faceValue U F)):
       τRG C * c * d^2 - Shoal b * PathData.loopsPrice p c a t ≤ R.inChannels C p c U:=by
       let q:=Shoal b*PathData.loopsPrice p c a t; let P(z: Signed):= pull z 0 U; let g(z):= ∑ x,R.baseTerm C p (P z) x; let v(z):= R.principal C p c (P z)
       have he(z:Signed) : c*g z-q ≤ v z:=by have ht:= (abs_le.mp (price_loop (P z) (h.turn z) p X hb)).1; change -q≤v z-c*g z at ht; linarith only [ht]
       let w:ℝ:= Fintype.card Signed; have hw:0<w:= by unfold w; positivity
       have hz:R.baseTerm C p U F ≤ g 1:=by unfold g P; rw[pull_id]; exact single_le_sum (fun i _=> R.base_nonneg C p U i) (mem_univ _)
       have hP:C.linear*d^2/2 ≤ g 1:= (clippedB C p d hd hp _ hF).trans (le_trans ?_ hz); swap
       · unfold baseTerm; refine le_add_of_nonneg_right ?_; split <;> positivity
       have hG: g 1 ≤ ∑ i,g i:=single_le_sum (f:=g) (fun i _=>sum_nonneg (fun j _=> R.base_nonneg C p (P i) j)) (mem_univ _)
       calc
           _ = w⁻¹*(c*(C.linear*d^2/2)-w*q):= by unfold τRG; field_simp; unfold w q; ring
           _ ≤ w⁻¹* ∑ i:Signed,(c*g i-q):=mul_le_mul_of_nonneg_left (by rw[sum_sub_distrib,sum_const,card_univ,nsmul_eq_mul,←mul_sum]; exact sub_le_sub_right (mul_le_mul_of_nonneg_left (hP.trans hG) hb) _) (inv_nonneg.mpr hw.le)
           _ ≤ _:=mul_le_mul_of_nonneg_left (sum_le_sum fun i _=>he i) (inv_nonneg.mpr hw.le)
end YM.OPE.Merchant.Aloof
