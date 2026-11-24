import YM.FormalBulk08.Hay.Sums

/-! Low ports in canonical slot notation. Each condition uses exactly the
appropriate projecting rank (loop at coupling grade two). -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Hay
open Filter Set Function MeasureTheory Lattice RG Exterior Wilson Precision Tree Work.F05
open Stationary hiding shine Rays
open Reef Series Wick Jets Orb Plait PowerSeries Lava Mesa Broc City Cork Lotus Shore Gorge Laurent Bloch Flat Next.Free
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius Matrix
variable {G:Gauge}{c f n:Side}{S:StepData c f}{p q:Clip}{R U:PathData G}{σ α γ Γ Λ B C:ℝ}{e j:ℕ}
-- Capacities, no activation presup
lemma stock_lane (e:ℕ) (n:Side) : MvPolynomial.homogeneousComponent (e+2) (coeff e (novel p R n))= -coeff (e+2) (paste (intended p R)) := by
    rw [novel,map_sub,map_neg,after_one,add_comm 2,map_sub,map_neg, MvPolynomial.homogeneousComponent_eq_self (paste_grade ..), MvPolynomial.homogeneousComponent_of_mem (paste_grade ..),if_neg (by omega),sub_zero]
lemma stock_rim (e:ℕ)(n:Side): MvPolynomial.homogeneousComponent e (coeff e (novel p R n))= -coeff e (paste (turnSeries R.loop)) := by
    rw [novel,map_sub,map_neg,after_one,map_sub,map_neg, MvPolynomial.homogeneousComponent_of_mem (paste_grade ..),if_neg (by omega), MvPolynomial.homogeneousComponent_eq_self (paste_grade ..), neg_zero,zero_sub]
lemma colA (h: U.Bounds q σ B C)(r) (e:r<3)(n:Side): coeff r (paste (inputSeries q U (m:=n)))= coeff r (paste (intended q U (m:=n))) := by
    have hu:= (stain_knit U q h (m:=n)).analytic; have ht := turns_analytic U.cubic h.width h.three (m:=n)
    rw [Stationary.intent,paste_sum _ _ (hu.add ht).contDiffAt (turns_analytic U.quartic h.width h.four).contDiffAt, paste_sum _ _ hu.contDiffAt ht.contDiffAt,map_add,map_add,Broc.uncut_moans _ ⟨h.three,fun i=> (h.invariant i).2.1⟩ h.width r e, Broc.uncut_moans _ ⟨h.four,fun i=> (h.invariant i).2.2⟩ h.width r (by omega),add_zero,add_zero]
lemma draft_read (h: U.Bounds q σ B C)(α:ℝ)(n:Side): coeff 2 (paste (draft α U q ∘ Stationary.arm G n 1))= α • coeff 2 (paste (intended q U))+ coeff 2 (paste (turnSeries U.loop (m:=n))):= by
    let f: Link G n→ℝ:=inputSeries q U; let V:=turnSeries U.loop (m:=n); let g: Link G n→ℝ:=fun _=>α; have hf : ContDiffAt ℝ ∞ f 0:=(stain_knit U q h).analytic.contDiffAt
    have he:draft α U q ∘ Stationary.arm G n 1= (g * f)+V:= rfl
    rw [he,paste_sum _ _ (show ContDiffAt ℝ ∞ (g*f) 0 from contDiffAt_const.mul hf) (turns_analytic U.loop h.width h.two).contDiffAt,map_add,paste_mul g f contDiffAt_const hf,paste_flat, coeff_C_mul]; rw [show coeff 2 (paste f)=_ from colA h 2 (by norm_num) n]; congr 1; exact (MvPolynomial.smul_eq_C_mul ..).symm
lemma stock_cum {V: Pot G}(h:Troupe V q U)(n:Side): marble (e+2) (coeff e (novel q U n))=cum 0 n (V e (e+2)) := by
    rw [←h.buys]; exact h.flower ..
lemma head_lane (F: Forest S.ratio)(Y:Bid.Dir G c→AxisChart G F)(x:S.Choices)(h:ClassicalMatch F p q R U Y)(hp:e≤2){Q : Pap (wire G c)} (he:MvPolynomial.homogeneousComponent (e+2) (coeff e Q) = -coeff (e+2) (paste (victory F x p R Y))){V: Pot G}(H:Troupe V q U) : marble (e+2) (coeff e Q)=cum 0 c (V e (e+2)):= by
   rw [←stock_cum H c]; apply facade_unique (marble_agate _ _) (marble_agate _ _); rw [marble_grade,marble_grade,he,stock_lane]; have hx:= cardBeam c _ _ (h (e+2) (by omega) x); exact congr_arg (-·) (show coeff (e+2) (paste (victory F x p R Y))=_ from hx)
lemma body_lane (F: Forest S.ratio)(Y:Bid.Dir G c→AxisChart G F)(x:S.Choices) (A:ChartRatio G)(h:FiniteBound F R U p q α A Y Γ γ Λ)(hx:U.Bounds q σ B C){Q:Pap (wire G c)} (he:MvPolynomial.homogeneousComponent 2 (coeff 2 Q) = -coeff 2 (paste (Precision.thermal F x p R Y A ∘ Stationary.arm G c 1))) {V:Pot G}(ht:Troupe V q U)(v:chain (Lines G c 1) 2):
    |marble 2 (coeff 2 Q) v-cum 0 c (V 2 2+α • V 0 2) v| ≤ 1/2*(skyL G c*((Fintype.card (Site c):ℝ)*Γ*Λ*Real.exp (-γ*c.val))) := by
   let g:= Precision.thermal F x p R Y A; let d:= draft α U q (c:=c); let W:= Stationary.arm G c 1
   have hg: AnalyticAt ℝ g 0:= (h.born x).analyticAt
   have hd: AnalyticAt ℝ d 0:=h.classicalResult.analyticAt
   have hT (f: Bid.Dir G c→ℝ)(h:AnalyticAt ℝ f 0): Agate (-Broc.beam (f ∘ W) 2) := by rw [←neg_one_smul ℝ]; exact (beam_pulse _ (AnalyticAt.comp ((map_zero W).symm ▸ h) (W.analyticAt _)) _).smul _
   have H : marble 2 (coeff 2 Q)= -Broc.beam (g ∘ W) 2 := facade_unique (marble_agate _ _) (hT g hg) (by rw [marble_grade,he,map_neg,beam_price])
   obtain ⟨s,B,hs,Hb⟩:= ht.fare 0 2; obtain ⟨s',D,Hs,Hy⟩:=ht.fare 2 2
   rw [H,cum_plus 0 c Hs.le hs.le Hy (Hb.smul _), cum_smul]; have hv:cum 0 c (V 2 2)+α • cum 0 c (V 0 2) = -Broc.beam (d ∘ W) 2:= by
       have hl(k): marble 2 (coeff k (novel q U c))=cum 0 c (V k 2):= by rw [←ht.buys]; exact ht.flower k 2 0 c
       rw [← hl,←hl]; apply facade_unique (Agate.add (marble_agate _ _) ((marble_agate _ _).smul _)) (hT d hd); rw [map_add,map_smul,map_neg,marble_grade,marble_grade,stock_lane 0 c, stock_rim, beam_price, show coeff 2 (paste (d ∘ W))=_ from draft_read hx α c]; rw [smul_neg]; abel
   rw [hv, Pi.neg_apply,Pi.neg_apply,neg_sub_neg,abs_sub_comm]; exact sky_cost g d hg hd (fun i j a b p q=> by have ht:= h.wave_price x i j a b p q; convert ht using 1) v
end YM.FormalBulk08.Hay
