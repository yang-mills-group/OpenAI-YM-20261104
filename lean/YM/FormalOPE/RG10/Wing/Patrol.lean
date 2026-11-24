import YM.FormalOPE.RG10.Wing.Submarine
/-! # Rooted gauge change costs from vector field, any Tier. No moment mismatch kth transport.
 Price exponential polynomial reserve IN ADVANCE. Significant reduction: no multiplicity from
 cluster propagating L^4. Ward equations completely prior to this. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Wing.Patrol
open Function PowerSeries Finset Route Cycle HStein Submarine Tier
open scoped Topology BigOperators Classical
variable {X : Type} [Fintype X]
variable {k t i :ℕ} (u:X→Channel X) (F:Tier) (w:X→ℝ)
local notation "K"=>Packet X
local notation "W"=>Channel X
local notation "D"=>kick u
omit [Fintype X] in
lemma premiered (p q:Channel X) (h:0≤w): F.gain w (p+q) k ≤ F.gain w p k+F.gain w q k:= mag_add _ _ _ (F.dep_sign w h) _ _
omit [Fintype X] in
lemma photos (m:Letters X)(h:0≤w): F.gain w (PowerSeries.C (glyph m)) k = F.face w m:= by rw [gain_constant,glyph,money F w h,norm_one,mul_one]
omit [Fintype X] in
lemma recital (i:X)(h:0≤w): F.gain w (HStein.sprout i) k = F.value (w i) := (photos F w (k:=k) _ h).trans (Tier.level ..)

local notation "l"=> Primitives.GCC.LocalPolynomial.length
variable {u F} {M:ℝ}
variable (h:0≤w) (hv: Targeted F w w u k M) (he: Targeted Tier.free w w u k M) (hz: 0 ≤ M)
include he h hz
private lemma pay (m:Letters X): Tier.free.gain w (D (C (glyph m))) k ≤ (4:ℝ)^l m * M := by
 obtain hx|hx:= eq_empty_or_nonempty m.support
 · rw [Finsupp.support_eq_empty.mp hx,show glyph (0:Letters X)=1 from rfl,map_one,Derivation.map_one_eq_zero]; unfold gain; rw [mag_empty]; positivity
 obtain ⟨a,ha⟩:= hx
 let z:=m-Finsupp.single a 1; have hp : m=z+Finsupp.single a 1:= (Finsupp.sub_add_single_one_cancel (Finsupp.mem_support_iff.mp ha)).symm; have hm' : l m=l z+1:= Eq.symm (distill ha)
 have hh : Tier.free.gain w (u a) k ≤ M:= by simpa using he a
 nth_rw 1 [hp]; rw [← comma,_root_.map_mul,call, show C (MvPolynomial.X a)= HStein.sprout a from rfl, Derivation.leibniz,sprouting]; simp only [smul_eq_mul]
 apply (premiered Tier.free w _ _ h).trans; have hy := pay z;
 apply (add_le_add (gain_mul Tier.free w h _ _) (gain_mul Tier.free w h _ _)).trans; rw [photos Tier.free w z h, Tier.flat,one_mul,recital Tier.free w a h,Tier.free_stamp,one_mul]; apply (add_le_add hh hy).trans; rw [hm', pow_succ];
 nlinarith [one_le_pow₀ (show (1:ℝ) ≤ 4 by norm_num) (n:=l z)] -- argument?
termination_by l m
decreasing_by have hx:=distill ha; omega
include hv
lemma light (m:Letters X): F.gain w (D (C (glyph m))) k ≤ ((4:ℝ)^l m * M)*F.face w m:= by
 obtain hx|hx:= eq_empty_or_nonempty m.support
 · rw [Finsupp.support_eq_empty.mp hx,show glyph (0:Letters X)=1 from rfl,map_one,Derivation.map_one_eq_zero,Tier.silent]; unfold gain; rw [mag_empty]; positivity
 obtain ⟨a,ha⟩:= hx
 let z:=m-Finsupp.single a 1; have hp : m=z+Finsupp.single a 1:= (Finsupp.sub_add_single_one_cancel (Finsupp.mem_support_iff.mp ha)).symm; have hm' : l m=l z+1:= Eq.symm (distill ha); have hj:=F.grade (h a); have hU := F.ready w h m; have hB:= F.bright w h z
 have h0:=zero_le_one.trans hj; have hU':=zero_le_one.trans hU
 have hh : Tier.free.gain w (u a) k ≤ M:= by simpa using he a
 let B₁:=(4:ℝ)^l z*M; have hB1:M≤B₁:= le_mul_of_one_le_left hz (one_le_pow₀ (by norm_num)); have ho:=hz.trans hB1
 have h' := light z; have hu:=pay w h he hz z
 have hui:= F.degree w h m a ha; have hl : F.face w z≤F.face w m:= F.grows w h z m (tsub_le_self)
 nth_rw 1 [hp]; rw [← comma,_root_.map_mul,call, show C (MvPolynomial.X a)= HStein.sprout a from rfl, Derivation.leibniz,sprouting]; simp only [smul_eq_mul]
 apply (premiered F w _ _ h).trans; apply (add_le_add (F.twice_all w h _ _) (F.twice_all w h _ _)).trans
 rw [photos Tier.free w z h, photos F w z h, Tier.flat,one_mul,recital Tier.free w a h,recital F w a h,Tier.free_stamp,one_mul]
 apply (add_le_add (add_le_add (hv a) (mul_le_mul_of_nonneg_left hh hB)) (add_le_add h' (mul_le_mul_of_nonneg_left hu h0))).trans; rw [hm',pow_succ]; unfold B₁ at *
 set C₁:= F.face w m; set K':= F.face w z; set B:=(4:ℝ)^l z; set H:= F.value (w a)
 nlinarith -- might fail
termination_by l m
decreasing_by have hy:=distill ha; omega
-- charge kick iterates from all rows. keep moment F
lemma sails (d:ℕ) (p:Packet X) (hp:p.totalDegree ≤ d) : F.gain w (D (C p)) k ≤ ((4:ℝ)^d*M)* F.valueOf w p:= by
 nth_rw 1 [resolves p]; rw [map_sum,map_sum]; apply (F.sumUp w h _ _).trans; rw [F.capital _ h, mul_sum]; apply sum_le_sum; intro i hi
 have H (c:ℂ)(p:Packet X): PowerSeries.C (c • p)=c • C p:= by apply PowerSeries.ext; intro i; cases i <;> simp
 rw [H, Derivation.map_smul,coin_steady]
 have ht:=pow_le_pow_right₀ (show (1:ℝ)≤4 by norm_num) ((show l i ≤ p.totalDegree from MvPolynomial.le_totalDegree hi).trans hp)
 exact (mul_le_mul_of_nonneg_left ((light w h hv he hz i).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ht hz) (F.bright w h _))) (norm_nonneg _)).trans (by apply le_of_eq; ring)
omit hv he h hz
end YM.FormalOPE.RG10.Wing.Patrol
