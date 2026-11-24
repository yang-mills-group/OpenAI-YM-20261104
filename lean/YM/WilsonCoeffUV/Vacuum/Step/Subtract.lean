import YM.WilsonCoeffUV.Vacuum.Step.Closure
/-! Subtract moment reads. First argument reference uses DIFFERENCE only
from coefficients multiplying lower-order input. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Next.Free PowerSeries
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{σ A B D E δ:ℝ}{i j k r:ℕ}
def retent (Z:Ten ℝ (YForest G) 2){r:ℕ}(P: Ten ℝ (YForest G) r): Ten ℝ (YForest G) r := if h:r=2 then P-(h.symm ▸ (readSun (h ▸ P) • Z)) else P
lemma retent_front (Z P:Ten ℝ (YForest G) 2): retent Z P=P-readSun P • Z:= dif_pos rfl
lemma retent_next {r:ℕ}(h:r ≠ 2)(Z: Ten ℝ (YForest G) 2)(P: Ten ℝ (YForest G) r): retent Z P=P:= dif_neg h
lemma retent_zero (Z:Ten ℝ (YForest G) 2) : retent Z (0: Ten ℝ (YForest G) r)=0:= by by_cases h:r=2 <;> first | exact retent_next h .. | subst r; simp [retent_front,sun_zero]
lemma retent_add (Z:Ten ℝ (YForest G) 2){P Q:Ten ℝ (YForest G) r}(h:Amber terrain σ A P)(hp: Amber terrain σ B Q)(he:0<σ) : retent Z (P+Q)=retent Z P+retent Z Q:=by
    by_cases H:r=2
    · subst r; simp only [retent_front,sun_add h hp he he,add_smul,add_sub_add_comm]
    rw [retent_next H,retent_next H,retent_next H]
lemma retent_any {P Q: Ten ℝ (YForest G) r}(Z: Ten ℝ (YForest G) 2) (h:r=2 → ∃ σ A,0<σ ∧ Amber terrain σ A P ∧ Amber terrain σ A Q): retent Z (P+Q)= retent Z P+retent Z Q:= by
    by_cases H:r=2; · obtain ⟨s,a,hp,hq,hv⟩:= h H; exact retent_add Z hq hv hp
    rw [retent_next H,retent_next H,retent_next H]
lemma tenant (Z:Ten ℝ (YForest G) 2){P: Ten ℝ (YForest G) r}(c:ℝ): retent Z (c•P)=c•retent Z P:= by
   unfold retent; split <;> rename_i h
   · subst r; simp_rw [sun_μ,smul_sub,smul_smul]
   rfl
lemma retent_sub (Z:Ten ℝ (YForest G) 2){P Q:Ten ℝ (YForest G) r}(h:Amber terrain σ A P)(hp: Amber terrain σ B Q)(he:0<σ): retent Z (P-Q)=retent Z P-retent Z Q:=by
   rw [sub_eq_add_neg,retent_add Z h hp.neg he]; simpa only [neg_one_smul,sub_eq_add_neg] using congr_arg (retent Z P+·) (tenant Z (P:=Q) (-1))
lemma retent_sum (Z:Ten ℝ (YForest G) 2){r:ℕ}{ι:Type*}{s:Finset ι}{f:ι→Ten ℝ (YForest G) r}(e:∀ i,r=2→∃ σ A,0<σ ∧ Amber terrain σ A (f i)): retent Z (∑ i∈s,f i)=∑ i∈s,retent Z (f i):=by
   by_cases H:r=2; swap; · simp_rw [retent_next H]
   subst r; obtain ⟨v,a,hp,hb⟩:= bundle_cap (P:=f) (fun i=> e i rfl) s; rw [retent_front, fuel_sum s hp (A:=fun _=>a) hb, Finset.sum_smul]; simp_rw [retent_front, Finset.sum_sub_distrib]

def ruby (σ A : ℝ):ℝ:= 1+ceilPoly 2 (σ/2)*sheetPay (σ/2)*A
lemma ruby_nn (h:0<σ)(p:0≤A): 1≤ruby σ A:=le_add_of_nonneg_right (mul_nonneg (mul_nonneg (ceilPoly_pos ..).le (sheetPay_pos _ (by positivity)).le) p)
lemma apt (h:0<σ){Z:Ten ℝ (YForest G) 2}(he:Amber terrain σ B Z){P:Ten ℝ (YForest G) r}(p: Amber terrain σ A P): Amber terrain σ (A*ruby σ B) (retent Z P):=by
    by_cases t:r=2
    · subst r; rw [retent_front]; apply (p.sub (he.smul _)).le; refine (add_le_add_right (mul_le_mul_of_nonneg_right (sun_cost p h) he.1) A).trans_eq ?_
      unfold ruby; ring
    rw [retent_next t]; exact p.le (le_mul_of_one_le_right p.1 (ruby_nn h he.1))
lemma app_gap (h:0<σ){Z W:Ten ℝ (YForest G) 2}(he: Amber terrain σ D (Z-W)){P: Ten ℝ (YForest G) r}(p:Amber terrain σ B P): Amber terrain σ (B*(ceilPoly 2 (σ/2)*sheetPay (σ/2))*D) (retent W P-retent Z P):=by
   by_cases ht:r=2
   · subst r; rw [retent_front,retent_front,sub_sub_sub_cancel_left,← smul_sub]; exact (he.smul _).le (mul_le_mul_of_nonneg_right (sun_cost p h) he.1)
   rw [retent_next ht,retent_next ht,sub_self]; exact Amber.zero.le (mul_nonneg (mul_nonneg p.1 (mul_nonneg (ceilPoly_pos ..).le (sheetPay_pos _ (by positivity)).le)) he.1)
lemma PairA.retent {Z W:Ten ℝ (YForest G) 2}(he:PairA σ B δ Z W){P Q: Ten ℝ (YForest G) r}(p:PairA σ A δ P Q)(h:0<σ)(e:0≤δ): PairA σ (2*A*ruby σ B) δ (retent Z P) (retent W Q):=by
    have ha:= p.nn; have hb:=he.nn
    have hz : A*ruby σ B≤2*A*ruby σ B:= mul_le_mul_of_nonneg_right (by linarith) (zero_le_one.trans (ruby_nn h hb))
    refine ⟨(apt h he.pose p.pose).le hz,(apt h he.vale p.vale).le hz,?_⟩
    rw [show Bank.retent Z P-Bank.retent W Q=Bank.retent Z (P-Q)+(Bank.retent Z Q-Bank.retent W Q) from ?_]; swap; · rw [retent_sub Z p.pose p.vale h]; abel
    have hv:= (app_gap h he.visit p.vale).neg; rw [neg_sub] at hv; apply ((apt h he.pose p.visit).add hv).le; unfold ruby; linarith only [mul_nonneg ha e]

lemma Satin.closure {P Q:(i:Gear G)→ Rally k r i→ Ten ℝ (YForest G) j}(h:Satin (largus k r) (smallus k r) Gear.σ P Q): Satin (largus k r) (smallus k r) Gear.σ (fun i x=> retent (orbQ x.P.Z) (P i x)) (fun i x=> retent (orbQ x.Q.Z) (Q i x)):=by
    obtain ⟨d,H⟩:=h; refine ⟨d,fun I=>?_⟩; obtain ⟨A,h,e⟩:=H I
    refine ⟨2*A*ruby I.σ I.D,mul_nonneg (by positivity) (zero_le_one.trans (ruby_nn I.price (zero_le_one.trans I.bill_nn))),fun i=>?_⟩
    have he : PairA I.σ I.D i.σ (orbQ i.P.Z) (orbQ i.Q.Z) := by simpa only [flatPal,↓reduceIte,shine_lit] using kernel_pair (i.Ω.mono I.holds.le) 0 2
    have hx:= PairA.retent he (e i) I.price i.θ; convert! hx using 1; ring

-- numeric reset modifies only strict predecessors after reference projection
namespace Stand
variable {I:Gear G}(P:Stand I)
def chime (e r j:ℕ): ℝ:= coeff (e-j) (P.moving^j*(P.moving⁻¹)^r)
def corr (e r:ℕ) : Ten ℝ (YForest G) r:= ∑ i∈(Finset.range e).erase 0, P.chime e r i • retent (orbQ P.Z) (P.driftU i r)
lemma status (P:Stand I){e}(h:e≠0)(r) : retent (orbQ P.Z) (P.stake e r)=P.stake e r:= by
   by_cases he:r=2; swap; · exact retent_next he ..
   subst r; rw [retent_front,←stellar_read,P.starlit]; simp [h]
lemma stillStart (P:Stand I)(r): retent (orbQ P.Z) (P.driftU 0 (r+2))=0 := by
   rw [show P.driftU 0 = _ from P.lead]; by_cases h:r=0
   · subst r; simp only [shine_lit,retent_front,P.mint,one_smul,sub_self]
   rw [shine_dark (by omega),retent_zero]
lemma component (h:k≠0): P.stake k (r+2)=retent (orbQ P.Z) (P.driftU k (r+2))+P.corr k (r+2):=by
   set j:= r+2
   let Q i:= P.chime k j i; have hz : Q k=1:=by unfold Q chime; simp [show constantCoeff P.moving=1 from back_cc P.sunshine]
   have he : P.stake k j= ∑ i∈ Finset.range (k+1), Q i • P.driftU i j:=by unfold stake Blue.mix; apply Finset.sum_congr rfl; intro i hi; unfold lop; rw [if_neg (show j≠0 by unfold j; omega)]; rfl
   have hp i (h:j=2): ∃ σ A,0<σ ∧ Amber terrain σ A (Q i • P.driftU i j):=by
      obtain ⟨s,a,hp,hq⟩:=P.ez i; generalize hm : Q i = b; rw [h]
      exact ⟨_,_,hp,hq.smul _⟩
   rw [← status P h j,he,retent_sum (orbQ P.Z) hp,Finset.sum_range_succ,← Finset.add_sum_erase _ _ (show 0∈Finset.range k from Finset.mem_range.mpr (Nat.pos_of_ne_zero h)),hz,one_smul]; simp_rw [tenant]; rw [stillStart,smul_zero,zero_add,add_comm]; rfl
end Stand
end YM.WilsonCoeffUV.Bank
