import YM.WilsonCoeffUV.Marked.Capture.LogCost
/-!
# CAPTURE on q-open interval

Validated profiles in k-units, center at 0 when integrated, halo `k≤λ_b` and
age-on-z hull. Engineering and test costs explicit esp `Φ`; ε requires
consumer Λ/g input to use this subpower expansion. Unmasked bulk ESTIMATE.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.WilsonCoeffUV.Wheel.Flooring
open Wheel.Mark Function PowerSeries Blue Mer Lattice RG Embroider Embroider.Canvas Soil Bank Laurent Cosmos Filter Gauge Power Matrix Precision Wilson Tree Exterior AnalyticNext.QuarticMatch.Sheets Bloch FreeResolvent Work.F08 Shard Realm PathCost MeasureTheory Set Real
open Fountain Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {ι α β U:Type}{J I S T:Finset ι}{D k K':ι→ℕ}{d:ℕ}{c:Side}{B' i j i' j' a e r h N n m b b' l:ℕ}{G:Gauge}{σ τ u g B B₀ C x y z ρ β':ℝ}{E W V' U':Credit}

-- radius uniform integer halo. origin cov works with translated profiles (through center convention).
def yardLen (B:ℕ):ℕ:= B+2
lemma spectrum (P:Rarity d)(p:1≤y)(x:(P.radius)≤ (B':ℕ)*y) : cairnM P y y ≤ yardLen B':=by
    have hv:0<y:=lt_of_lt_of_le zero_lt_one p; unfold yardLen; apply Nat.ceil_le.mpr; rw [abs_of_pos hv]; apply (div_le_iff₀ hv).mpr; unfold radiusH; rw [abs_of_pos hv]; push_cast; linarith
lemma wanderC (P:Rarity d)(p:1≤y)(x:(P.radius)≤ (B':ℕ)*y)(o:Cover)(g:o∈canvasM P y y): Bank.terrain.gap 0 o≤ 4*yardLen B':=by
   let K:= yardLen B'; let T:=cairnM P y y; have hT:T≤ K:=spectrum P p x; change size (o-0)≤ _; rw [sub_zero]; simp only [canvasM, Fintype.mem_piFinset, Finset.mem_Icc] at g
   have H i : (o i).natAbs≤K:=by obtain ⟨a,b⟩:=g i; omega
   refine (Finset.sum_le_sum (g:=fun _=> K) (fun i _=> H i)).trans ?_; rw [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; rfl
lemma planeVol (X:Rarity d)(A:ℝ)(F:Amplitude X A)(p:1 ≤y)(o:CellR)(x:Cover): ‖wheelC y y x X.ψ o‖≤ A*y^d:=by
    have hv:=F.1; apply pledge (sonal y y o x X.ψ) (by positivity); intro j v w i; rw [currentP _ _ _ _ _ _ v,norm_mul, Real.norm_of_nonneg (by positivity)]; exact (mul_le_mul (pow_le_pow_right₀ p v) (F.2 _ v w _) (norm_nonneg _) (by positivity)).trans_eq (mul_comm ..)
lemma portE (x:ℝ)(h:1≤ x)(k): 0≤drumB k x ∧ drumB k x≤ x^4:=by
    refine ⟨drumC _ (zero_le_one.trans h) _,mul_le_of_le_one_right (by positivity) ?_ ⟩; exact inv_le_one_of_one_le₀ (one_le_pow₀ h)

section
variable [DecidableEq ι][Fintype ι]
def lengthC (G:Gauge)(D k:ι→ℕ)(e:ℕ):= (formalO G D k Finset.univ e).choose
variable {R:Realm G (e+1) E}
abbrev Vσ (R:Realm G (e+1) E)(m:ℕ)(h:R.anchor≤m):= min 1 (R.mint m h).σ
lemma perk (v:R.anchor ≤ m):0 < Vσ R m v:=lt_min one_pos (R.mint m v).width
omit [DecidableEq ι] in
lemma shelled (D:ι→ℕ)(p:Case D)(X:Finset ι): ‖touch p X‖≤∏ i∈X,‖p i‖:=by
   apply ContinuousLinearMap.opNorm_le_bound _ (Finset.prod_nonneg fun _ _=> norm_nonneg _); intro v
   rw [hit_leaf, mul_comm]; exact (v.le_opNorm _).trans (mul_le_mul_of_nonneg_left (folio_norm _) (norm_nonneg _))

lemma pedal (h:1≤ y)(v:0≤B)(P:Outerm G D)(F:Garland D) (q:Wellness k P)(X:ι→ℝ)(x:∀ i,Amplitude (F i) (X i)){B':ℕ}(t:∀ i,(F i).radius ≤ B'*y)(g:R.anchor ≤ b)(q':Uniform R P b g B)(p': i ≤ e) (z:CellR):
   let C:ℕ:= (2*yardLen B'+1)^4
   let U:=B *exp (4*yardLen B':ℕ)
   Cork Bank.terrain 0 (Vσ R b g) (( ∏ i':ι,(C:ℝ)*y^4*(X i' *y^(D i'))) * (lengthC G D k e *U^Fintype.card ι)) ((Finale y y z F k (AuthSum P)).2 i j):=by
   intro c U; let s:= Vσ R b g; let S:= boxes y y F; let f(p:ι→Cover):= AuthSum P p
   have he:0<s:= perk g; let Y (i:ι):= X i*y^D i; let c':=4*yardLen B'; let CC:= exp (c':ℝ); have hx:0≤U:=by unfold U; positivity
   have hC:1≤CC:= Real.one_le_exp (by positivity); let Z:= lengthC G D k e
   have hp (m:ι→Cover)(v':m∈S): trueKnots (P m) Finset.univ s U e:=by
       intro T _ i u j; by_cases z:T=∅; · subst T; rw [q.quiet' m]; simp only [Finset.card_empty,pow_zero]; exact Cork.zero.cost zero_le_one
       obtain ⟨i',hi⟩:= Finset.nonempty_iff_ne_empty.mpr z
       have hq:(m i')∈ canvasM (F i') y y:=(Fintype.mem_piFinset.mp v') i'
       have hg:(Bank.terrain.gap 0 (m i'):ℝ)≤ c':= Nat.cast_le.mpr (wanderC _ h (t i') _ hq)
       apply (cLeaf m hi hg he.le (Wig.shave (q' m T i u j) (show s≤_ from min_le_right ..))).cost; unfold U; rw [mul_pow]; refine mul_le_mul_of_nonneg_left ((Real.exp_le_exp.mpr (show s*(c':ℝ)≤ ↑c' from mul_le_of_le_one_left (by positivity) (min_le_left ..))).trans ?_) (pow_nonneg v _); change CC≤CC^T.card; nth_rw 1 [←pow_one CC]; exact pow_le_pow_right₀ hC (Finset.card_pos.mpr ⟨i',hi⟩)
   let B:= Z*U^Fintype.card ι; have hZ:0≤Z:=(formalO G D k Finset.univ e).choose_spec.1; have hB:0≤B:= mul_nonneg hZ (pow_nonneg hx _)
   have ht m (v':m∈S): Cork Bank.terrain 0 s B ((f m Finset.univ).2 i j):= (by simpa only [Finset.card_univ] using! (formalO G D k Finset.univ e).choose_spec.2 U s hx he.le _ (q.level' m) (hp m v') i p' j)
   have hf p:‖touch (lyra y y z F p) Finset.univ‖≤ ∏ i,Y i:=(shelled _ _ _).trans (Finset.prod_le_prod (fun i _=>norm_nonneg _) (fun i _=> planeVol _ _ (x i) h z (p i)))
   let A:=∏ i,y^4*Y i
   have hz i: 0≤Y i:= by have he:=(x i).1; unfold Y; positivity
   have hT:0≤ A:=Finset.prod_nonneg fun i _=>mul_nonneg (by positivity) (hz i)
   let W m:= lyric y k • scrollR y y z F (AuthSum P) m
   have hw m (v:m∈S): Cork Bank.terrain 0 s (A*B) ((W m).2 i j):=by
        let C:=ht m v; apply ((C.touch (touch (lyra y y z F m) _)).μ (lyric y k)).cost; rw [abs_of_nonneg (show 0≤ lyric y k from Finset.prod_nonneg fun i _=> (portE y h (k i)).1), ← mul_assoc]; apply mul_le_mul_of_nonneg_right _ hB; unfold A; rw [Finset.prod_mul_distrib]; apply mul_le_mul _ (hf m) (norm_nonneg (touch (lyra y y z F m) Finset.univ)) (Finset.prod_nonneg fun _ _=> show 0≤y^4 by positivity); exact Finset.prod_le_prod (fun i _=>(portE y h (k i)).1) (fun i _=>(portE y h (k i)).2)
   change Cork _ _ _ _ ((∑ i∈S,W i).2 i j); rw [Prod.snd_sum,Finset.sum_apply,Finset.sum_apply]; apply (Cork.sum hw).cost; rw [Finset.sum_const,nsmul_eq_mul,←mul_assoc]; apply mul_le_mul_of_nonneg_right _ hB; have hv:S.card ≤ ∏ _ :ι,c:=by
        unfold S boxes; rw [Fintype.card_piFinset]; apply Finset.prod_le_prod; · intros; omega
        intro i _; rw [canvas_count]; have he:=spectrum _ h (t i); unfold c; gcongr
   apply (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hv) hT).trans; unfold A; rw [Nat.cast_prod, ← Finset.prod_mul_distrib]; exact le_of_eq (Finset.prod_congr rfl (fun _ _=> (mul_assoc ..).symm))
end
end YM.WilsonCoeffUV.Wheel.Flooring
