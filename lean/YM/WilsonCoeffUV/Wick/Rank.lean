import YM.WilsonCoeffUV.Wick.Identity
/-!
# Wick jet exposure on the cover by arbitrary full bounded symbol
Not diluting. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.WilsonCoeffUV.Bank.Carp
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Soil Cosmos
open Exterior Next.Free
open scoped Topology BigOperators ContDiff
variable {c f:Side}{U V α β: Type*} [NormedAddCommGroup V][NormedSpace ℝ V] {r e j k n m:ℕ}{G:Gauge}{x s ξ σ A B:ℝ}
section
variable [Fintype U][Fintype α]
-- arbitrary any size cap

noncomputable def iceberg (G:Matrix U U ℝ)(P:Gen V U) : ℕ → Gen V U
    | 0=> P
    | i+1=> ((i+1:ℕ):ℝ)⁻¹ • ripple G (iceberg G P i)
def carve (u:ℕ)(G:Matrix U U ℝ)(P:Gen V U):= ∑ i∈Finset.range (u+1),iceberg G P i
lemma ice_r (u v:ℕ) (G: Matrix U U ℝ) {P:Gen V U} (h:still P (v+1)) : still (iceberg G P u) (v+1):=by
    induction u with
    | zero => exact h
    | succ u ih=> intro i hi; rw [iceberg, Pi.smul_apply, ripple_zero_at _ _ _ (ih (i+2) (by omega)), smul_zero]
lemma ice_tail (u:ℕ)(G:Matrix U U ℝ){P: Gen V U}(h:still P k)(p:r+2*u≥k): iceberg G P u r=0:=by
    induction u generalizing r with
    | zero=> apply h; omega
    | succ u ih=> rw [iceberg,Pi.smul_apply,ripple_zero_at _ _ _ (ih (r:=r+2) (by omega)), smul_zero]
lemma ice_s (u:ℕ)(G: Matrix U U ℝ){P:Gen V U}(h:Pure P): Pure (iceberg G P u):= by induction u with | zero=> exact h | succ i ih=> exact fun r=> (pure_ripple G ih r).smul _
lemma carved (u:ℕ)(G:Matrix U U ℝ){P:Gen V U}(h:still P k): still (carve u G P) k:=by intro j hj; rw [carve,Finset.sum_apply]; exact Finset.sum_eq_zero fun i _=> ice_tail i G h (by omega)
lemma sculpt (u:ℕ)(G:Matrix U U ℝ){P:Gen V U}(h:Pure P): Pure (carve u G P):=by intro j; rw [carve,Finset.sum_apply]; exact Blue.Smooth.sum fun i _=> ice_s i G h j
lemma ice_ink (k h)(G:Matrix U U ℝ){P:Gen ℝ U}(he:still P (k+1))(hp:Pure P): spanT h U (spreadH G (totalR P))=totalR (iceberg G P h) := by
    let M:= spreadH G (totalR P); let W:=iceberg G P
    induction h with
    | zero=> rw [span_zero]; exact (spreadSolves G _).2
    | succ i ih=>
       apply (smul_right_inj (M:=POL U) i.succ_ne_zero).mp
       rw [← span_clock, (spreadSolves G _).1,cadenceLap,ih,←visible_ripple G (show FiniteGen (W i) from ⟨_,ice_r i k G he⟩) (ice_s i _ hp),iceberg,visible_μ (finite_ripple G ⟨_,ice_r i k G he⟩),← Nat.cast_smul_eq_nsmul (R:=ℝ),smul_smul, mul_inv_cancel₀ (by positivity),one_smul]
lemma carving (u:ℕ)(G:Matrix U U ℝ){P:Gen ℝ U}(h:still P (u+1))(e:Pure P): totalR (carve u G P)= glaze G (totalR P):= by
    set Q: Scan U:=∑ i∈Finset.range (u+1), MvPolynomial.X (none:Option U) ^ i * launchT (totalR (iceberg G P i))
    have ht : spreadH G (totalR P)=Q:=by
       apply (MvPolynomial.optionEquivLeft ℝ U).injective; ext1 k
       change spanT k U (spreadH G (totalR P))= spanT k U Q; rw [ice_ink u k G h e]; unfold Q; rw [map_sum]; simp_rw [past_lamp]; by_cases hx:k<u+1
       · rw [Finset.sum_eq_single k]<;> simp +contextual [hx]
       rw [show iceberg G P k=0 from funext fun i=> ice_tail k G h (by omega), Finset.sum_eq_zero] ; simp [totalR]
       exact fun i hi=> if_neg (fun e:i=k=> hx (e ▸ Finset.mem_range.mp hi))
    rw [glazed,ht]; unfold Q; rw [carve,visible_sum (fun i _=>⟨_,ice_r i u G h⟩),map_sum]; refine Finset.sum_congr rfl fun i _=>by rw [map_mul, map_pow,stopT_X,stopT_launch,Option.elim_none,map_one,one_pow,one_mul]
end
section any
variable {v:U}{u:Cover}
-- Any bounded unused covariance, can propagate at exponential width fraction in leading finite lots. `stretchδ` compares two.
def shoulder (W:ropes U α β)(A:ℝ):Prop := 0≤ A ∧∀ x y, ‖W x y‖ ≤ A
structure SymbolK (P:(n:Side)→ ropes (Site n) α α)(T: ropes Cover α α): Prop where
   point x y: Tendsto (fun n=>P n (foldUnder n x) (foldUnder n y)) atTop (𝓝 (T x y))
   price: ∃ A:ℝ, ∀ᶠ n in atTop,shoulder (P n) A
lemma SymbolK.bound {P:(n:Side)→ ropes (Site n) α α}{T: ropes Cover α α}(h:SymbolK P T): ∃ A,shoulder T A:=by
    obtain ⟨A,H⟩:=h.price; obtain ⟨s,hp⟩:=H.exists; exact ⟨A,hp.1,fun x y=>le_of_tendsto (h.point x y).norm (H.mono fun i hi=>hi.2 _ _)⟩
lemma soul_bill {G:ropes U α α} {d:Distance U} {w:U}{P: Gen V (U×α)}(h:shoulder G A)(e:Cork d w s B (P (r+2)))(hp:0≤s): Peb d w s (A*B*((1/2:ℝ)*(r+1:ℕ)*(r+2:ℕ))) (rain G P r):=by
   have ha:= h.1; have hb:= e.1
   refine ⟨by positivity,fun x y=>?_⟩; rw [rain_spell,norm_smul,Real.norm_eq_abs]; simp_rw [abs_mul]; push_cast; simp only [abs_one,abs_div,abs_of_nonneg (by positivity : 0≤ (2:ℝ)), abs_of_nonneg (by positivity : 0≤(r:ℝ)+1), abs_of_nonneg (by positivity : 0≤(r:ℝ)+2)]
   calc
     _ ≤ (1/2:ℝ) * A *(r+1)*(r+2)*(B*Real.exp (-s*brims d w x y)):= mul_le_mul (by gcongr; exact h.2 _ _) ((e.2 _).trans (mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonpos_left (Nat.cast_le.mpr (tap_cup x y)) (neg_nonpos.mpr hp))) hb)) (norm_nonneg _) (by positivity)
     _ = _ := by ring
variable {R:ropes Cover α α}{K:(n:Side)→ ropes (Site n) α α}{P:Gen V (Cloth α)}{Q:(n:Side)→Gen V (Co n α)} {o:Cover}
lemma sunset (h:SymbolK K R)(e:Bends o (fun n=> Q n (r+2)) (P (r+2))): Paves o (fun n=>rain (K n) (Q n) r) (rain R P r):=by
   obtain ⟨a,A⟩:= h.price; obtain ⟨s,b,t,B⟩:= e.price
   refine ⟨fun x y=>?_,s,_,t,(A.and B).mono (fun n ⟨p,h⟩=>soul_bill p h t.le)⟩; simp_rw [rain_spell]; have he :=e.point (Fin.cons (y 1) (Fin.cons (y 0) x)); have hv n: Fin.cons ((slideC n y 1)) (Fin.cons (slideC n y 0) (slideC n x))=(foldUnder n ∘ Fin.cons (y 1) (Fin.cons (y 0) x)):= by rw [←comps_head,←comps_head]; rfl
   simp_rw [hv]; exact ((((h.point (y 0) (y 1)).const_mul _).mul_const _).mul_const _).smul he
variable [Fintype α] [CompleteSpace V]
noncomputable def ivern (T:ropes Cover α α)(P:Gen V (Cloth α)) : ℕ→ Gen V (Cloth α)
    | 0=> P
    | i+1 => ((i+1:ℕ):ℝ)⁻¹ • rime T (ivern T P i)
def mason (T:ropes Cover α α)(P:Gen V (Cloth α))(u:ℕ):=∑ i∈Finset.range (u+1),ivern T P i
lemma icy (h:SymbolK K R)(e:Bends o (fun n=> Q n (r+2*j)) (P (r+2*j))): Bends o (fun n=> iceberg (K n) (Q n) j r) (ivern R P j r):=by
    induction j generalizing r with
    | zero=> simpa only [iceberg,ivern,Nat.mul_zero, Nat.add_zero] using e
    | succ j ih=>
      have hb:r+2*j.succ=r+2+2*j:= by omega
      rw [hb] at e
      have he:= sunset h (ih (r:=r+2) e); simp_rw [iceberg,ivern,Pi.smul_apply,←rain_reads]; exact (he.rest).μ _
lemma mason_path (h: SymbolK K R)(u:ℕ)(p:∀ i,Bends o (fun n=> Q n i) (P i))(r): Bends o (fun n=>carve u (K n) (Q n) r) (mason R P u r):= leaderT (P:=fun n i=> iceberg (K n) (Q n) i) (F:=ivern R P) (fun _ _=> icy h (p _))
omit [CompleteSpace V] [Fintype α] in
lemma ice_none (h:still P n)(p:r+2*j≥n): ivern R P j r=0:=by
   induction j generalizing r with
   | zero=> apply h; omega
   | succ k ih=> funext w; rw [ivern,Pi.smul_apply,Pi.smul_apply,rime,ruins]; simp_rw [rain_spell, ih (r:=r+2) (by omega)]; simp
omit [CompleteSpace V] [Fintype α] in
lemma mason_cap (v:ℕ)(h:still P (k+1)): still (mason R P v) (k+1):= by intro i hi; rw [mason,Finset.sum_apply]; exact Finset.sum_eq_zero fun u _=> ice_none h (by omega)
omit [CompleteSpace V] [Fintype α] in
lemma mason_delta (v:ℕ)(h:still P (k+1))(hp:k≤v): mason R P v=mason R P k:= by
   unfold mason; symm; apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hp _)); intro i _ hi; exact funext (fun r=> ice_none h (show k+1≤r+2*i from by have hg : k+1 ≤ i :=Nat.le_of_not_gt fun hv=>hi (Finset.mem_range.mpr hv); omega))
end any
end YM.WilsonCoeffUV.Bank.Carp
