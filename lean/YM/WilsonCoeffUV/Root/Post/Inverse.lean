import YM.WilsonCoeffUV.Root.Post.BlockDiagonal
/-! # Exact inverse support and pre-price bound in diagonal sectors. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n c:Side}{U V E:Type*}{r h D l j e k a m:ℕ} {G:Gauge}{F:Labels.Frame G h}{s t t' A X B C δ:ℝ}
lemma quiet {A: Coil F}(p:leaseM n F (lineS A 0))(x y:Alma F)(g: highUp F x ≤ highUp F y): lineS A⁻¹ 0 x y= if x=y then (matPow n x)⁻¹ else 0:= by
    rw [line_steed p,steed,saddle, Matrix.diagonal_mul]; unfold hamp; rw [Matrix.sum_apply, Finset.sum_eq_single 0, pow_zero]; swap
    · intro b hb h; exact (rapid.nesting p).power b x y (by omega)
    swap; · simp [ceiling]
    by_cases h:x=y; · subst y; simp
    simp [h]
lemma eased {A: Coil F}(p:leaseM n F (lineS A 0)) (x:Alma F): ‖lineS A⁻¹ 0 x x‖≤ 1:= by rw [quiet p x x le_rfl,if_pos rfl,Real.norm_of_nonneg (inv_nonneg.mpr (zero_le_one.trans (matPow₁ ..)))]; exact inv_le_one_of_one_le₀ (matPow₁ ..)

def Rapt (F:Frame G h)(A:Wall F)(C:ℝ): Prop:= 0≤ C ∧ ∀ i j:Alma F,valence F i=valence F j→ ‖A i j‖≤ C
lemma rapt_zero :Rapt F 1 1:=⟨zero_le_one,fun i j _=> by
   by_cases h:i=j; · subst j; simp
   simp [h]⟩
lemma Rapt.mul {A B:Wall F}{K:ℝ}(p:Rapt F A C)(q:Rapt F B K)(a:Tram F 0 A)(b:Tram F 0 B): Rapt F (A*B) ((Fintype.card (Alma F):ℝ)*C*K):=by
    have hp:=p.1; have hq:=q.1; refine ⟨by positivity,fun i j u=>?_⟩
    rw [Matrix.mul_apply]; apply (norm_sum_le ..).trans; refine (Finset.sum_le_sum (g:=fun _=>C*K) (fun v _=>?_)).trans_eq (by simp [mul_assoc]);
    by_cases h: valence F v= valence F i
    · rw [norm_mul]; exact mul_le_mul (p.2 i v h.symm) (q.2 v j (h.trans u)) (norm_nonneg _) hp
    rcases lt_or_gt_of_ne h with hh|hh; · rw [a i v (by omega),zero_mul,norm_zero]; positivity
    rw [b v j (by omega),mul_zero,norm_zero]; positivity
lemma wellB (F: Frame G h)(C:ℝ)(r:ℕ)(h:0≤C): ∃ B:ℝ,0≤B∧∀ Y:Wall F, Tram F 0 Y → Rapt F Y C → Rapt F (Y^r) B:=by
    induction r with
    | zero=> exact ⟨1,zero_le_one,fun Y _ _=>by rw [pow_zero]; exact rapt_zero⟩
    | succ r ih=>
       obtain ⟨B,b,h⟩:=ih; refine ⟨(Fintype.card (Alma F):ℝ)*B*C,?_ ,fun Y p g=>?_⟩; · positivity
       rw [pow_succ]; exact (h Y p g).mul g (p.power r) p
lemma holdShelter (F:Frame G h)(C:ℝ)(p:0≤C): ∃ B:ℝ,0≤B∧∀ n:Side,∀ A:Wall F,leaseM n F A → (∀ i j: Alma F,valence F i= valence F j→ ‖A i j‖≤C*matPow n j) → Rapt F (steed A n) B:=by
    choose D hd H using fun r=>wellB F (1+C) r (by positivity)
    let K:= ∑ j∈Finset.range (ceiling h),D j; have hk :0≤ K:= Finset.sum_nonneg fun _ _=> hd _
    refine ⟨K,hk,fun n a h g=>?_⟩
    let f:= negNest a n; have hx : Rapt F f (1+C):=by
       refine ⟨by positivity,fun i j v=>?_⟩; unfold f negNest; rw [Matrix.sub_apply, saddle, Matrix.mul_diagonal]; have hp:=zero_lt_one.trans_le (matPow₁ n j)
       apply (norm_sub_le ..).trans; apply add_le_add (rapt_zero.2 i j v); rw [norm_mul,Real.norm_of_nonneg (inv_nonneg.mpr hp.le)]; exact (mul_le_mul_of_nonneg_right (g i j v) (inv_nonneg.mpr hp.le)).trans_eq (mul_inv_cancel_right₀ hp.ne' _)
    have hh : Rapt F (hamp a n) K:=by
        refine ⟨hk,fun i j v=>?_⟩; unfold hamp; rw [Matrix.sum_apply]; exact (norm_sum_le ..).trans (Finset.sum_le_sum fun i' _=> (H i' f (Tram.nesting h.1) hx).2 i j v)
    refine ⟨hk,fun i j v=>?_⟩; rw [steed,saddle, Matrix.diagonal_mul,norm_mul]; apply le_trans _ (hh.2 i j v); rw [Real.norm_of_nonneg (inv_nonneg.mpr (zero_le_one.trans (matPow₁ ..)))]; exact mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ (matPow₁ ..))
end YM.WilsonCoeffUV.Cosmos
