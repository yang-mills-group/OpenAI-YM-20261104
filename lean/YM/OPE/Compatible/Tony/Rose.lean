import YM.OPE.Compatible.Tony.Hill
/-!
# Ease through arc labels. Exponential layers.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume.Script
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Work.F08 Matrix Bloch Precision Wilson Planned.PrimaryIntegral295.Carrier
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J X Y:Type*}{d m r k i:ℕ}{G:Gauge}
namespace Wool
variable {a b s K σ C D:ℝ}
open Page
lemma tump (G:Gauge)(n r:ℕ)(s:ℝ)(h:0<s):∃ c:ℝ,0 ≤ c∧∀ x:Signed,∀ A:I→ Atom G n,∀ K,SumBudget (fun i=>(A i).budget s) K→ Felt (paymentAtoms A x r) (cone (s/2) r) (c*K):=by
       obtain ⟨u,hu,H⟩:=brief (I:=I×Cue G n) G _ _ n r (half_pos h) (lumenD G); exact ⟨u,hu,fun i A K hp=> H _ _ K (smelt_cost hp h i) fun i j=>brightD _ _ _⟩
lemma vats (G:Gauge)(p:Clip)(s b:ℝ)(hs:0<s)(hB:0≤b)(r:ℕ):∃ c:ℝ,0 ≤ c∧∀ R:PathData G,∀ U,R.Bounds p s b U → Felt (oathX R p r) (cone (s/2) r) c:=by
       obtain ⟨C,hC,H⟩:=brief (I:=ℕ×ℕ) G _ _ 2 r (half_pos hs) (lumenD G); obtain ⟨F,hF,W⟩:=brief (I:=Unit) G (s/2) _ 1 r (half_pos hs) (lumenD G); obtain ⟨X,hX,A⟩:= tump (I:=ℕ) G 3 r s hs; obtain ⟨Y,hY,Q⟩:= tump (I:=ℕ) G 4 r s hs; let f:Signed→PlaqAxes→ℝ:=fun _ _=>‖p.direct‖*(F*Real.exp ((s/2)*4))+‖(1/2:ℝ)‖*(∑ _ :G.ColorIndex,C*(b*b)); let t(x):= (∑ j,f x j)+X*b+Y*b
       have hh(x):0 ≤ t x:=by
            apply add_nonneg (add_nonneg (sum_nonneg fun i _=>?_) (mul_nonneg hX hB)) (mul_nonneg hY hB); unfold f; positivity
       refine ⟨‖avgF‖*(∑ i,t i),mul_nonneg (norm_nonneg _) (sum_nonneg fun i _=>hh i),fun R U h=>?_⟩; let a:=cone (s/2) r; refine Sack.scale_line (Sack.finGather _ _ _ (fun i _=>?_) (fun i=>saltRat _)) _; change Felt (loftX R p i r) a (t i)
       apply Sack.splits (Sack.splits (A:=∑ j,f i j) ?_ (A _ _ b h.three) (fun _=>saltRat _)) (Q i _ b h.four) (fun _=>saltRat _); refine Sack.finGather univ (fun j=> waistX R p i j r) (f i) (fun j _=>?_ ) (fun _=>saltRat _); apply Sack.splits (Sack.scale_line (W _ _ _ (ledgerF j i G _) (fun _ _=>litD _ _)) _) _ (fun _=>saltRat _); exact Sack.scale_line (Sack.finGather univ (fun u=>twin R i j u r) _ (fun u _=> H _ _ _ (duet_cost h i j u) (duet_funds R i j u)) (fun _=>saltRat _)) _
lemma va_roi (G:Gauge)(s:ℝ)(hs:0<s)(r:ℕ):∃ C:ℝ,0 ≤ C∧∀ (p:Clip)(R:PathData G)(b U:ℝ),R.Bounds p s b U→ Felt (oathY R r) (cone (s/2) r) (C*U):=by
       obtain ⟨c,hc,H⟩:= tump (I:=ℕ) G 2 r s hs; refine ⟨‖avgF‖*((Fintype.card Signed):ℝ)*c,(by positivity),fun p R b U h=>?_⟩; apply Sack.tips (Sack.scale_line (Sack.finGather univ (fun i:Signed=>paymentAtoms R.loop i r) (fun _=>c*U) (fun i _=> H _ _ _ h.two) (fun _=>saltRat _)) avgF); simp only[sum_const,nsmul_eq_mul,card_univ]; exact le_of_eq (by ring)
-- Unsilt, F.
open OPE.Votive Variance
lemma cull {I:Type}[Fintype I] {R:Script I r}{n:Side} (h:Felt R a b) (he:0<a)(x:Fin r→deck I n):library n (expose R) x=library n (expose (silt R)) x := by rw [expose,expose,libScale,libScale,silt_read (Sack.water h (fun i=>sorgh i he.le))]
lemma payroll (p:PathData G)(P:Clip)(h:p.Bounds P σ C D)(k:ℕ)(n:Side): Voice (expose (oathX p P k)) (spool G n).toContinuousLinearMap (swornV P p):=by
       intro v; obtain ⟨c,hc,H⟩:= vats G P σ C h.width ((tsum_nonneg (h.rows (⟨(0,1),by decide⟩:PlaqAxes)).1).trans (h.rows _).2.2) k; rw[cull (H _ _ h) (peak _ _ (half_pos h.width))]; exact (inkSongs _ _ _ k 0 h).2.2 v
lemma payrollL (p:PathData G)(P:Clip)(h:p.Bounds P σ C D)(k:ℕ)(n:Side): Voice (expose (oathY p k)) (spool G n).toContinuousLinearMap (swornY p):=by
       intro v; obtain ⟨c,hc,H⟩:= va_roi G _ h.width k; rw [cull (H _ _ _ _ h) (peak _ _ (half_pos h.width))]; exact (leafSongs _ _ _ k 0 h).2.2 v
end Wool
end YM.OPE.Flume.Script
