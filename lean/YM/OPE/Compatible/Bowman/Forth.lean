import YM.OPE.Compatible.Estuary.Line
/-!
# Exact inertia metric characters and α-input.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Votive
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Work.F05 Flume Flume.Script Frequency
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J Y Z:Type}{G:Gauge}{n c:Side}{S:StepData c c}{p q:Clip}{R T:PathData G} {P:Patch}{K:KernelChoices}{V:ChartRatio G} {i j t r m:ℕ} {s s' u α T₁ T₂ b b' d U ℓ:ℝ}{B:Sponsor G} {H:Seasons B}
namespace Alps
variable (A: Alps B H i b) (hi:4 ≤ i)
abbrev root := Op B.K A.gear
include hi
lemma tiltBed (n:Side): (A.root).acts n= Precision.K (A.sky.metric.acts n):=by
     rw [Op_stays hi]; unfold Precision.K; rw [A.active.2.1.metric, Matrix.mul_assoc,Matrix.mul_assoc, (obligations B.K.penalty (B.l i) B.K.penalty_pos (B.h.net _) hi A.gear n).2.2.1]
lemma inkTot (n:Side)(x y: Bid.Dir G n): iteratedFDeriv ℝ 2 (swornV A.clip A.live (n:=n)) 0 ![x,y]= dotProduct (flatten x) (tensor G (A.root.acts n) *ᵥ flatten y):=by
    have hh := chartK A.live A.clip n A.pays -- arg
    have hz:=low_columns A.pays A.fills (A.active.2.2.2.1 n) (A.active.2.2.2.2 n)
    let R:= A.live; let Y:=A.sky; let L:=(arm G n 1).symm.toContinuousLinearMap; let C:=inputSeries A.clip A.live (m:=n)
    have hp(z:Bid.Dir G n): L z=(arm G n 1).symm z:=rfl
    have hv(ξ:Bid.Dir G n): arm G n 1 (L ξ)=ξ:= (arm G n 1).apply_symm_apply ξ; rw [hh.2, show swornX A.live A.clip (n:=n)= C ∘ L from funext (fun i=>congr_arg (fun p=> secondTerm A.clip A.live (represent p)) (hv i).symm), jets_linear L ((stain_knit _ _ A.pays).analytic.contDiffAt)]
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]; rw [show (fun j:Fin 2=> L (![x,y] j))=![L x,L y] from funext fun i=> by fin_cases i <;>rfl, hz.2.2, hv x, hv y,component_dot]; simp_rw [component_mul]; rw [tiltBed];rfl; exact hi
-- delta in same alphabet. Counting equality.
omit hi in
lemma delta_lent (j:Tab (Shade G) n): flatten ((spool G n).symm (deltaH j)) = deltaH (lent G n j) :=by
    ext1 i; obtain ⟨i,rfl⟩:= (lent G n).surjective i; rw [show flatten _ _= deltaH j i from congr_fun ((altPaint _).trans ((spool G n).apply_symm_apply (deltaH j))) i]; by_cases hp:i=j; rw [hp]; simp [deltaH]; simp [deltaH, hp, (lent G n).injective.ne hp]
lemma ticket (v:Page (Shade G) 2)(hx:v.primary=0)(n:Side):
    scribe (0:Site n) (inkV A.live A.clip 2) (hand v n)=tensor G (A.root.acts n) (lent G n (0,(v 0).2)) (lent G n (wrap n (v 1).1,(v 1).2)):=by
      let p:Tab (Shade G) n:=(0,(v 0).2); let q:=((wrap n (v 1).1,(v 1).2)); let x:=(spool G n).symm (deltaH p); let y:=(spool G n).symm (deltaH q)
      obtain ⟨hh,H,hY⟩:= inkSongs A.live A.clip n 2 0 A.pays; have he : hand v n=(spool G n).toContinuousLinearMap∘![x,y]:=by
          have ht:(v 0).1=0:=hx
          ext1 i; fin_cases i
          · change deltaH (wrap n (v 0).1,(v 0).2)=spool G n x; rw [ht,map_zero];exact ((spool G n).apply_symm_apply _).symm
          exact ((spool G n).apply_symm_apply _).symm
      rw [← centerSync _ hh.1 hx, he,hY ![x,y], A.inkTot hi,show flatten x= _ from delta_lent p, show flatten y= _ from delta_lent q]; change dotProduct (deltaH _) ((tensor G (A.root.acts n))*ᵥ deltaH _) = _; simp only [deltaH]; simp; rfl -- include arguments? delta_lent has hi?
omit hi in
lemma rootsync {A: Row I J}(hp:Whole A)(x:Cover)(p:I)(q:J): Tendsto (fun i:ℕ=> A.acts (epochX i) (0,p) (wrap _ x,q)) atTop (𝓝 (A p q x)):=by
   let f(y):= if y=x then A p q y else 0; let g(j:Side)(y:Cover):ℝ:= if wrap j x =0+wrap j y then A p q y else 0; have hh: ∑' i,f i= A p q x:=by unfold f;simp
   have h := hp.safe p q; let V(i:ℕ):=epochX i; have ht:Tendsto (fun i=>(V i).val) atTop atTop:=tendsto_add_atTop_nat _; rw [← hh]; change Tendsto (fun i:ℕ=>∑' j:Cover,g (V i) j) _ _
   apply tendsto_tsum_of_dominated_convergence h; swap; · apply Eventually.of_forall; intro x i; unfold g; split_ifs <;> simp
   intro i; unfold f g; split
   next he=>rw [he]; simp
   next he=> apply tendsto_const_nhds.congr'; filter_upwards [eventually_unfold V ht x,eventually_unfold V ht i] with j hy hp; rw [if_neg]; intro h; rw [zero_add] at h; exact he (hp ▸ hy ▸ congr_arg lift h.symm) -- rw[if_neg] ordering
lemma textReal (v:Page (Shade G) 2)(hv:v.primary=0): inkV A.live A.clip 2 v= if (v 0).2.2=(v 1).2.2 then A.root (coord (v 0).2.1) (coord (v 1).2.1) (v 1).1 else 0:=by
    obtain ⟨c,H⟩:= (inkSongs A.live A.clip 1 2 0 A.pays).2.1; let V(i:ℕ):=epochX i; have he:Tendsto (fun i=>(V i).val) atTop atTop:=tendsto_add_atTop_nat _; apply tendsto_nhds_unique (lands _ (sootS H) v V he)
    simp_rw [A.ticket hi v hv]; by_cases hx:(v 0).2.2=(v 1).2.2; swap; · rw [if_neg hx]; exact tendsto_const_nhds.congr (fun i=> (if_neg hx).symm : ∀ i:ℕ,_ = tensor G _ _ _)
    rw [if_pos hx]; exact (rootsync (A:= A.root) (Op_whole hi _) (v 1).1 ..).congr (fun _=> (if_pos hx).symm)
end Alps
end YM.OPE.Votive
