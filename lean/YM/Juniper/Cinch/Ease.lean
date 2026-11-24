import YM.Juniper.Cinch.Shift
set_option autoImplicit false
noncomputable section
namespace YM.Juniper.Cinch
open Function Filter Metric Lattice Wilson RG PhysicalNext PhysicalNext.Repeat
open Push Push.AbsoluteSums AnalyticBridge VerifiedReset Collection Averaging
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G: Gauge}{c:Side}{X:Support c}{W:BudgetPoint}
set_option quotPrecheck false
local notation "p"=> Averaging.axes01
open Boulevard Meadow Further.LogJets Pressure Quot Real
local notation "H"=> logHessian
local notation "V"=> Directions G c
local notation "N"=> (Fintype.card (Site c):ℝ)
variable {U V':Listing G c}{A B:Collection.Source G c}{b d v w τ σ : ℝ}(h : Collection.Local U W A b v)
  (hB: Collection.Local V' W B d w)(hG:G.Simple)
-- pre-local exact; both orientations genuine. EBudget stronger. Exposed differences of pulses in θ units; augment.
abbrev Throng (A: Collection.Source G c) := Boulevard.throng A.logRead
include h hG
lemma meets_o (x:V) : HasSum (fun i=> H (A.logRead i) x x) (leftDerivs (Throng A) [x,x] 1):= by
    obtain ⟨f,hf,hV⟩:= h.cheap; have hp:= Boulevard.planetary hV (fun i=> (hf i).1)
    have ho:= Boulevard.enclosed h.smooth hp.2.1 hf; have he:= h.smooth; have h₁ : (1:Config G c)∈sunny W:= fun i=> by simpa [Gauge.chord,faceValue,square,travel,Lattice.Step.read, posDir, negDir] using W.threshold_pos
    have hh:[x,x].length ≤ W.order:= by simp; linarith only [W.order_ge]
    simp_rw [hessian_diag hG (h.smooth _), Throng]; exact ((Termwise.smooth_exchange (Boulevard.sky W) ho 1 h₁).2 [x,x] hh).symm ▸ (ho.sums [x,x] hh 1 h₁).hasSum
lemma almond (x y:V): HasSum (fun i=> logHessian (A.logRead i) x y) ( (leftDerivs (Throng A) [x+y,x+y] 1-leftDerivs (Throng A) [x,x] 1-leftDerivs (Throng A) [y,y] 1)/2):=by
   let d(w):= leftDerivs (Throng A) [w,w] 1; have hz:= (((meets_o h hG (x+y)).sub (meets_o h hG x)).sub (meets_o h hG y)).mul_right ((2:ℝ)⁻¹); rw [div_eq_mul_inv]; apply HasSum.congr_fun hz; intro i
   simp only [hessian_eq,map_add,add_apply]; simp_rw [← hessian_eq,hessian_symm (h.smooth _) y x]; ring
lemma shone (hn:4≤c.val): N*delta (U.read A)= ∑' i,projection (U.reg i) (A.logRead i) p p:=by
   let g(x:Site c):= total (U.read A) x p p
   have he(x:Site c): g x= delta (U.read A):=(isotropic hG h.projects hn x h.transforms p p).trans (if_pos rfl)
   rw [show N*delta (U.read A)=∑ x':Site c,g x' from by simp_rw [he]; rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]]
   unfold g total; rw [← Summable.tsum_finsetSum (f:=fun i x=> censusAt (U.read A) i p p x) (fun i _=> h.projects.seriesAt hG _ _ i)]; refine tsum_congr fun i=>?_ ; simp [censusAt]; rfl

variable {K: PathData G}{β ε:ℝ}{c':Clip}
include hB
omit hG in
lemma thrive (he: earlyValue U K c' W A β τ ε=earlyValue V' K c' W B β σ ε)(x :V): leftDerivs (Throng A) [x,x] 1=leftDerivs (Throng B) [x,x] 1:= by
    let F(A: Collection.Source G c) := Throng A; let r0:(Config G c→ℝ):= fun _=> (τ-σ) * N
    have hE(V':Config G c)(hh : V'∈ sunny W)(Y:Listing G c)(D:Collection.Source G c)(b:ℝ): earlyValue Y K c' W D β b ε V'= Real.exp (b*N - K.inChannels c' W β V' - F D V')*Real.exp (-ε*receipt K c' W V'):=by
       have hp: (Y.read D).additive W V'= F D V':= by
          apply tsum_congr; intro i; apply masked_eq _ _ _ _ (by unfold Healthy; rw [smoky hh]; simp)
       unfold earlyValue Rep.eval Rep.exponent; unfold frozen; dsimp only; rw [hp, Activities.gas_one _ _ (smoky hh),mul_one] -- fix
    have h₁ : (1:Config G c)∈sunny W:= fun i=> by simpa [Gauge.chord,faceValue,square,travel,Lattice.Step.read, posDir, negDir] using W.threshold_pos
    have ht: F A-F B=ᶠ[𝓝 1] r0:= by
       filter_upwards [(sky W).mem_nhds h₁] with x hx; have hc:= congr_fun he x; rw [hE x hx U, hE x hx V'] at hc; have hp:= Real.exp_injective (mul_right_cancel₀ (Real.exp_ne_zero _) hc); change F A x-F B x=(τ-σ)*N; linarith only [hp]
    have hh:= hB; let t:=(W).order; have hv (U:Listing G c)(a:Collection.Source G c)(b d)(ht: Collection.Local U W a b d): Push.Local.Chart W.order (F a) 1 := by
       obtain ⟨f,hf,hA⟩:= ht.cheap; exact (Termwise.smooth_exchange (Boulevard.sky W) (enclosed ht.smooth (Boulevard.planetary hA (fun i=>(hf i).1)|>.2.1) hf) 1 h₁).1
    have hQ:= W.order_ge; apply eq_of_sub_eq_zero; change leftDerivs (F A) _ _ - leftDerivs (F B) _ _=0; rw [← VerifiedReset.left_sub (hv _ _ _ _ ‹_›) (hv _ _ _ _ hB) (by simp; omega), (UVNext.PricedKernels.left_congr ht _).self_of_nhds]; simp [r0,Work.G07.left_const]
lemma bloom (he: earlyValue U K c' W A β τ ε=earlyValue V' K c' W B β σ ε): (∑' i,coke (A.logRead i))=∑' i,coke (B.logRead i):=by
   have hs(x y:Site c): (∑' i,pullback (f:=A.logRead i) x y)=(∑' i,pullback (f:=B.logRead i) x y):= by
      rw [show ∑' i,pullback (f:=A.logRead i) x y= _ from (almond h hG _ _).tsum_eq,show ∑' i,pullback (f:=B.logRead i) x y= _ from (almond hB hG _ _).tsum_eq]; simp_rw [Cinch.thrive h hB he] -- ht omission
   have ht (a: Collection.Source G c)(b d)(Y)(h : Collection.Local Y W a b d): (∑' i,coke (a.logRead i))=∑ j:Site c,∑ k:Site c,(coord j k (p).val.1)^2*(∑' i,pullback (f:=a.logRead i) j k):= by
      let k(x y:Site c):=(coord x y (p).val.1)^2; have hp(x y:Site c): Summable (fun i=>k x y * pullback (f:=a.logRead i) x y):= (almond h hG _ _).summable.mul_left _
      unfold coke; rw [Summable.tsum_finsetSum (fun i _=> summable_sum fun j _=> hp i j)]; simp_rw [Summable.tsum_finsetSum (fun i _=> hp _ i), tsum_mul_left]; rfl
   rw [ht A b v U h, ht B d w V' hB]; simp_rw [hs]
end YM.Juniper.Cinch
