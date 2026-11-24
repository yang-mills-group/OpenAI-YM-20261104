import YM.RG11Proof.Rigidity.Ice.Stroll

/-!
# Closed charge ledger
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity.Ice
open Fields Labels Maxwell Function Extra.FD Reads Maxwell.Free Set Filter Pert.Position
open scoped Classical BigOperators Topology ContDiff InnerProductSpace
variable {G:Gauge}{F:Frames G}{d:ℕ}
local notation "V"=>G.Color
local notation "Y"=> V→L[ℝ] V

lemma stock (Q:TaylorTower G) (p:WickPol G): Continuous (fun O:Y => probe (films O Q) p) := by
  induction p using MvPolynomial.induction_on with
  | C c=> simp [probe]; exact continuous_const
  | add p q hp hq=>simp_rw [map_add]; exact hp.add hq
  | mul_X p a hp=>
    simp_rw [map_mul,←symbol_coordinate,symbol_test]
    apply hp.mul (Complex.continuous_ofReal.comp ?_)
    apply (coordinateLeg a).continuous_of_finiteDimensional.comp
    let D : Y→ₗ[ℝ] Shell G a.1:={
        toFun O:= films O Q a.1
        map_add' o i:= by apply Subtype.ext; funext h j; apply ContinuousMultilinearMap.ext; intro v; rfl
        map_smul' t o:= by apply Subtype.ext; funext h j; apply ContinuousMultilinearMap.ext; intro v; rfl }
    exact D.continuous_of_finiteDimensional

lemma both_axes (Q:TaylorTower G)(n:ℕ): Continuous (fun p : Y×E F d=> quoteL F n (films p.1 Q) p.2) := by
  let b:=(tower F d).b
  conv => arg 1; intro p; rw [←b.sum_equivFun p.2, map_sum]
  refine continuous_finsetSum _ fun i _=> ?_
  simp_rw [map_smul]; exact ((continuous_apply i).comp (b.equivFun.toLinearMap.continuous_of_finiteDimensional.comp continuous_snd)).smul ((stock Q (Reads.top n (writes F d (b i)))).comp continuous_fst)

private lemma ice_factors (b:Buffer F d) :
    {q : ℝ×Y| Feasible b q.1 q.2} = (⋂ x:V,⋂ y:V,{q : ℝ×Y| ⟪q.2 x,q.2 y⟫_ℝ=⟪x,y⟫_ℝ}) ∩
    (⋂ i:News F d,⋂ Q:TaylorTower G,{q:ℝ×Y|quoteL F i.n Q i.v=quoteL F i.n (films q.2 Q) (drive b.val i.v q.1)}):= by ext1 q; simp only [Feasible,mem_setOf_eq,mem_inter_iff,mem_iInter]
private lemma news_eq (b:Buffer F d)(i:News F d)(Q:TaylorTower G):
    IsClosed {q:ℝ×Y|quoteL F i.n Q i.v=quoteL F i.n (films q.2 Q) (drive b.val i.v q.1)}:= by
  have hh (i:News F d) : Continuous (fun p : ℝ×Y=> (p.2,drive b.val i.v p.1)):=continuous_snd.prodMk (((show Differentiable ℝ (drive b.val i.v) from fun t=> (march b.val _ t).differentiableAt).continuous).comp continuous_fst)
  have h₁:= (both_axes (F:=F) (d:=d) Q i.n).comp (hh i)
  simp only [Function.comp_def] at h₁
  exact @isClosed_eq ℂ (ℝ×Y) _ _ _ (fun _ : ℝ×Y => quoteL F i.n Q i.v) (fun q:ℝ×Y=> quoteL F i.n (films q.2 Q) (drive b.val i.v q.1)) continuous_const h₁
private lemma iso_eq (x y : V) : IsClosed {q : ℝ×Y| ⟪q.2 x,q.2 y⟫_ℝ=⟪x,y⟫_ℝ}:= by
  have he (x : V) : Continuous fun p:ℝ×Y=>p.2 x := (ContinuousLinearMap.apply ℝ V x).continuous.comp continuous_snd
  exact isClosed_eq ((he x).inner (he y)) (continuous_const (y:=inner ℝ x y))
lemma iceClosed (b:Buffer F d) : IsClosed {q : ℝ×Y| Feasible b q.1 q.2} := by
  rw [ice_factors]; exact (isClosed_iInter (fun x=>isClosed_iInter fun y=> iso_eq x y)).inter
    (isClosed_iInter fun i=>isClosed_iInter fun Q=> news_eq b i Q)

lemma ice_ball {t:ℝ}{O:Y}{b:Buffer F d}(h:Feasible b t O): O∈Metric.closedBall (0:Y) 1:=by
  have ht (x : V): ‖O x‖=‖x‖:=by obtain ⟨v,rfl⟩:=h.folds; exact v.norm_map _
  rw [Metric.mem_closedBall,dist_zero_right]; apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; simp [ht]

lemma ice_pool (b:Buffer F d)(t:ℝ) : IsCompact {p:Y| Feasible b t p}:=by
  let A:={q:ℝ×Y|Feasible b q.1 q.2}
  exact (isCompact_closedBall (0:Y) 1).of_isClosed_subset ((iceClosed b).preimage (continuous_const.prodMk continuous_id)) (fun _ hk=>ice_ball hk)

end YM.RG11.Rigidity.Ice
