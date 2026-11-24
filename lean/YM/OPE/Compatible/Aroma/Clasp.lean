import YM.OPE.Compatible.Aroma.Nape
/-! # Shell factor input at one grade -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free Maxwell Exterior Tensor WithLp Work.F08 Matrix Bloch Planned.PrimaryIntegral295.Carrier Precision
open scoped Topology BigOperators Classical
variable {r d' m n j:ℕ}{b e s:ℝ}{I J W T:Type*} {G:Gauge}
namespace Script
open Page
abbrev TLim (G:Gauge) (n:ℕ):= Labels.Taylor G n
abbrev Fang (G:Gauge)(n:ℕ):= (Axis × (Fin n→Axis)) × G.ColorIndex
def pierce (G:Gauge)(n:ℕ) : TLim G (n+1) →ₗ[ℝ] (Fang G n → ℝ) where
    toFun t k:= flame t k.1.1 (basis∘k.1.2) k.2
    map_add' := by
        intro a b; funext k; let f (p:TLim G (n+1)):=takeCurl p; have he(i j):takeCurl (a+b) i j=takeCurl a i j+takeCurl b i j:=congr_arg (fun p=> (p:formSpace _ _).val i j) (Maxwell.potential.map_add a b)
        simp only [flame,he, _root_.sum_apply,ContinuousMultilinearMap.curryLeft_apply, _root_.add_apply,Finset.sum_add_distrib]; rfl
    map_smul':=by
        intro t a; funext k; have he (i j):takeCurl (t • a) i j=t • takeCurl a i j:=congr_arg (fun p=> (p:formSpace _ _).val i j) (map_smul Maxwell.potential t a)
        simp only [flame,he, _root_.sum_apply,ContinuousMultilinearMap.curryLeft_apply,_root_.smul_apply,← Finset.smul_sum]; rfl
lemma sparks {A: TLim G (n+1)} {b:Axis}(hp: pierce G n A=0): flame A b=0:=by
    ext1 x; let T:=flame A b; have hx : (fun i:Fin n=> ∑ j:Axis,x i j • basis j) =x:=by funext i; ext j;simp
    rw [show flame A b x=T (fun i=> ∑ j:Axis,x i j • basis j) from congr_arg T hx.symm]; rw [T.map_sum fun i j=> x i j • basis j]; refine Finset.sum_eq_zero (M:=G.Color) ?_; intro i _; rw [T.map_smul_univ]; have he: T (fun j=> basis (i j))=0:=by ext1 a; exact congr_fun hp ((b,i),a)
    rw [he,smul_zero]
lemma fangRank : LinearMap.ker (pierce G n)=LinearMap.range gaugeJet:=by
    ext A; change pierce G n A=0 ↔ _; constructor
    · intro h; have he:=closedCurl A; let v:=takeCurl A; have hv : v∈ Maxwell.onShell G.Color n.succ:=by
         refine ⟨he,fun i x=>?_⟩; unfold v; rw [← flame_eq,sparks h]; exact smul_zero _
      let P : Shell G n.succ:=⟨v,hv⟩; exact ⟨P,Maxwell.potential.injective (Subtype.ext (match_leg P))⟩
    rintro ⟨v,rfl⟩; ext1 i; let A:=gaugeJet v; suffices h:flame A i.1.1=0 by change flame A _ _ _=_; rw [h];rfl
    apply Tensor.ext_diag
    · intro x s; unfold flame; simp only [_root_.sum_apply, freeze_sym _ ((closedCurl A).coeffSym _ _) _ x s]
    · intro x s;rfl
    ext1 x; apply smul_right_injective G.Color (show ((n+1:ℕ):ℝ)≠0 by positivity); change ((n+1:ℕ):ℝ) • Tensor.diagonal _ _=_; rw [flame_eq,show takeCurl A=_ from match_leg v]; exact (v.property.2 i.1.1 x).trans (smul_zero _).symm
-- rank 1 (engineering 2)
lemma orchardRank : LinearMap.range (gaugeJet (G:=G) (j:=0))=⊤:=by
   ext A; refine ⟨fun _=>Set.mem_univ _,fun _=>?_⟩; let v:= takeCurl A
   have he(Q:Tensor.T E4 G.Color 0)(x:E4)(a:Axis):grad a (Tensor.diagonal Q) x=0:=by rw [show Tensor.diagonal Q=fun _=> Tensor.diagonal Q 0 from funext fun x=>congr_arg Q (Subsingleton.elim ..)]; simp [grad,Analysis.D]
   have h: v∈ Maxwell.onShell G.Color 0:= ⟨closedCurl A,fun i x=>by simp_rw [he];simp⟩; let t: Shell G 0:= ⟨v,h⟩; exact ⟨t,Maxwell.potential.injective (Subtype.ext (match_leg t))⟩
-- Fang dual range
lemma scope_factor {E V:Type*} [AddCommGroup E][Module ℝ E][AddCommGroup V][Module ℝ V] (A:E→ₗ[ℝ] V) (B:E→ₗ[ℝ]ℝ) (h:LinearMap.ker A≤LinearMap.ker B):∃ f:V→ₗ[ℝ]ℝ,B=f ∘ₗ A:=by
   let H:= A.quotKerEquivRange; let g:= Submodule.liftQ (LinearMap.ker A) B h; let T:= LinearMap.range A; let Y:= g ∘ₗ H.symm.toLinearMap; refine ⟨Y ∘ₗ T.subtype.leftInverse,?_⟩; apply LinearMap.ext;intro i
   let v:=A.rangeRestrict i; change B i=g (H.symm (T.subtype.leftInverse (T.subtype v))); rw [LinearMap.leftInverse_apply_of_inj T.ker_subtype, ← show H ((LinearMap.ker A).mkQ i)=v from Subtype.ext (A.quotKerEquivRange_apply_mk i) ,H.symm_apply_apply]; rfl
lemma sharpen (p:TLim G (n+1)→ₗ[ℝ]ℝ) (hp:LinearMap.range gaugeJet≤LinearMap.ker p):∃ f,p=f ∘ₗ (pierce G n):= scope_factor _ _ (fangRank.le.trans hp)
end Script
end YM.OPE.Flume
