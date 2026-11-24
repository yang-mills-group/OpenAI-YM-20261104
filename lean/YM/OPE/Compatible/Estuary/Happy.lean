import YM.OPE.Compatible.Lintel.Paine
/-! # Rooted stencil. Constructs costed gradient shift.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Work.F05 Votive Tree
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J Y Z:Type}{G:Gauge}{n m c f:Side}{S:StepData c f}{p q:Clip}{R T:PathData G} {P:Patch}{K:KernelChoices}{V:ChartRatio G} {i j t r:ℕ} {s s' u α T₁ T₂ b b' d U ℓ:ℝ}
namespace Script
open Page Virgin FreeResolvent.Draw
local notation "O"=> TypeFace 0
local notation "X"=> TypeFace 1
def myth (L:Side): Ratio 1 L:=⟨L,(one_mul L.val).symm⟩
lemma myth_res (x: Site n):(myth n).residue x=x:=by rw [← wrap_lift x]; rw [Ratio.residue_wrap]; rfl
def glen (L:Side)(h:Odd L.val)(x:Site L):=(forest (myth L) h).hike x
lemma hike_lines (g:Ratio c f)(h:Odd g.count.val)(x:Site f): (forest g h).hike x=glen g.count h (g.residue x):=by
    let p:= g.count; let T:= forest (myth p) h
    induction x using Forest.hike.induct (forest g h) with
    | case2 i hi =>
       have hr : ¬ leaf (myth p) (g.residue i):= fun hh=> hi ((leaves g _).mpr ((leaves ..).1 hh|> fun h=>myth_res (g.residue i) ▸ h)); unfold glen; rw [Forest.hike,dif_neg hi, Forest.hike,dif_neg hr]
    | case1 i hi ih=>
       have hf:= (leaves g i).mp hi; let v:Site p:=g.residue i; have hg: leaf (myth p) v:= (leaves ..).mpr (by rw [myth_res]; exact hf); let b:=riseA v
       rw [Forest.hike,dif_pos hi, ih]; unfold glen; change b :: T.hike (g.residue (i+b.vec))=T.hike v; conv_rhs => rw [Forest.hike,dif_pos hg]
       have hX : T.up v=b:=by change riseA ((myth p).residue v)=b; rw [myth_res]; rfl
       have hh: g.residue (i+b.vec)=v+b.vec:=by rw [map_add,← wrap_vec,Ratio.residue_wrap,wrap_vec]
       rw [hX,hh]
-- combine fixRoot
abbrev groper (L:Side) (h:Odd L.val):Row (Co L O) (Co L X):= fun x=> path L (lift x.1) (glen L h x.1)
def bow (P:Patch):Row (Co P.L O) (Co P.L X):=minusRows (groper P.L P.odd_side) (fun _=>rootRow P vac)
lemma bow_price (P:Patch):Whole (bow P):=by
    obtain ⟨M,hM,hK⟩:=ready_rootRow P 1; obtain ⟨N,hN,hP⟩ := ready_strip (R:=groper P.L P.odd_side) (fun i=> path_ready _ _) 1
    change Whole (_-_); refine (show Whole (groper P.L P.odd_side) from ⟨1,N,one_pos,hP⟩).minus ⟨1,M,one_pos,fun i j=> hK vac j⟩
def straighter (P:Patch)(A:Cross P.L X X):Cross P.L O X:=composeRows (bow P) A
variable (S)
lemma feeling {x:Body 0 f}(a:Body 1 f):
    (bow S.patch).acts c (splitCo S.ratio O x) (splitCo S.ratio X a)= integralLink x.1 ((forest S.ratio S.patch.odd_side).hike x.1) (Pi.single a 1)-(fixRoot S) (S.ratio.parent x.1,vac) a:=by
      rw [hike_lines]; let R:=S.ratio; obtain ⟨M,hM,hH⟩:=ready_rootRow S.patch 1; obtain ⟨N,hN,hP⟩ := ready_strip (R:=groper S.patch.L S.patch.odd_side) (fun i=> path_ready _ _) 1
      let V:= groper S.patch.L S.patch.odd_side; let Y:Row (Co S.patch.L O) (Co S.patch.L X):=fun _=> rootRow S.patch vac; have hy:Whole Y:=⟨1,M,one_pos,fun i j=> hH vac j⟩
      erw [show Row.acts (bow S.patch) c=_ from (Whole.less (A:=V) (B:=Y) ⟨1,N,one_pos,hP⟩ hy c),block_root]; change V.acts c (splitCo R O x) _-Y.acts c _ _=_; erw [split_co R x]; apply congr_arg₂; swap; · rfl
      let y:=R.parent x.1; let z:=lift (R.residue x.1); have he : wrap f z+R.embed y=x.1:= (add_comm ..).trans (R.unpack_at x.1); have hh:=spot_path (g:=R) y a z (glen R.count S.patch.odd_side (R.residue x.1)); rw [he] at hh; exact hh
lemma straighten_acts (A:Cross S.ratio.count X X)(h:Whole A): installed S.ratio (straighter S.patch A)= straighten S (forest S.ratio S.patch.odd_side) (installed S.ratio A):=by
    apply Matrix.ext_of_mulVec_single; intro i; let P : Body 1 c→ℝ:=Pi.single i 1; let v:= installed S.ratio A; let Q:= (forest S.ratio S.patch.odd_side); let y:=v*ᵥP
    ext1 j; erw [books]; change (installed _ _ *ᵥ P) _ = integralLink j.1 (Q.hike j.1) y-(_ *ᵥ _) _
    let B:= (bow S.patch).acts c; let T: Matrix _ _ ℝ:=B.submatrix (splitCo S.ratio O) (splitCo S.ratio X)
    have hh: installed S.ratio (straighter S.patch A)= T*v:=by
       unfold installed; erw [(bow_price S.patch).acts h c]; unfold T v B installed; erw [Matrix.submatrix_mul_equiv]; rfl -- orientation
    rw [hh, ← Matrix.mulVec_mulVec]
    let L:= integralLink j.1 (Q.hike j.1); let U:= fixRoot S; let V:= (S.ratio.parent j.1,vac); change ∑ i: Body 1 f, T j i *y i=L y-∑ i:Body 1 f,U V i*y i; have hv: L y=∑ i:Body 1 f,L (Pi.single i 1)*y i:=by
       rw [show L y= _ from congr_arg L (show y=∑ i,y i • Pi.single i 1 from funext (fun i=>by simp [Finset.sum_apply,Pi.single_apply,_root_.mul_ite])),map_sum]; exact sum_congr rfl fun i _=> by rw [map_smul];exact mul_comm ..
    rw [hv,← sum_sub_distrib]; exact sum_congr rfl fun i _=>by rw [show T j i=_ from feeling S (x:=j) i,sub_mul]
end Script
end YM.OPE.Flume
