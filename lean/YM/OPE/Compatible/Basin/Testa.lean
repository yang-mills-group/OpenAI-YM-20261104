import YM.OPE.Compatible.Basin.Canter
/-!
# Row relabel tuning. Tests. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Tree Exterior Stationary Woody
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J Q E:Type*} {G:Gauge}{n m l c f:Side}{S:StepData c f} {g:Ratio c f} {r:ℕ}
namespace Script
open Virgin Page Work.F05
lemma folds (t:S.Choices){H:Forest S.ratio}{p:Clip}{R:PathData G}{g:Bid.Dir G c→AxisChart G H}(h:Critical H p R g)(x:Bid.Dir G c): (fieldT (cabin g) x)=(x, fderiv ℝ (cabin g) 0 x):=by
    have ht:=viewer t h; let A:= ContinuousLinearMap.snd ℝ (Bid.Dir G c) (AxisChart G H); let Y:=cabin g; have hp:fderiv ℝ Y 0=A∘L fderiv ℝ (viewS Y) 0:= by rw [show fderiv ℝ Y 0=fderiv ℝ (A ∘ viewS Y) 0 from rfl,fderiv_comp _ A.differentiableAt (ht.hl.differentiableAt (by simp)),A.fderiv]
    exact Prod.ext (ht.rim x) (DFunLike.congr_fun hp x).symm
section mean
variable {P:Patch}{K:KernelChoices}
def sifter (C:Medal P G K r)(v: Train r): Row (Tile G P.L) (Shade G):= toLeft (unitRow _) (braidRow id (mus G) (C.rowNet v))
lemma siftPay (C:Medal P G K r)(v:Train r): Whole (sifter C v):=toLeft_cash _ _ ⟨1,1,one_pos,fun i j=> Work.F08.strip_unit i j⟩ (braidP _ _ _ (C.row_p v))
variable (C:Medal S.patch G S.kernel r)(v:Train r)(hr:Odd S.ratio.count.val)
local notation "W"=> C.rowNet v
local notation "F"=>forest S.ratio hr
local notation "T"=>squad S.ratio hr G
lemma tapWorks : ∀ i:Active G F,∀ j:Co c (PAC G 1),(installed S.ratio (C.highCross v)) (plant F i) j=(C.rowNet v).acts c (T i) j:=by
    intro i j; let M:=installed S.ratio (into G S.ratio.count); erw [Medal.highCross, Whole.from_coarse S.ratio (into_good ..) (C.row_p v),Matrix.mul_apply,← (T).sum_comp]
    change (∑ u, M (plant F i) (T u) * (C.rowNet v).acts c (T u) j) = _
    simp_rw [show ∀ u:Active G F, M (plant F i) (T u)=if u=i then 1 else 0 from fun u=>by rw [show M (plant F i) (T u)= insertion (plant (G:=G) F) (plant F i) u from congrFun (congrFun (into_trunks S.ratio hr|>.symm) (plant F i)) u]; simp only [insertion,Matrix.of_apply,(plant_inj F).eq_iff]] -- M unfold
    simp only [ite_mul,zero_mul,one_mul,sum_ite_eq', mem_univ,if_true]
lemma adjust (x: Bid.Dir G c)(j:Tab (Slip G S.patch.L) c):
     ((sifter C v).acts c*ᵥspool G c x) (starJ j)=((C.rowNet v).acts c *ᵥ flatten x) j:=by
       unfold mulVec dotProduct; rw [← (lent G c).sum_comp (g:=fun u=> (C.rowNet v).acts c j u*flatten x u)] -- suspect name
       exact sum_congr rfl (fun _ _=> rfl)
lemma tapView (k:S.Choices){p:Clip}{R:PathData G}{g:Bid.Dir G c→AxisChart G F}{B:Matrix (Body 1 f) (Body 1 c) ℝ}(h:Critical F p R g)(hp:Guessed F B g)(x: Bid.Dir G c)(hm: installed S.ratio (C.highCross v)=tensor G (extracted S F B)): paintV S.ratio hr G (fieldT (cabin g) x)= (sifter C v).acts c*ᵥ(spool G c x):=by
       apply funext; intro i; rcases i with ⟨i,j|j⟩
       · rw [folds k h]; let A:= unitRow (Shade G); change _=(A.acts c).mulVec (spool G c x) (i,j); rw [show A.acts c=1 from acts_unit c]; exact congr_fun (Matrix.one_mulVec (spool G c x)).symm (i,j)
       obtain ⟨u,hu⟩:= (T).surjective (i,j); change paintV S.ratio hr G (fieldT (cabin g) x) (starJ (i,j))= _; rw [folds k h]; change paintV S.ratio hr G _ (starJ (i,j))=((sifter C v).acts c*ᵥ spool G c x) (starJ (i,j));rw [←hu,petalV,adjust C v]; change cash _ (fderiv ℝ (cabin g) 0 x) _=_; rw [plantT k h hp,← hm]; simp_rw [Matrix.mulVec,dotProduct, tapWorks C v hr]; erw [hu]; rfl
end mean
end Script
end YM.OPE.Flume
