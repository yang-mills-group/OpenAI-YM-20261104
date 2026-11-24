import YM.AllOrder.Fire.Dir
/-!
# Kernel of finite `Hot`: covariance-weighted connected calculus
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Fire
open Function Finset Laplace.SigmaP PositionX.Jet PertExtension PertExtension.Series PositionX.Gauss Radial MeasureTheory Response Module
open scoped Topology ContDiff BigOperators Classical
variable {Y X:Type} [NormedAddCommGroup X][NormedSpace ℝ X] [NormedAddCommGroup Y][NormedSpace ℝ Y]
local notation "Ω"=>X×Y
local notation "T"=>ℝ×(X×Y)
open GaussianScore
variable [FiniteDimensional ℝ X][FiniteDimensional ℝ Y] (A: Law Y) -- later instance attr
variable {a b:Ω} {f:X×Y→ℝ}
lemma point_price (p:T) (h:Plausible f)(r:Ω) (z:Y): diff' (((0:ℝ),r),0) (blow f) (p,z) = diff' r f (wardrobe (p,z)) := by
 obtain ⟨t,x,w⟩:=p; obtain ⟨a,b⟩:=r
 rw [licensed (blown h|>.smooth.contDiffAt), licensed h.smooth.contDiffAt]; congr 1; ext1 i; simp [blow,wardrobe,add_assoc,add_comm (t•z)]
lemma smooth_local (p:T)(h:Plausible f): Plausible (fun y:Y=> f (wardrobe (p,y))) := localP (blown h) p
lemma clock_price (p:T)(z:Y)(h:Plausible f): diff' ((((1:ℝ),(0:Ω))), 0) (blow f) (p,z)= diff' ((0:X),z) f (wardrobe (p,z)):= by
   obtain ⟨t,x,w⟩:=p; rw [licensed ((blown h).smooth.contDiffAt), licensed h.smooth.contDiffAt]; congr! 1; ext1 i; simp [blow,wardrobe, add_smul,add_assoc]
lemma flipped_price (p:T)(x y : Y)(h:Plausible f): diff' x (fun y:Y=> f (wardrobe (p,y))) y = p.1* diff' ((0:X),x) f (wardrobe (p,y)):= by
   obtain ⟨t,u,v⟩:=p
   have he :t * diff' ((0:X),x) f (wardrobe (((t,u,v)),y)) = diff' ((0:X), t • x) f (wardrobe (((t,u,v)),y)):= by unfold diff'; rw [show ((0:X),t•x)=t • ((0:X),x) by simp,map_smul]; rfl
   rw [show (t,u,v).1=t from rfl,he,licensed (smooth_local _ h|>.smooth.contDiffAt),licensed h.smooth.contDiffAt]; congr! 1; ext1 i; simp [wardrobe,smul_add, smul_comm t i,add_assoc]

variable {ι:Type} [Fintype ι]
variable (B:Basis ι ℝ Y)
-- embed in ambient X×Y; keep two functions to curry.
abbrev delayX (x:X)(y:Y):Ω:= (x,y)
abbrev vec (i:ι) : Ω:= ( (0:X),B i)
abbrev Inv (i:ι) : Y := A.inverse (B.coord i)
omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] in
lemma spread [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]  (_h:Plausible f)(p:T)(y:Y): diff' ((0:X),y) f (wardrobe (p,y)) = ∑ i,(B.coord i y)*diff' (vec (X:=X) B i) f (wardrobe (p,y)) := by
   let w:= fderiv ℝ f (wardrobe (p,y)); let L : Y→L[ℝ]ℝ:= w ∘L ContinuousLinearMap.inr ℝ X Y; change L y=∑ i,(B.coord i y)*L _
   conv_lhs=>rhs;rw [← B.sum_equivFun y]
   rw [map_sum]; apply Finset.sum_congr rfl; intro i _;rw [_root_.map_smul];rfl
omit [Fintype ι] in
lemma invert_c [Fintype ι]  (i j :ι): B.coord j (Inv A B i)=B.coord i (Inv A B j) := by
  rw [←A.applies (B.coord i),← A.applies (B.coord j)]; exact A.turns .. |>.symm -- Inv unexpand? check
variable [MeasurableSpace Y][BorelSpace Y]
-- need move variable μ after. 
variable (μ: Measure Y) [μ.IsAddHaarMeasure]
lemma sequential (p:T) (h:Plausible f)(r:Ω): diff' ((0:ℝ),r) (Hot A μ f) p= Hot A μ (diff' r f) p:= by
 unfold Hot; rw [diff_bound A μ (blown h)]; exact congr_arg (A.average μ) (funext fun _=> point_price _ h ..)
def infinity (f:Ω→ℝ) : Ω→ℝ := ∑ i : ι, diff' ((0:X),Inv A B i) (diff' (vec B i) f)
-- time lifted version
abbrev foot {D:Type}[NormedAddCommGroup D](y:D) := ((0:ℝ),y)
def lap (f:T→ℝ):T→ℝ:= ∑ i:ι,diff' (foot ((0:X), Inv A B i)) (diff' (foot (vec B i)) f)

lemma lightning (p:T) (h:Plausible f):diff' ((1:ℝ),(0:Ω)) (Hot A μ f) p=p.1* lap A B (Hot A μ f) p := by
    let Q i:= diff' (vec (X:=X) B i) f
    let F i (z:Y):= Q i (wardrobe (p,z)); have hf i:=h.ds (vec (X:=X) B i); have hF i:= smooth_local p (hf i)
    rw [Hot,diff_bound A μ (blown h)]; simp_rw [clock_price p _ h,spread B h]
    let L i:= (B.coord i); have he i : Plausible (F i):= hF i
    have ht(p:T)(g:Ω)(f:Ω→ℝ)(h:Plausible f):diff' (foot g) (Hot A μ f) p=A.average μ (fun z=> diff' g f (wardrobe (p,z))):= sequential A μ p h _
    have hv (i): diff' (Inv A B i) (F i)= p.1 • (fun y:Y=> diff' ((0:X),Inv A B i) (Q i) (wardrobe (p,y))) := funext fun y=> flipped_price p _ _ (hf i)
    have hN i : A.average μ ((F i)*L i)= p.1* diff' (foot ((0:X),Inv A B i)) (diff' (foot (vec (X:=X) B i)) (Hot A μ f)) p:= by
       rw [show diff' (foot (vec (X:=X) B i)) (Hot A μ f)=_ from funext fun v=> sequential A μ v h (vec (X:=X) B i), ht _ _ _ (hf i)]
       change A.average μ _= p.1*A.average μ (fun z=> diff' ((0:X),Inv A B i) (Q i) (wardrobe (p,z)))
       rw [← average_scale, ← hv i, byParts A μ (he i) (Inv A B i), Inv, A.applies]
    change (A.average μ (fun y:Y=>∑ i,L i y*F i y))=_ * lap _ _ (Hot A μ f) p
    unfold lap; rw [Finset.sum_apply, Finset.mul_sum]; simp_rw [← hN]
    change A.average μ (fun y:Y=>∑ i,L i y*F i y)=∑ i,A.average μ _; rw [show (fun y:Y=>∑ i,L i y*F i y)=∑ i,F i* (L i : Y→ℝ) from (funext fun _=>by simp [Finset.sum_apply,mul_comm])]; exact average_sum A μ (fun i _=> (he i).mul (Plausible.line _))
end YM.AllOrder.Fire
