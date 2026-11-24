import YM.Comparison.RG02.Assembly.Clipper
import YM.Push.LOOP_COEFFICIENT.Paths.Calculus
import YM.PertExtension.PTBills
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Assembly.Clipper
open Function Filter Finset MeasureTheory
open YM.Marker YM.Multi Order Assembly Actual YM.Lattice YM.Tree
open YM.Precision YM.Next.SectorChange
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff ENNReal
variable {G : Gauge} {V : Type} [DecidableEq V] {R : Census V}
variable {I : Type} [Fintype I] [DecidableEq I]
local notation "Λ" => I→ℝ
open YM.Tensor YM.Analysis PertExtension.Series PertExtension.Series.Tested
variable {E X Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

section scalar
variable [FiniteDimensional ℝ E] {f:E→ℝ} (hf : ContDiffAt ℝ ω f 0)
include hf
lemma exponent (L:E→L[ℝ]ℝ) (x:E) (n k:ℕ) : Assembly.jet (fun y=> L y ^ n * f y) (n+k) x=(L x)^n*Assembly.jet f k x:= by
   let F y := L y^n*f y
   have he := (Aspiration.single (R:=ℝ) (L x^n) n).prod (directions (hf.of_le le_top) x)
   have ht : (fun t:ℝ=> (t^n • L x^n)*f (t • x))=fun t:ℝ=> F (t • x):=funext fun t=>by unfold F; rw [map_smul]; simp [smul_eq_mul,mul_pow]
   change Aspiration (fun t:ℝ=> (t^n • L x^n)*f (t • x)) _ at he; rw [ht] at he
   have hp:= congr_fun ((directions (f:=F) (((L.contDiff.contDiffAt.pow _).mul hf).of_le le_top) x).unique he) (n+k)
   change Radial.jet F (n+k) x= _
   rw [hp]; unfold Tested.conv term; rw [PowerSeries.coeff_mul,sum_eq_single (n,k)]
   · simp only [PowerSeries.coeff_mk, if_true]; rfl
   · intro i hi hk; rw [HasAntidiagonal.mem_antidiagonal] at hi; have he:i.1 ≠ n:=by rintro H; exact hk (Prod.ext H (by omega))
     simp [he,PowerSeries.coeff_mk]
   simp
end scalar
section xz
-- Constant-in-vertical conditions on derivative arrays, authentic neighborhoods in X.
variable (f : X×E→ℝ) (v:E)
def cylinder (k : ℕ) (b:ℝ) := (fun x : X=> dz k (0,v) f (x,0)) =ᶠ[𝓝 0] fun _=> b
variable (hf : ContDiffAt ℝ ω f 0)
include hf
lemma arrived (k : ℕ) (x : X) {b:ℝ} (ht : cylinder f v k b) (n:ℕ) (hn:n≠0) : Assembly.jet (dz k (0,v) f) n (x,0)=0 := by
   let L: X→L[ℝ] X×E := ContinuousLinearMap.inl ℝ _ _
   let g := dz k (0,v) f
   change Assembly.jet g _ (L x)=_
   rw [← jet_continuous_right L ((dz_known hf _ _).of_le le_top)]; unfold Assembly.jet
   rw [((show g ∘ L =ᶠ[𝓝 0] _ from ht).iteratedFDeriv ℝ n).eq_of_nhds,iteratedFDeriv_const_of_ne hn]; simp

local notation "x_v"=> ((0:X), v)
lemma split_vert (n : ℕ) (z:ℝ) (x:X) : Assembly.jet f n (x,z • v)=∑ i∈range (n+1), z^i/(i.factorial:ℝ)*Assembly.jet (dz i x_v f) (n-i) (x,0):= by
   rw [show (x,z • v)=(x,(0:E))+z • x_v from Prod.ext (by simp) (by simp)]; exact Clipper.split hf (x,0) x_v z n

-- small-orders; odd part dereference; signs unchanged. Continuation proofs use homogeneity.
omit hf in
lemma plane_first (x:X) : Assembly.jet f 1 (x,v)=Assembly.jet f 1 (x,0) + Assembly.jet f 1 (0,v):= by
   have hf0 : ∀ v, Assembly.jet f 1 v=fderiv ℝ f 0 v:= fun u=> by simp
   simp_rw [hf0]; rw [← map_add]; congr <;> simp
lemma budget3 {b c:ℝ} (h1 : cylinder f v 1 b) (h2 : cylinder f v 2 c) (z:ℝ) (x:X):
    Assembly.jet f 3 (x,z • v)=Assembly.jet f 3 (x,0) + z^3 * Assembly.jet f 3 (0,v):= by
   have h(y:X)(z:ℝ) := split_vert f v hf 3 z y
   have e(y:X)(z:ℝ): Assembly.jet f 3 (y,z • v)=Assembly.jet f 3 (y,0)+ z^3/(3:ℕ).factorial* dz 3 x_v f 0 := by
      rw [h]; simp only [sum_range_succ,sum_range_zero,zero_add,Nat.reduceSub, show dz 0 x_v f=f from rfl,Assembly.jet_zero]
      norm_num only [ arrived f v hf 1 y h1 _ (by decide : 2≠0), arrived f v hf 2 y h2 1 (by decide),Nat.factorial,mul_zero,add_zero,pow_one,div_one,one_mul,one_div,zero_add,pow_zero]
   have hh:=e 0 1; rw [one_smul,show ((0:X),(0:E))=0 from rfl, empty 3 (by decide) f] at hh
   rw [hh,e]; ring

-- even z-reflection: rank determined by centered fields separately
lemma mean2 (x:X): (Assembly.jet f 2 (x,v)+Assembly.jet f 2 (x,-v)) = 2*(Assembly.jet f 2 (x,0)+Assembly.jet f 2 (0,v)):= by
   have h(y:X)(z:ℝ) := split_vert f v hf 2 z y
   have he(y:X): Assembly.jet f 2 (y,v)+Assembly.jet f 2 (y,-v)=2*(Assembly.jet f 2 (y,0))+ dz 2 x_v f 0 :=by
       have hp:=h y 1; have hq:=h y (-1)
       simp only [sum_range_succ,sum_range_zero,zero_add,Nat.reduceSub, show dz 0 x_v f=f from rfl,Assembly.jet_zero,one_smul,neg_one_smul] at hp hq
       norm_num only [Nat.factorial,one_mul,one_div] at hp hq; linarith only [hp,hq]
   have hq:=he 0; rw [show ((0:X),(0:E))=0 from rfl, empty 2 (by decide), show ((0:X),-v)=(-1:ℝ)•x_v from Prod.ext (by simp) (by simp),weight, show (-1:ℝ)^2=1 by norm_num,one_smul] at hq
   linarith only [he x,hq]
lemma mean4 {b:ℝ} (ha : cylinder f v 2 b) (x:X): (Assembly.jet f 4 (x,v)+Assembly.jet f 4 (x,-v)) = 2*(Assembly.jet f 4 (x,0)+Assembly.jet f 4 (0,v)):= by
   have h(y:X)(z:ℝ): Assembly.jet f 4 (y,z•v)=Assembly.jet f 4 (y,0) + z*Assembly.jet (dz 1 x_v f) 3 (y,0)+ z^3/6 * Assembly.jet (dz 3 x_v f) 1 (y,0) + z^4 /24 * dz 4 x_v f 0 := by
       rw [split_vert f v hf]; simp only [sum_range_succ,sum_range_zero,zero_add,Nat.reduceSub, show dz 0 x_v f=f from rfl,Assembly.jet_zero]
       norm_num only [ arrived f v hf 2 y ha 2 (by decide),Nat.factorial,mul_zero,add_zero,pow_one,div_one,one_mul,one_div,zero_add,pow_zero]
   have hp (y:X): (Assembly.jet f 4 (y,v)+Assembly.jet f 4 (y,-v)) = 2* Assembly.jet f 4 (y,0)+ (1/12:ℝ)* dz 4 x_v f 0 := by
       have he:=h y 1; have hk:=h y (-1); norm_num only [one_smul,neg_one_smul] at he hk; linarith only [he,hk]
   have he:=hp 0; rw [show ((0:X),(0:E))=0 from rfl, empty 4 (by decide), show ((0:X),-v)=(-1:ℝ)•x_v from Prod.ext (by simp) (by simp),weight, show (-1:ℝ)^4=1 by norm_num,one_smul] at he
   linarith only [hp x,he]

-- cylinders from genuine partial-derivatives, then erased in mixed tensors.
lemma vertical_one : ∀ᶠ x in 𝓝 (0:X), dz 1 x_v f (x,0)=fderiv ℝ (fun y=>f (x,y)) 0 v := by
   have hu : Tendsto (fun x:X=> (x,(0:E))) (𝓝 0) (𝓝 0) := tendsto_id.prodMk_nhds tendsto_const_nhds
   filter_upwards [hu.eventually (hf.eventually (by simp))] with x hx
   let A := ContinuousLinearMap.inr ℝ X E
   let g := fun y=> (x,(0:E))+ A y
   have hg : HasFDerivAt g A 0 := (A.hasFDerivAt).const_add _
   rw [show (fun y:E=>f (x,y))=f ∘ g from funext fun y=> congrArg f (by simp [g,A])]
   change fderiv ℝ f _ _=_
   rw [fderiv_comp _ (by simpa [g,A] using! hx.differentiableAt (by simp : (ω:WithTop ℕ∞)≠0)) hg.differentiableAt, hg.fderiv,ContinuousLinearMap.comp_apply,show g 0=(x,0) by simp [g]]; rfl
lemma vertical_two : ∀ᶠ x in 𝓝 (0:X), dz 2 x_v f (x,0)=Work.F05.bend (fun y=>f (x,y)) 0 v v := by
   have hu : Tendsto (fun x:X=> (x,(0:E))) (𝓝 0) (𝓝 0) := tendsto_id.prodMk_nhds tendsto_const_nhds
   filter_upwards [hu.eventually (hf.eventually (by simp))] with x hx
   let L:=ContinuousLinearMap.inr ℝ X E
   let y:=(x,(0:E))
   have he:= (Push.Loops.Paths.iterated_affine (f:=f) L y 0 (show ContDiffAt ℝ ω f (y+L 0) by rw [L.map_zero,_root_.add_zero]; exact hx) ![v,v])
   have H : (fun v'=> f (x,v'))=fun z:E=>f (y+L z):= funext fun b=>congrArg f (by simp [L,y])
   rw [Work.F05.bend_apply,H,he,L.map_zero,add_zero,show (fun i:Fin 2=> L (![v,v] i))= Fin.cons x_v (Fin.cons x_v Matrix.vecEmpty) by funext i; fin_cases i <;> rfl, Analysis.cons_inner (j:=1) (hx.of_le le_top), iteratedFDeriv_one_apply]; rfl
end xz
end YM.Comparison.RG02.Assembly.Clipper
