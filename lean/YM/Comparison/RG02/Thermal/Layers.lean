import YM.Comparison.RG02.Thermal.Payment
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Thermal
open Function Filter Finset MeasureTheory
open YM.Marker YM.Multi Order Assembly Actual YM.Lattice YM.Tree
open YM.Precision YM.Next.SectorChange

open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff ENNReal
variable {G : Gauge} {V : Type} [DecidableEq V] {R : Census V}
variable {I : Type} [Fintype I] [DecidableEq I]
local notation "Λ" => I→ℝ
open Affinity Gaussian Bulk RG Wilson Exterior YM.Work.F05
variable {c f : Side} {S : StepData c f} {P : PathData G} {p : Clip} {O : ChartRatio G}
namespace Layers
variable (K : Kernel S p P O) (F : Forest S.ratio) (t : S.Choices) (W : Colors R G f) (hW : W.Standard)
local notation "I'"=> Precision.Key F G
local notation "X"=> fieldDir G c 1
local notation "Λ'"=> Precision.Key F G→ℝ
local notation "Z"=> House X I'
local notation "E"=> X × (Precision.Key F G →ℝ)
local notation "T"=> Fix.vibe K F t
local notation "Aϑ"=> Pull.blown K F t T W
local notation "Q"=>Payment.cover K F t
local notation "B"=>Payment.heat K F t
local notation "C"=>Payment.supplement K F t W
def base (x:X) := tested F t p P x (K.b F x)
local notation "heatX"=> Precision.thermal F t p P (K.b F) O

include hW in
set_option maxHeartbeats 400000 in
lemma pure (n:ℕ) (hn : n≤2) (x : E) : Assembly.jet Aϑ (2+n) (1,x)=Assembly.jet Q (2+n) x+Assembly.jet B n x := by
   let A : Z→L[ℝ] (X × (Precision.Key F G→ℝ)):= ContinuousLinearMap.snd ..; let L: Z→L[ℝ]ℝ:=ContinuousLinearMap.fst ..
   let h : Z→ℝ:= fun x=> L x ^ 2 * (B ∘ A) x
   have he:= Payment.cover_service K F t
   have hz:= Payment.heat_service K F t
   have hy : Aϑ= Q ∘ A + h + C := funext (Payment.summarizes K F t W)
   have hd : ContDiffAt ℝ ω (Q ∘ A) 0 := he.comp (f:=A) _ A.contDiff.contDiffAt
   have hu : ContDiffAt ℝ ω (B ∘ A) 0 := hz.comp (f:=A) _ A.contDiff.contDiffAt
   have hh : ContDiffAt ℝ ω h 0:=(L.contDiff.contDiffAt.pow _).mul hu
   have hs : GradeAt 5 C:= Payment.remains K F t W hW
   have hf {f g:Z→ℝ} (hf : ContDiffAt ℝ ω f 0) (hg : ContDiffAt ℝ ω g 0) : Assembly.jet (f+g) (2+n) (1,x)=Assembly.jet f (2+n) (1,x)+Assembly.jet g (2+n) (1,x) := by unfold Assembly.jet; rw [iteratedFDeriv_add_apply (hf.of_le le_top) (hg.of_le le_top),_root_.add_apply,smul_add]
   rw [hy,hf (f:=Q ∘ A + h) (hd.add hh) hs.smooth,hf hd hh,hs.jet_z _ (i:=2+n) (by omega), add_zero]; unfold h; rw [jet_continuous_right A (he.of_le le_top), Clipper.exponent hu, jet_continuous_right A (hz.of_le le_top),show L (1,x)=1 from rfl,one_pow,one_mul]; rfl
lemma stationary (x:X) (n:ℕ): Assembly.jet Q n (x,0)=Assembly.jet (base K F t) n x :=
   (jet_continuous_right (L:=ContinuousLinearMap.inl ℝ X (Λ')) ((Payment.cover_service K F t).of_le le_top) x).symm.trans (congrArg (fun p:X→ℝ=> Assembly.jet p n x) (funext (Payment.center K F t)))

lemma thermal_fee (x:X) (n:ℕ) (hn : n≠0) : Assembly.jet B n (x,0)=Assembly.jet heatX n x := by
   let p := ContinuousLinearMap.inl ℝ X (Λ'); let q:X→ℝ:= B ∘ p
   have hf : ∃ c:ℝ, heatX =ᶠ[𝓝 0] q+fun _=>c := ⟨_,(Payment.thermal_amount K F t).mono fun y hy=>eq_add_of_sub_eq hy.symm⟩
   obtain ⟨c,he⟩:=hf
   have ht := Payment.heat_service K F t
   have hm : ContDiffAt ℝ ω q 0 := ht.comp (f:=p) _ p.contDiff.contDiffAt
   change Assembly.jet B n (p x)=_
   rw [← jet_continuous_right p (ht.of_le le_top)]; unfold Assembly.jet; rw [(he.iteratedFDeriv ℝ n).eq_of_nhds,iteratedFDeriv_add_apply (hm.of_le le_top) contDiffAt_const, iteratedFDeriv_const_of_ne hn,Pi.zero_apply, add_zero]

-- geothermal identification with determinant taken *after* whitening.
-- fees at orders 1 and 2-in-g. rank-three odd, drops in expectation.
variable (x:fieldDir G c 1) (v:Precision.Key F G→ℝ)
def forecast (n:ℕ) : ℝ:= Assembly.jet (base K F t) (2+n) x + Assembly.jet heatX n x
include hW
set_option maxHeartbeats 400000 in
lemma first : Assembly.jet Aϑ 3 (1,x,v) = forecast K F t x 1 + Assembly.jet Aϑ 3 (1,0,v):= by
   have h := Clipper.budget3 _ _ (Payment.cover_service K F t) (Payment.plumb K F t v) (Payment.shifted K F t v) 1 x
   have h₁ := Clipper.plane_first (f:=B) v x
   have hp y : Assembly.jet Aϑ 3 ((1:ℝ),y)=Assembly.jet Q 3 y+Assembly.jet B 1 y := Layers.pure K F t W hW 1 (by omega) y
   rw [one_smul,one_pow,one_mul] at h
   -- replace before rewriting B
   rw [hp (x,v),hp (0,v),h,h₁]; unfold forecast
   rw [stationary K F t x 3, thermal_fee K F t x 1 (by decide)]; change _ = (Assembly.jet _ 3 x+_) +_; abel
lemma blanker (v : Λ') : Assembly.jet Aϑ 3 (1,0,-v)= -(Assembly.jet Aϑ 3 (1,0,v)) := by
   have hp y : Assembly.jet Aϑ 3 ((1:ℝ),y)=Assembly.jet Q 3 y+Assembly.jet B 1 y := Layers.pure K F t W hW 1 (by decide) y
   rw [hp (0,v),hp (0,-v), show ((0:X),-v)=(-1:ℝ)•((0:X),v) from Prod.ext (by simp) (by simp), Clipper.weight,Clipper.weight]; simp only [show (-1:ℝ)^3=(-1:ℝ) by norm_num,pow_one,neg_one_smul,neg_add]
set_option maxHeartbeats 400000 in
lemma second : Assembly.jet Aϑ 4 (1,x,v)+Assembly.jet Aϑ 4 (1,x,-v)=2*forecast K F t x 2+(Assembly.jet Aϑ 4 (1,0,v)+ Assembly.jet Aϑ 4 (1,0,-v)) := by
   have hp y: Assembly.jet Aϑ 4 ((1:ℝ),y)=Assembly.jet Q 4 y+Assembly.jet B 2 y := Layers.pure K F t W hW 2 (by decide) y
   have hv := Clipper.mean2 B v (Payment.heat_service K F t) x
   have ht := Clipper.mean4 Q v (Payment.cover_service K F t) (Payment.shifted K F t v) x
   rw [hp (x,v),hp (x,-v), hp (0,v), hp (0,-v),show ((0:X),-v)=(-1:ℝ)•((0:X),v) from Prod.ext (by simp) (by simp),Clipper.weight,Clipper.weight]
   unfold forecast; change _= 2*(Assembly.jet _ 4 x+Assembly.jet _ 2 x)+_
   rw [← stationary,← thermal_fee]; swap; norm_num
   -- weight simplify
   simp only [show (-1:ℝ)^4=1 by norm_num, show (-1:ℝ)^2=1 by norm_num,one_smul]
   linarith only [hv,ht]
end Layers
end YM.Comparison.RG02.Thermal
