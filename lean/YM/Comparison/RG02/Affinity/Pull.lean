import YM.Comparison.RG02.Affinity.Identity
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Affinity
open Function Filter Finset MeasureTheory
open YM.Marker YM.Multi Order Assembly Actual YM.Lattice YM.Tree
open YM.Precision YM.Next.SectorChange
open Matrix
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff ENNReal
variable {G : Gauge} {V : Type} [DecidableEq V] {R : Census V}
variable {I : Type} [Fintype I] [DecidableEq I]
local notation "Λ" => I→ℝ
open Gaussian PertExtension.Series Laplace Bulk RG Wilson Exterior
variable {c f : Side} {P : PathData G} {J : Clip} {V0 : ChartRatio G} {S : StepData c f}
    {W : Colors R G f} (hW : Well W)
namespace Pull
variable (K : Kernel S J P V0) (F : Forest S.ratio) (t : S.Choices)
local notation "I'"=> Precision.Key F G
local notation "X"=> fieldDir G c 1
local notation "E"=> House X I'
local notation "w"=> W.power
local notation "Aϑ"=> geometric K F t W
local notation "fϑ"=> markFn S F W
local notation "Qϑ"=> K.covariance F t
local notation "Ω"=> Bulk.Joint S F (G:=G)


def moved (_g : E) : Ω := (_g.1,_g.2.1,(fderiv ℝ (K.b F) 0) _g.2.1 + tape _g.2.2)
def stands : E →L[ℝ] (Bulk.Joint S F (G:=G)) :=
   ({toFun:=moved K F
     map_add':=fun x y=> by
        apply Prod.ext (by rfl); refine Prod.ext rfl ?_
        change fderiv ℝ (K.b F) 0 (x.2.1+y.2.1) + gaugeCount (x.2.2+y.2.2) =_
        rw [map_add,map_add]; change _ = (fderiv ℝ (K.b F) 0 x.2.1 + gaugeCount x.2.2)+(fderiv ℝ (K.b F) 0 y.2.1+gaugeCount y.2.2)
        abel
     map_smul' := fun u a=> by
        apply Prod.ext (by rfl); refine Prod.ext rfl ?_
        change fderiv ℝ (K.b F) 0 (u • a.2.1) + gaugeCount (u • a.2.2)=u • (fderiv ℝ (K.b F) 0 a.2.1+gaugeCount a.2.2)
        rw [_root_.map_smul,_root_.map_smul,_root_.smul_add] } : House X I' →ₗ[ℝ] (Bulk.Joint S F (G:=G))).toContinuousLinearMap
-- edit above

variable [Fintype V]

lemma locates (x:X) (v:I'→ℝ) : stands K F (season x v)= Bulk.translated K F x v := by rw [Bulk.footing, facing]; rfl

include hW
omit [Fintype V] in
lemma rooted : GradeAt 2 (geometric K F t W) := by
   obtain ⟨hw,_⟩:=geometric_ready K F t W hW
   refine Buy.deuce _ ((stone_smooth K F t).add (fee_starts K F W hW).smooth) hw.base0 ?_
   apply ContinuousLinearMap.ext; intro v; have h:= hw.base1 v; simpa [← Assembly.jet_eq, Assembly.jet, iteratedFDeriv_one_apply] using h
omit [Fintype V] in
lemma ready : Ray Qϑ (Aϑ ∘ stands K F) := by
   have hp:= rooted hW K F t
   refine ⟨hp.coarse (stands K F).contDiff.contDiffAt (stands K F).map_zero, fun x v=> ?_⟩
   have h (v:I'→ℝ) : Assembly.jet (Aϑ ∘ stands K F) 2 (1,x,v)=Assembly.jet Aϑ 2 (translated K F x v) := Eq.trans (jet_continuous_right (stands K F) (hp.smooth.of_le le_top) (1,x,v)) (by rw [← locates K F x v]; simp only [facing])
   rw [h v,h 0, Bulk.completed K F t W x _ hW, Bulk.completed K F t W x _ hW]; simp [Gaussian.force]
omit [Fintype V] in
lemma spirited (i : Hot R) : GradeAt (w i) (fϑ i ∘ stands K F) := (joint_receipt S F (hW.suppose_mark i)).coarse (stands K F).contDiff.contDiffAt (stands K F).map_zero
-- t remains fine-unit coupling; rewrite exactly
omit [Fintype V] in
lemma pulling (x:X) (v:I'→ℝ) : Assembly.affine (R:=R) w (fun i=> fϑ i ∘ stands K F) (Aϑ ∘ stands K F) (season x v) = Assembly.affine (R:=R) w fϑ Aϑ (Bulk.translated K F x v) := by
   unfold Assembly.affine; congr 1
   · unfold vacuumLetter; simp_rw [jet_continuous_right _ ((rooted hW K F t).smooth.of_le le_top), locates]
   unfold curve markLetter; congr 1; ext1 n; congr 1; funext i
   dsimp only [markFn]; rw [jet_continuous_right _ ((joint_receipt S F (hW.suppose_mark i)).smooth.of_le le_top), locates] -- defeq?

variable (Z : Vibe (fieldDir G c 1) (Precision.Key F G))
def painted (W:Colors R G f) := fun i=> (markFn S F W i ∘ stands K F) ∘ Z.effect
def blown (W:Colors R G f) := Z.price (geometric K F t W ∘ stands K F)
def forecast (W:Colors R G f) (x:X) (r:ℕ) := Assembly.prescription (1,x,0) (reach X) W.power (painted K F Z W) (blown K F t Z W) Qϑ (K.symm F t) r

private theorem straight (x:X) (r:ℕ) : Fk K F t W x r=Assembly.prescription (1,x,0) (reach X) w (fun i=> fϑ i ∘ stands K F) (Aϑ ∘ stands K F) Qϑ (K.symm F t) r := by
   unfold Bulk.Fk; ext i; rw [(Assembly.contracted _ _ _ _ _ _ _ (K.positive F t) ..).2,(Assembly.contracted _ _ _ _ _ _ _ (K.positive F t) ..).2]; refine integral_congr_ae (Eventually.of_forall fun y=> ?_)
   dsimp only; simp_rw [exponent_identity]; exact (congrArg (fun p' : PTable R=> (Poly.pass (series R r p')).part i) (pulling hW K F t x y)).symm

theorem port (x:X) (r:ℕ) : Fk K F t W x r=forecast K F t Z W x r :=
      (straight hW K F t x r).trans (Door.agree x Qϑ (K.positive F t) Z (ready hW K F t) (spirited hW K F) r (K.symm F t))
end Pull
end YM.Comparison.RG02.Affinity
