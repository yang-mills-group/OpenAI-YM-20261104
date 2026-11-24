import YM.Integration.WilsonMarkedInheritedGaussianPlacement
import YM.Comparison.RG02.Bulk.Fk
import YM.Integration.WilsonCommonConditionalGaussian
import YM.Integration.WilsonMarkedRelativeForestResponse

/-! The retained/free displacement in the actual nonlinear integration chart. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMarkedRelativeGaussianCoordinates
open Function Finset Matrix Lattice Wilson Exterior Precision RG Next.Free UVExtension.Free
open Tree Work.F03 FormalBulk08 FormalBulk08.Flat Reef Jets AllOrder.Ker Push.Uniform Next.SectorChange
open Primitives.TwoWave Primitives.TwoWave.RealSlice PhysicalNext.Repeat.Legato
open Comparison.RG02
open scoped Classical Matrix Topology

variable {G:Gauge} {c f:Side} {S:StepData c f}

def colors (G:Gauge) : (G.ColorIndex→ℝ) ≃L[ℝ] G.Color :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : G.ColorIndex=>ℝ)).symm

def charge (G:Gauge) : ℝ := max 1 ‖(colors G).toContinuousLinearMap‖

theorem grouped (a:G.ColorIndex→ℝ) : ‖colors G a‖ ≤ charge G*‖a‖ :=
  ((colors G).toContinuousLinearMap.le_opNorm a).trans (mul_le_mul_of_nonneg_right (le_max_right ..) (norm_nonneg _))

theorem copied (x:fieldDir G c 1) (v:Site f×Axis) (a:G.ColorIndex) :
    |linearCopy S.ratio (collect G x) v a| ≤ ‖x‖:=by
  unfold linearCopy
  split
  · simp
  · exact (PiLp.norm_apply_le (p:=2) (collect G x (S.ratio.parent v.1,v.2)) a).trans
      (norm_le_pi_norm x _)

def relative (F:Forest S.ratio) (x:fieldDir G c 1) (a:Rays (Pine G S F)) : ChartVars F G:=
  (x,fun v=>colors G (fun l=>a (Reef.pines F (v,l))-(linearCopy S.ratio (collect G x) v.val) l))

theorem placement (F:Forest S.ratio) (x:fieldDir G c 1) (a:Rays (Pine G S F)):
    ‖relative F x a‖ ≤ charge G*(‖a‖+‖x‖):=by
  have h : 1 ≤ charge G:=le_max_left ..
  rw [Prod.norm_def,max_le_iff]
  refine ⟨?_,?_⟩
  · change ‖x‖ ≤ _;nlinarith [mul_nonneg (sub_nonneg.mpr h) (norm_nonneg x),mul_nonneg (zero_le_one.trans h) (norm_nonneg a)]
  · refine (pi_norm_le_iff_of_nonneg (mul_nonneg (zero_le_one.trans h) (add_nonneg (norm_nonneg _) (norm_nonneg _)))).2 fun i=>?_
    apply (grouped _).trans
    apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans h)
    refine (pi_norm_le_iff_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 fun l=>?_
    exact (norm_sub_le ..).trans (add_le_add (norm_le_pi_norm a _) (copied (S:=S) x i.val l))

theorem flatten (x:fieldDir G c 1):‖FreeResolvent.flatten x‖ ≤ ‖x‖:=by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 fun i=>?_
  exact (PiLp.norm_apply_le (p:=2) (x _) _).trans (norm_le_pi_norm x _)

private theorem full_charge {v K b m t:ℝ} (hK:0 ≤ K)(hb:0 ≤ b)(hm:0 ≤ m)(ht:0 ≤ t)
    (paid:v ≤ K*((b*m+t)+m)) :1+v ≤ (1+K+K*(b+1)*m)*(1+t):=by
  nlinarith only [paid,hK,ht,mul_nonneg (mul_nonneg (mul_nonneg hK (by linarith : 0 ≤ b+1)) hm) ht]

def focus (F:Forest S.ratio) (D:Matrix (Pine G S F) (wire G c) ℝ) (x:fieldDir G c 1)
    (ξ:Rays (Pine G S F)) : ChartVars F G :=
  relative F x ((D.mulVec (FreeResolvent.flatten x : wire G c → ℝ)) + ξ)

theorem shifted (F:Forest S.ratio) (D:Matrix (Pine G S F) (wire G c) ℝ) (b:ℝ) (hb:0 ≤ b)
    (bought:∀a d,|D a d| ≤ b) (x:fieldDir G c 1) (ξ:Rays (Pine G S F)):
    1+‖focus F D x ξ‖ ≤ 
      (1+charge G+charge G*((Fintype.card (wire G c):ℝ)*b+1)*‖x‖)*(1+‖ξ‖):=by
  let y : wire G c → ℝ := FreeResolvent.flatten x
  let w : ℝ := (Fintype.card (wire G c):ℝ)*b
  have hw : 0 ≤ w := mul_nonneg (Nat.cast_nonneg _) hb
  have hK : 0 ≤ charge G := zero_le_one.trans (le_max_left ..)
  have iy : ‖y‖ ≤ ‖x‖ := flatten x
  have hd : ‖D.mulVec y‖ ≤ w*‖y‖ := WilsonMarkedInheritedGaussianPlacement.mean D b hb bought y
  have hd' : ‖D.mulVec y‖ ≤ w*‖x‖ := hd.trans (mul_le_mul_of_nonneg_left iy hw)
  have vec : ‖D.mulVec y+ξ‖ ≤ w*‖x‖+‖ξ‖ := (norm_add_le (D.mulVec y) ξ).trans (add_le_add_left hd' ‖ξ‖)
  have total : ‖focus F D x ξ‖ ≤ charge G*((w*‖x‖+‖ξ‖)+‖x‖) :=
    (placement F x (D.mulVec y+ξ)).trans (mul_le_mul_of_nonneg_left (add_le_add_left vec ‖x‖) hK)
  exact full_charge hK hw (norm_nonneg x) (norm_nonneg ξ) total

theorem original (R:Run G) (N i per:ℕ) (hi:i<N)
    (F:Forest (R.family.path.levels.clock.op i per).ratio)
    (tag:(R.family.path.levels.clock.op i per).Choices)
    (x:fieldDir G (R.family.side i per) 1) (z:(F.Free × G.ColorIndex)→ℝ):
    let S:=R.family.path.levels.clock.op i per
    let K:=((RunFormalChain.fromRun R).step N i per hi)
    let D:=Flat.rawMean G S F (Bloch.installed S.ratio ((destination R.family.path.levels N i).duo R.family.path.levels.clock.kernel.penalty).A0)
    (Bulk.translated K F x z).2=relative F x (D*ᵥFreeResolvent.flatten x + z ∘ (Reef.pines F).symm):=by
  dsimp only
  rw [Bulk.footing]
  apply Prod.ext
  · rfl
  funext a
  apply PiLp.ext
  intro l
  have h:=congrFun (WilsonCommonConditionalGaussian.mean R N i per hi F tag x) (a,l)
  let K := (RunFormalChain.fromRun R).step N i per hi
  let S := R.family.path.levels.clock.op i per
  let D := Flat.rawMean G S F (Bloch.installed S.ratio ((destination R.family.path.levels N i).duo R.family.path.levels.clock.kernel.penalty).A0)
  change (fderiv ℝ (K.b F) 0 x a) l + linearCopy S.ratio (collect G x) a.val l = (D *ᵥ FreeResolvent.flatten x) (Reef.pines F (a,l)) at h
  change (fderiv ℝ (K.b F) 0 x a) l + z (a,l) = (D *ᵥ FreeResolvent.flatten x) (Reef.pines F (a,l)) + z ((Reef.pines F).symm ((Reef.pines F) (a,l))) - linearCopy S.ratio (collect G x) a.val l
  rw [Equiv.symm_apply_apply]
  linarith only [h]

end YM.Integration.WilsonMarkedRelativeGaussianCoordinates
end
