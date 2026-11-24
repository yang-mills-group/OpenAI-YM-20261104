import YM.PertExtension.SelfRate
import YM.PertExtension.BareSlot

/-! Radial first derivatives on the genuine tree fluctuation space of
clover slots used by the source section. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.PertExtension.LatticePT.Slope
open Function Filter Set Wilson Lattice RG Source MeasureTheory Orb GaussianScore Gauge
open Orb.SlotEvaluation LatticePT.Projection
open scoped ContDiff Topology Classical BigOperators Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{n:Side}(o:Site n)(u:Dir G n)(z:RG.Slot)

def address (o:Site n)(z:RG.Slot): Face (Per n) := (wrap _ z.offset + o,z.plaq) -- infer
lemma first_plate : HasDerivAt (fun r:ℝ=>G.mat (faceValue (coverAt o (r • u)) (z.offset,z.plaq))) (G.colorMat (letterPolar (address o z) u)) 0:=by
     unfold coverAt faceValue; simp_rw [travel_at]
     exact (first_walk u _ _).congr_deriv (congr_arg _ (face_line ..))
@[simp] lemma plate_unit : faceValue (coverAt o (0:Dir G n)) (z.offset,z.plaq) = 1:=by
  unfold coverAt faceValue; rw [representative_zero]; exact Pressure.one _

lemma currency : HasDerivAt (fun r:ℝ=>G.curvature (faceValue (coverAt o (r•u)) (z.offset,z.plaq))) (letterPolar (address o z) u) 0:=by
   simp_rw [Gauge.curvature,Gauge.mat_inv]
   have he := first_plate o u z
   apply HasDerivAt.congr_deriv (G.projectColor.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 ((he.sub he.star).const_smul ((1/2):ℝ)))
   change G.projectColor (((1/2):ℝ) • (G.colorMat _ - star (G.colorMat _)))= _
   rw [G.colorMat_skew,sub_neg_eq_add, ←two_smul ℝ,smul_smul]
   norm_num
lemma wound : HasDerivAt (fun r : ℝ=>z.eval (coverAt o (r • u))) (letterPolar (address o z) u) 0:=by
   let b (r:ℝ):G.El:=travel (coverAt o (r•u)) 0 z.walk
   let M (r:ℝ):G.Color:=G.curvature (faceValue (coverAt o (r•u)) (z.offset,z.plaq)); let B:=fun r=>G.mat (b r)
   let a(r):=G.adjoint (b r) (M r)
   have hb : b 0=1 := by dsimp only [b];rw [zero_smul,zero_links];exact Pressure.one _
   have hv : HasDerivAt B (G.colorMat (line (variation u) ((wrap n) 0+o) z.walk)) 0:=by unfold B b;simp_rw [coverAt,travel_at];apply first_walk
   let hz:= currency o u z
   have ht:HasDerivAt (fun r=>B r * G.colorMat (M r) * star (B r)) (G.colorMat (letterPolar (address o z) u)) 0:=by
      apply ((hv.mul (G.colorMat.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 hz)).mul hv.star).congr_deriv -- adjust
      change _ + _ * star (G.colorMat (line (variation u) _ z.walk)) = _
      simp [M,B,hb,faceValue,Pressure.one];rfl
   exact HasDerivAt.congr_deriv (G.projectColor.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 ht) (by apply G.project_colorMat _)

local notation "smallG"=> (nhdsWithin (0:ℝ) (Ioi 0))
def leg {n : Side}(o:Site n)(p:Atom G) : Module.Dual ℝ (Dir G n):=Projection.signal (address o p.1) (LatticePT.colorBasis p.2)
lemma legible (p:Atom G):Tendsto (fun t:ℝ=>t⁻¹*field p.1 o p.2 (t • u)) smallG (𝓝 (leg o p u)):=by
   have ht: HasDerivAt (fun r:ℝ=>field p.1 o p.2 (r • u)) ((letterPolar (address o p.1) u) p.2) 0:= (EuclideanSpace.proj (𝕜:=ℝ) p.2).hasFDerivAt.comp_hasDerivAt 0 (wound o u p.1)
   convert! ht.tendsto_slope_zero_right using 2 <;> simp only [field,zero_add,zero_smul, slot_zero,leg,Projection.signal_eq,LatticePT.colorBasis,EuclideanSpace.basisFun_inner, PiLp.zero_apply,sub_zero];rfl

lemma cov (e:Even n.val)(X Y:Cover)(a b:Atom G): (saddle e).wick (leg (wrap n Y) b) (leg (wrap n X) a) = echo n X Y (atAddress a) (atAddress b) := by
    have he x c : address (wrap n x) c= (wrap n (x+c.offset),c.plaq):= by unfold address;rw [map_add,add_comm]
    unfold leg;simp_rw [he]
    exact LatticePT.signals (n:=n) (G:=G) (u:=X) (v:=Y) (atAddress a) (atAddress b) e -- echo built from signals
end YM.PertExtension.LatticePT.Slope
