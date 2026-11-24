import YM.Integration.WilsonIndependentSpoutPostedAction
import YM.Integration.WilsonIndependentSpoutThermalMark

/-! Normalize the actual finite primitive board on the measured Schur law.
The whole inlet mark is carried on the common quiet and its source-independent
Jacobian cancels in its own denominator. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutPostedHearing
open Matrix PowerSeries Function Lattice RG WilsonCoeffUV WilsonCoeffUV.Blue
open WilsonCoeffUV.Mer WilsonCoeffUV.Embroider WilsonCoeffUV.Embroider.Canvas WilsonCoeffUV.Bank
open Wilson WilsonCoeffUV.Power RegulatorIR.Diagram RegulatorIR.Budget RegulatorIR.Geometry.Field
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Prim RegulatorIR.Budget.Packet RegulatorIR.Oracle
open RegulatorIR.Ledger RegulatorIR.Clocks RegulatorIR.Clocks.Warp RegulatorIR.Calibration
open PertExtension PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested
open Tree FreeResolvent Metric Precision Exterior Next.Free
open WilsonIndependentPublicFreeTrain
open WilsonIndependentSpoutSchurFrame (field)
open WilsonIndependentSpoutPostedAction (coefficient)
open scoped Classical BigOperators Matrix MatrixOrder
variable {G:Gauge}

private theorem head {c n:Side}(S:StepData c n)(F:Forest S.ratio)(H Y:FaceRow)
    (Q:Matrix (Body 1 n) (Body 1 c) ℝ)(α:Cost)(unit:constantCoeff α=1)
    {Ñ:ChartRatio G}{V:PChart G n}(p:shellK 2 V)(base:V 0=shine (orbQ (precisionC G n H)))
    (hz:S.patch.Branches S.kernel G)(hu:Inputs S Q (H.acts n) (Y.acts c))
    (hs:(H.acts n).transpose=H.acts n)(ratio:LocalRatio Ñ):
    constantCoeff (field S F H Y Q α Ñ V)=0:=by
  rw [WilsonIndependentSpoutSchurFrame.original S F H Y Q α unit p base hz hu hs]
  have hx:constantCoeff (redo (U:=Active G F⊕Woods G c) α X)=0:=by rw [redo_X];simp
  have hu₀:constantCoeff (shot S F Q Ñ V)=0:=by
    rw [shot,loom,←coeff_zero_eq_constantCoeff_apply,coeff_map,coeff_zero_eq_constantCoeff_apply,
      flash_blank (pack_zero S ratio),map_zero]
  rw [map_add,WilsonIndependentSpoutSchurVote.passed _ hx hu₀,map_mul,map_sub,map_one,map_pow,
    WilsonIndependentSpoutSchurVote.soil_head,constantCoeff_inv,unit,inv_one,map_one,one_pow,
    sub_self,zero_mul,zero_add]

def posted (A:Levels G)(N m:ℕ)(n:Side)(T:Branchix→Orders (KFoot G))(α:Cost)
    (V:PChart G (n*(loose A m).L)):Ink (Active G (repeatF (mStep A n m))⊕Woods G n):=
  mk fun e=>if e=0 then 0 else coefficient A N m n T α V e

variable {W:Type}{M:W→ℕ}{sides:Page M→Side}{K:KernelChoices}
    (C:Circuit M sides)(Y:Program K)(Z:∀P:Patch,P.Branches K G)(D:Tent M)(f:Flap M)
    (A:Levels G)(s:ℕ)(inc:Matches A C K s f.volW)

include Y inc in
theorem frame (simple:G.Simple)(n:Side):
    let N:=s+M f.volW;let m:=s+(M f.volW-(f.offset+1));let S:=mStep A n m;let F:=repeatF S
    let Q:=roam A N m n;let H:=freeForms A N (m+1);let H':=freeForms A N m
    let Ñ:=XSpace.Bare.chart G;let V:=(story A Ñ N (m+1)).1 (n*(loose A m).L)
    let α:=tale (D f.prev).dine
    posted A N m n (C.bore G Z (sheet D) f) α V=field S F H H' Q α Ñ V:=by
  intro N m S F Q H H' Ñ V α
  have finer:m<N:=by dsimp only [m,N];have:=f.ok;omega
  have hV:Interlace H V:=(old A Ñ simple (XSpace.Bare.chart_ratio G) N (m+1) finer).basis _
  have unit:constantCoeff α=1:=by rw [←coeff_zero_eq_constantCoeff_apply];simpa [α] using (D f.prev).origin
  apply PowerSeries.ext
  intro e
  rw [posted,coeff_mk]
  by_cases z:e=0
  · subst e;rw [if_pos rfl,coeff_zero_eq_constantCoeff_apply]
    exact (head S F H H' Q α unit hV.lamp hV.stem (A.blocks m 0).branches
      (horizon_step A m N finer n _ rfl) (age_sym A ..) (XSpace.Bare.chart_ratio G)).symm
  · rw [if_neg z]
    exact WilsonIndependentSpoutPostedAction.original C Y Z D f A s inc n e (Nat.pos_of_ne_zero z)

include Y inc in
theorem original (simple:G.Simple)(n:Side)(k:ℕ)(U:Era G ℝ)(ink:Auth k U):
    let N:=s+M f.volW;let m:=s+(M f.volW-(f.offset+1));let S:=mStep A n m;let F:=repeatF S
    let Q:=roam A N m n;let H:=freeForms A N (m+1)
    let Ñ:=XSpace.Bare.chart G;let j:=n*(loose A m).L;let V:=(story A Ñ N (m+1)).1 j
    let α:=tale (D f.prev).dine;let M₀:=posted A N m n (C.bore G Z (sheet D) f) α V
    let W:=loom (camSlice G S F (extractV G S F Q)) (flash (U.1 j))
    let K₀:=Wick (Woods G n) (treeInverse G S F H 0)
    K₀ (raiseE M₀*redo α W)=K₀ (raiseE M₀)*redo α (flash (reed S F H Q Ñ V k (U.1 j))):=by
  intro N m S F Q H Ñ j V α M₀ W K₀
  let H':=freeForms A N m
  have finer:m<N:=by dsimp only [m,N];have:=f.ok;omega
  have hV:Interlace H V:=(old A Ñ simple (XSpace.Bare.chart_ratio G) N (m+1) finer).basis _
  have unit:constantCoeff α=1:=by rw [←coeff_zero_eq_constantCoeff_apply];simpa [α] using (D f.prev).origin
  have see:M₀=field S F H H' Q α Ñ V:=frame C Y Z D f A s inc simple n
  dsimp only [K₀,W]
  rw [see]
  exact WilsonIndependentSpoutThermalMark.normalized S F H H' Q α unit hV.lamp hV.stem
    (A.blocks m 0).branches (horizon_step A m N finer n _ rfl) (age_sym A ..) (XSpace.Bare.chart_ratio G)
    (Convention.tree_pos A m N rfl) hV.shape k (ink.span _) (ink.pale _)

end YM.Integration.WilsonIndependentSpoutPostedHearing
