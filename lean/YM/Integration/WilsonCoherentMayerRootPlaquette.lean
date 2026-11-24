import YM.Integration.WilsonCoherentMayerFuelPolynomial
import YM.Integration.WilsonPhysicalHistoryRetainedSpringSample
import YM.AnalyticNext.CUBIC_MATCH.Terms.Slots

/-! The actual four-link curl of a former Wilson curvature insertion as a
polynomial on the free coordinates of the very same forest, in every symmetry. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentMayerRootPlaquette
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open Blaze.March PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt RGLocalTaylor RGLocalTaylor.Insert
open RG01.Survive PhysicalNext.Repeat.Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat.Legato
variable {G:Gauge} {c f L:Side} {S:StepData c f} {T:Tube G S} {F:Forest S.ratio} {R:Rep G f}
    {P:Teller G} {Q:ConnectedActivityE6.Target G P} {W s μ C:ℝ} {o:Target.Order G W}
    {H:Cash W s μ L Q o C T R} {j n l k M:ℕ} {χ:Chi}

open PhysicalNext.Repeat.Malachite AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open Next.SectorChange WilsonCoherentMayerProjection
open Next.Rank Comparison.RG02.Cumulants Comparison.RG02.Assembly
open WilsonPositionSeparatedProfileMayerWickInputs WilsonRetainedSignedStencilTaylor
open WilsonCoherentMayerHearing Dict06.Series

variable (X:Coat T F)


open WilsonCoherentMayerFuelPolynomial (coordinate read_coordinate)
open OriginalMarkedRunAction WilsonCoherentMayerNoise Work.F03 Bid
private theorem coin_negative (B:Normal.poly (Eye X)):Rise.coin (-B)=Rise.coin B:=by simp [Rise.coin,Rise.cents]

def axis (e:Bond f)(b:G.ColorIndex):Normal.poly (Eye X):=if h:e∈F.trunks then 0 else coordinate X e h b

theorem axis_read (e:Bond f)(b:G.ColorIndex)(z:Air f G):
    Cloud.paint (fun i=>z (tube X i)) (axis X e b)=(WilsonCoherentMayerNoise.row F z e b:ℂ):=by
  by_cases h:e∈F.trunks
  · simp [axis,WilsonCoherentMayerNoise.row,h]
  · simp only [axis,dif_neg h,read_coordinate,WilsonCoherentMayerNoise.row,if_neg h];rfl

theorem axis_pay (e:Bond f)(b:G.ColorIndex):Rise.coin (axis X e b)≤1 ∧ (axis X e b).totalDegree≤1:=by
  by_cases h:e∈F.trunks <;> simp [axis,h,coordinate,Rise.coin]

def turn (t:Signed)(e:Bond f)(b:G.ColorIndex):Normal.poly (Eye X):=
  let v:Step:=(posDir e.2).rotate t
  let j:=v.used (affine t 0 e.1)
  if v.neg then -axis X j b else axis X j b

theorem turn_read (t:Signed)(e:Bond f)(b:G.ColorIndex)(z:Air f G):
    Cloud.paint (fun i=>z (tube X i)) (turn X t e b)=((pulled (angularSample F z) t (e.1,coord e.2) b):ℂ):=by
  simp only [turn,pulled,show axisEquiv.symm (coord e.2)=e.2 from axisEquiv.symm_apply_apply _]
  have back (j:Axis):axisEquiv.symm (coord j)=j:=axisEquiv.symm_apply_apply _
  split
  · simp only [map_neg,axis_read,angularSample,back,Prod.mk.eta]
    exact (Complex.ofReal_neg _).symm
  · simp only [axis_read,angularSample,back,Prod.mk.eta]

theorem turn_pay (t:Signed)(e:Bond f)(b:G.ColorIndex):Rise.coin (turn X t e b)≤1 ∧ (turn X t e b).totalDegree≤1:=by
  let v:Step:=(posDir e.2).rotate t
  by_cases h:v.neg=true
  · simp only [turn,show ((posDir e.2).rotate t).neg=true from h,if_true,coin_negative,MvPolynomial.totalDegree_neg]
    exact axis_pay X _ b
  · simp only [turn,show ((posDir e.2).rotate t).neg≠true from h]
    exact axis_pay X _ b

def curl (t:Signed)(q:Face (Per f))(b:G.ColorIndex):Normal.poly (Eye X):=
  turn X t (q.1+step q.2.val.1,q.2.val.2) b - turn X t (q.1,q.2.val.2) b -
    (turn X t (q.1+step q.2.val.2,q.2.val.1) b - turn X t (q.1,q.2.val.1) b)

theorem curl_read (t:Signed)(q:Face (Per f))(b:G.ColorIndex)(z:Air f G):
    Cloud.paint (fun i=>z (tube X i)) (curl X t q b)=((faceCurl q (pulled (angularSample F z) t) b):ℂ):=by
  change _=(((Exterior.d 1 f*ᵥExterior.parts G 1 (pulled (angularSample F z) t) b) (q.1,plaquette q.2)):ℂ)
  rw [Exterior.d_plaquettes]
  simp only [curl,map_sub,Complex.ofReal_sub,turn_read,Exterior.parts]

private theorem subtract (B A:Normal.poly (Eye X)):Rise.coin (B-A)≤Rise.coin B+Rise.coin A:=by
  rw [sub_eq_add_neg,←coin_negative X A]
  exact Rise.taller 0 zero_le_one B (-A)
private theorem degree_sub (B A:Normal.poly (Eye X)):(B-A).totalDegree ≤ max B.totalDegree A.totalDegree:=by
  rw [sub_eq_add_neg];exact (MvPolynomial.totalDegree_add ..).trans_eq (by rw [MvPolynomial.totalDegree_neg])

theorem paid (t:Signed)(q:Face (Per f))(b:G.ColorIndex):Rise.coin (curl X t q b)≤4 ∧ (curl X t q b).totalDegree≤1:=by
  let a:=turn X t (q.1+step q.2.val.1,q.2.val.2) b
  let c:=turn X t (q.1,q.2.val.2) b
  let d:=turn X t (q.1+step q.2.val.2,q.2.val.1) b
  let e:=turn X t (q.1,q.2.val.1) b
  have ha:=turn_pay X t (q.1+step q.2.val.1,q.2.val.2) b
  have hc:=turn_pay X t (q.1,q.2.val.2) b
  have hd:=turn_pay X t (q.1+step q.2.val.2,q.2.val.1) b
  have he:=turn_pay X t (q.1,q.2.val.1) b
  change Rise.coin (a-c-(d-e))≤4 ∧ (a-c-(d-e)).totalDegree≤1
  constructor
  · calc _≤Rise.coin a+Rise.coin c+(Rise.coin d+Rise.coin e):=(subtract X _ _).trans (add_le_add (subtract X _ _) (subtract X _ _))
         _≤1+1+(1+1):=add_le_add (add_le_add ha.1 hc.1) (add_le_add hd.1 he.1)
         _=4:=by norm_num
  · exact (degree_sub X _ _).trans (max_le ((degree_sub X _ _).trans (max_le ha.2 hc.2)) ((degree_sub X _ _).trans (max_le hd.2 he.2)))

end YM.Integration.WilsonCoherentMayerRootPlaquette
