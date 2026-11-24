import YM.Integration.WilsonPhysicalHistoryRetainedSpringFundedInteraction
import YM.Integration.WilsonPhysicalHistoryRetainedSpringIncoming

/-! The full finite list at one occupied site, with its multiplicities and
the optional signed cubic and quartic part of the entering physical path. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure RGLocalTaylor
open Coat Matter Pond Blaze.March PhysicalNext.Repeat Greenbelt PhysicalNext.Repeat.Legato
open Dict06.Series RGLocalTaylor.Insert Work.F03 Bid Coat Matter
open AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open IterationFour.Vacuum Comparison.RG02 Comparison.RG02.Assembly
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open scoped Topology BigOperators Classical
variable {G : Gauge} {n : Side}

def rosterSource (path : PathData G) (Z : SeriesA G) (w b c : ℝ) (bare : Bool) (x : Site n)
    (U : Config G n) : ℂ :=
  (if bare then (w:ℂ)*(interactionAt path x U:ℂ) else 0)+(b:ℂ)*(springPacketsAt Z c x U:ℂ)

def rosterTaylor (path : PathData G) (Z : SeriesA G) (w b c : ℝ) (bare : Bool) (x : Site n)
    (z : Dir G n) (K : ℕ) (g : ℝ) : ℂ :=
  (if bare then (w:ℂ)*interactionTaylor path x z (fun i=>if i then K+3 else K+2) g else 0)+
    ∑ i : Fin Z.length,((b*c^((Z.get i).grade-(Z.get i).rise):ℝ):ℂ)*
      siteTaylor (Z.get i).cells x z ((Z.get i).rise+K+1) g

private theorem sum_entries {α E : Type*} [AddCommMonoid E] (Z : List α) (f : α→E) :
    (Z.map f).sum=∑ i : Fin Z.length,f (Z.get i) := by
  conv_lhs => rw [←List.ofFn_get Z]
  simp only [List.map_ofFn,List.sum_ofFn,Function.comp_apply]

theorem roster_difference (path : PathData G) (Z : SeriesA G) (w b c : ℝ) (bare : Bool)
    (x : Site n) (U : Config G n) (z : Dir G n) (K : ℕ) (g : ℝ) :
    rosterSource path Z w b c bare x U-rosterTaylor path Z w b c bare x z K g=
      (if bare then (w:ℂ)*((interactionAt path x U:ℂ)-
        interactionTaylor path x z (fun i=>if i then K+3 else K+2) g) else 0)+
      ∑ i : Fin Z.length,((b*c^((Z.get i).grade-(Z.get i).rise):ℝ):ℂ)*
        ((sitePacket (Z.get i).cells x U:ℂ)-siteTaylor (Z.get i).cells x z ((Z.get i).rise+K+1) g) := by
  have read : (b:ℂ)*(springPacketsAt Z c x U:ℂ)=∑ i : Fin Z.length,
      ((b*c^((Z.get i).grade-(Z.get i).rise):ℝ):ℂ)*(sitePacket (Z.get i).cells x U:ℂ) := by
    simp only [springPacketsAt,sum_entries,Complex.ofReal_sum,Finset.mul_sum,Complex.ofReal_mul,mul_assoc]
  simp only [rosterSource,rosterTaylor,read,mul_sub,Finset.sum_sub_distrib]
  cases bare <;> simp only [Bool.false_eq_true,if_false,if_true] <;> ring

theorem roster_taylor_zero (path : PathData G) (Z : SeriesA G) (w b c : ℝ) (bare : Bool)
    (x : Site n) (z : Dir G n) (g : ℝ) : rosterTaylor path Z w b c bare x z 0 g=0 := by
  have empty (a : PrismA G) : siteTaylor a.cells x z (a.rise+1) g=0:=
    flat_site_polynomial _ _ _ (by omega : a.rise+1<a.rise+2) g
  simp only [rosterTaylor,Nat.zero_add,interaction_zero,empty,mul_zero,
    Finset.sum_const_zero,ite_self,add_zero]

theorem roster_incoming (R : Run G) (N per j r : ℕ) (Z : SeriesA G) (g : ℝ)
    (x : Site (R.family.side j per)) (U : Config G (R.family.side j per)) :
    let p:=finitePitch R N j r g
    let γ:=g^2*pitchTail R N j r g
    let path:=(R.family.path.rep N per j).path
    (springAt R N per j r Z g x U:ℂ)=
      (γ*secondAt (R.family.path.levels.params j).clip path x U:ℝ)+
      rosterSource path Z (γ+R.alloy.B.kin.alpha N j) (Integral.temperature g*p)
        (g/Real.sqrt p) true x U := by
  intros p γ path
  simp only [springAt,rosterSource,if_true,Complex.ofReal_add,Complex.ofReal_mul,p,γ,path]
  ring

end YM.Integration.OriginalMarkedRunAction
