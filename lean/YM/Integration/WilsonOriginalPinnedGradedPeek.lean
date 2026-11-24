import YM.Integration.WilsonOriginalPinnedDeckOrbit
import YM.Integration.WilsonOriginalGradedJointBinding

/-! The filed angular reading is exactly the Taylor coefficient of the deck orbit of one fixed physical source lift. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPinnedGradedPeek
open Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise QuadraticLocal.Poetry Stationary
open Comparison.RG02 AllOrder.Floe Multi Exterior Further.PhysicalPeriodLimitF933 Macrame FVA1Physical FVA1Physical.TwoReset
open WilsonOriginalOccupiedFieldLayout WilsonOriginalPinnedDeckOrbit WilsonOriginalJointDeckMotion WilsonEmittedRootedJetWage
open scoped Classical BigOperators ContDiff
variable {G:Gauge} {n N:Side} {V X ι:Type} [DecidableEq V] {o:Passport n V} {J:Census V}

def chart (G:Gauge) (N:Side) : Joint G N ≃L[ℝ] ℝ×fieldDir G N 1:=
  (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr ((edgeColor (G:=G) (n:=N)).symm.trans (Stationary.arm G N 1))

theorem tested (z:Joint G N): Bulk.projected (fun _ U=>U) (chart G N z) = RG.increment 1 z.2:=by
  funext e
  change Stationary.input G N (edgeColor.symm z.2) e=G.lieExp (z.2 e)*1
  rw [input_color,ContinuousLinearEquiv.apply_symm_apply,mul_one]

variable (h:n.val∣N.val) (M:ι→Row o J G X) (t:X) (grades:V→ℕ) (L:Layout G) (T:Finset Age)
abbrev bank := TwoReset.copyColor h M grades (fun i=>(M i).paint t) L T
local notation "Bank" => bank h M t grades L T
theorem original {w:V→ℝ} {σ C:ℝ} {order seats shelf:ℕ}
    (stock:Scene.Armada M w grades σ C order seats shelf) (hs:0<σ)
    (s:Hot J) (v:s.val.val) (b:PagesOf n N) (x:Site N) (j:ℕ) (A:Directions G N):
    Assembly.jet (WilsonOriginalPolarizedAngularPage.board h x (motion G) (needle h M t s.val v 0 b)) ((Bank).power s+j) (1,A)=
      (peek h M grades L T t j (edgeColor.symm A)).part s.val:=by
  rw [WilsonOriginalPinnedDeckOrbit.original h M t s.val v stock hs]
  have base:shade h M t 0 (fun i _=>(M i).mode=s.val)=frame h M t (fun i _=>(M i).mode=s.val):=by funext q;simp [shade]
  have read: (Bulk.projected ((Bank).mark s)) ∘ chart G N =frame h M t (fun i _=>(M i).mode=s.val):=by
    funext z
    rw [WilsonOriginalOccupiedFieldLayout.filed h M t stock hs L T s z]
    change (Bank).mark s z.1 (Bulk.projected (fun (_:ℝ) U=>U) (chart G N z))=_
    rw [tested]
  have analyticFrame:=WilsonOriginalOccupiedFieldLayout.analytic h M t stock hs 0 (fun i _=>(M i).mode=s.val)
  rw [base] at analyticFrame
  have reverse:Bulk.projected ((Bank).mark s)=frame h M t (fun i _=>(M i).mode=s.val) ∘ (chart G N).symm:=by
    rw [←read];funext y;simp
  have smooth:ContDiff ℝ ω (Bulk.projected ((Bank).mark s)):=by
    rw [reverse];exact analyticFrame.comp (chart G N).symm.contDiff
  rw [base,←read]
  unfold peek Air.discharge
  rw [part_lit _ s]
  unfold Assembly.jet
  have coeff:iteratedFDeriv ℝ ((Bank).power s+j) (Bulk.projected ((Bank).mark s) ∘ chart G N) 0=
      (iteratedFDeriv ℝ ((Bank).power s+j) (Bulk.projected ((Bank).mark s)) ((chart G N) 0)).compContinuousLinearMap (fun _=>(chart G N).toContinuousLinearMap):=
    (chart G N).toContinuousLinearMap.iteratedFDeriv_comp_right smooth 0 (by simp)
  rw [coeff,map_zero,ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rfl

end YM.Integration.WilsonOriginalPinnedGradedPeek
