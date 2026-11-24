import YM.Integration.WilsonCapturedRootedAngularSlots

/-! Exponential angular income of the real deposited word at its selected
occupied lift. The roster can be restricted before its subsequent comparison.
The graded board is the original copied and fired field on the same quiet layout. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonCapturedCoveredSourceWage
open Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise Stationary
open Comparison.RG02 Comparison.RG02.Order Multi AllOrder.Floe Exterior
open Further.PhysicalPeriodLimitF933 Macrame FVA1Physical FVA1Physical.TwoReset
open WilsonOriginalOccupiedFieldLayout WilsonOriginalPinnedDeckOrbit WilsonEmittedRootedJetWage
open WilsonOriginalSuspendedFootprint WilsonOriginalJointDeckMotion WilsonOriginalCenteredSeamSalary
open WilsonOriginalSuspendedTensor WilsonCapturedRootedAngularSlots WilsonOriginalLinkedAngularPage
open scoped Classical BigOperators ContDiff
variable {G:Gauge} {n N:Side} {V X ι:Type} [DecidableEq V] {o:Passport n V} {J:Census V}
    (h:n.val∣N.val) (M:ι→Row o J G X) (t:X) (s:J.Mode) (v:s.val)
    {w:V→ℝ} {grades:V→ℕ} {σ C:ℝ} {order seats shelf:ℕ}

def crop (cut:ι→Prop) : {i//cut i}→Row o J G X:=fun i=>M i.val

theorem earned (receipt:Scene.Armada M w grades σ C order seats shelf) (cut:ι→Prop) :
    Scene.Armada (crop M cut) w grades σ C order seats shelf:=by
  refine ⟨receipt.toMinistry,receipt.positive,?_,
    ⟨fun i=>receipt.purchases.spend i.val,fun i=>receipt.purchases.usable i.val⟩,
    fun i=>receipt.honor i.val⟩
  intro y
  have paid:=receipt.suggests y
  exact ⟨fun i=>paid.1 i.val,paid.2.1.comp_injective Subtype.val_injective,
    (tsum_comp_le_tsum_of_inj paid.2.1 paid.1 Subtype.val_injective).trans paid.2.2⟩

def fare (G:Gauge) (k r:ℕ) (σ C:ℝ) :=
  (k.factorial:ℝ)⁻¹*(Fintype.card (Fin r ↪ Fin k):ℝ)*
    (UVNext.PricedKernels.basin (σ/4)*(fee G σ k*C))

def field (cut:ι→Prop) (j k:ℕ) (b:PagesOf n N):Link G N→ℂ:=
  thermal (needle h (crop M cut) t s v j b) k

def exposure (ρ:ℝ) (r:ℕ) (root:Site N) (F:Link G N→ℂ) : ℝ:=
  ∑ x:Fin r→Site N×Loc G 1,Real.exp (ρ*(radius root (sites x):ℝ))*‖coefficient r F x‖

theorem original (receipt:Scene.Armada M w grades σ C order seats shelf) (hs:0<σ)
    (cut:ι→Prop) (j k r:ℕ) (b:PagesOf n N):
    let root:=(page h (o.origin v.val) b).val
    Poly.toll w s * exposure (σ/8) r root (field h M t s v cut j k b) ≤ fare G k r σ C:=by
  intro root
  have stock:=earned M receipt cut
  have source:=WilsonOriginalPinnedFieldWage.original h (crop M cut) t s v stock hs j k b
  have cash:0≤Poly.toll w s:=prod_nonneg fun v _=>(stock.positive v).le
  have bought:=income (needle h (crop M cut) t s v j b) k r root (σ/8) (Poly.toll w s) _ cash source
  unfold exposure field fare
  rw [mul_sum]
  simpa only [mul_assoc] using bought

theorem boundToProgram (receipt:Scene.Armada M w grades σ C order seats shelf) (hs:0<σ)
    (cut:ι→Prop) (s:Hot J) (v:s.val.val) (layout:Layout G) (tape:Finset Age)
    (b:PagesOf n N) (base:Site N) (e:ℕ) (a:Link G N) :
    let P:=crop M cut
    let K:=WilsonOriginalPinnedGradedPeek.bank h P t grades layout tape
    thermal (WilsonOriginalPolarizedAngularPage.board h base (motion G)
      (needle h P t s.val v 0 b)) (K.power s + e) a=
      (peek h P grades layout tape t e a).part s.val:=by
  have won:=WilsonOriginalPinnedGradedPeek.original h (crop M cut) t grades layout tape
    (earned M receipt cut) hs s v b base e (edgeColor a)
  simpa only [thermal,ContinuousLinearEquiv.symm_apply_apply] using won

end YM.Integration.WilsonCapturedCoveredSourceWage
