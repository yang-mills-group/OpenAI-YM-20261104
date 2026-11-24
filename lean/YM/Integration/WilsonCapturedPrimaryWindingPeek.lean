import YM.Integration.WilsonCapturedPrimaryWindingCensusRead
import YM.Integration.WilsonMeasuredUnconditionalCatalogue
import YM.Integration.WilsonEmittedFiledDeckFare

/-! The original pupil minus the next-word table keeps its true signed finite
antidiagonal, the full mark shift, and its degree-zero entry. -/
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWindingPeek
section grades
open WilsonMeasuredTransitionCatalogue
open scoped Classical BigOperators
variable {C V:Type} [Fintype C] [Fintype V] {D:ℕ}

theorem ledger (r:ℝ) (c:V→ℕ→ℝ) (X:C→ℕ→ℂ) (Y:V→ℕ→ℂ)
    (pole i:ℕ) (hi:i<pole+D+1) :
    (∑a:Names C V D, weight r c a • slice pole i (lag a) (value X Y a))=
      if pole ≤ i then (r:ℂ)*(∑ z,X z (i-pole))-
        ∑v,∑b∈(Finset.HasAntidiagonal.antidiagonal (i-pole):Finset (ℕ×ℕ)), (c v b.1:ℂ)*Y v b.2
      else 0 := by
  classical
  by_cases low:i <pole
  · have zero(a:Names C V D):slice pole i (lag a) (value X Y a)=0:=if_neg (by omega)
    simp only [zero,smul_zero,Finset.sum_const_zero,if_neg (Nat.not_le.mpr low)]
  have enough:pole≤ i:=by omega
  let e:=i-pole
  have hd:e≤D:=by dsimp [e];omega
  have out(z:C): weight r c (D:=D) (.inl z) • slice pole i (lag (V:=V) (D:=D) (.inl z)) (X z)
      = (r:ℂ)*X z e :=by simp [weight,lag,slice,enough,Complex.real_smul,e]
  have back (v:V)(k:Fin (D+1)):
      (-c v k) • slice pole i k.val (Y v) =
      -(if k.val≤e then (c v k:ℂ)*Y v (e-k.val) else 0):=by
    by_cases h:k.val≤e
    · have ok:k.val+pole≤ i:=by dsimp [e] at h;omega
      have addr:i-k.val-pole=e-k.val:=by dsimp [e];omega
      simp [slice,h,ok,addr,Complex.real_smul]
    · have skip:¬k.val+pole≤ i:=by dsimp [e] at h;omega
      simp [slice,h,skip]
  rw [Fintype.sum_sum_type,Fintype.sum_prod_type]
  simp only [value,weight,lag] at out ⊢
  simp_rw [out,back]
  simp only [Finset.sum_neg_distrib, ←Finset.mul_sum]
  have counted(v:V):=antidiagonal e hd (fun i j=>(c v i:ℂ)*Y v j)
  simp_rw [counted]
  rw [if_pos enough]
  abel

end grades
open Lattice RG Wilson Marker Multi QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise
open AllOrder AllOrder.Floe Laurent Comparison.RG02 FVA1Physical.TwoReset
open AnalyticBridge.SectorAffine.Offset WilsonMeasuredTransitionCatalogue
open WilsonMeasuredOriginalCatalogueUnion
open scoped BigOperators Classical
variable {G:Gauge} {n:Side} {C V X:Type} [Fintype C] [Fintype V]
  {I:C→Type} {K:V→Type} {P:C→Passport n Unit} {S:V→Passport n Unit}
  {J:Census Unit} {D:ℕ}
variable (F:(z:C)→I z→Row (P z) J G X) (T:(v:V)→K v→Row (S v) J G X)


variable (d:ℕ) (s:Multi.Hot J) (t:X)
local notation "code" => (fun _:Unit=>d)
local notation "model" => rows (D:=D) F T
variable (r:ℝ) (c:V→ℕ→ℝ)
variable (L:Layout G) (tape:Finset Age)
local notation "pole₀" => Launch.index J code s.val + 1

open Comparison.RG02.Adjacent RegulatorIR RegulatorIR.Budget RegulatorIR.Budget.Packet
open RegulatorIR.FVAAlt2 RegulatorIR.Diagram WilsonEmittedFiledThermalGerm
variable {Lab:Type} [DecidableEq Lab] {marks:Census Lab}

theorem recorded (V₁ V₂:Bulk.Colors marks G n) (c₁ c₂:UnitCost) (u:Lab)
    (well₁:Bulk.Well V₁) (well₂:Bulk.Well V₂)
    (t₁:V₁.power (Booth.Arm.pub u)=pole₀) (t₂:V₂.power (Booth.Arm.pub u)=pole₀)
    (read:∀e≤D,∀B:Stationary.Link G n,
      (r:ℂ)*(∑z,(peek dvd_rfl (F z) code L tape t e B).part s.val) -
        (∑v,∑l∈(Finset.HasAntidiagonal.antidiagonal e:Finset (ℕ×ℕ)),
          (c v l.1:ℂ)*(peek dvd_rfl (T v) code L tape t l.2 B).part s.val) =
        WilsonEmittedFiledDeckFare.row c₁ V₁ u e B-WilsonEmittedFiledDeckFare.row c₂ V₂ u e B)
    (i:ℕ) (hi:i<pole₀+D+1) (v:Directions G n) :
    (∑a:Names C V D,weight r c a • WilsonEmittedFiledGerm.price model (fun _=>code)
      (fun _=>t) lag s (fun _=>L) (fun _=>tape) i v a)=
      Assembly.jet (field c₁ V₁ u-field c₂ V₂ u) i (1,Stationary.edgeColor.symm v) := by
  let A:=WilsonCubicOriginalTorus.coordinates G n v
  let top (z:C)(j:ℕ):=(peek dvd_rfl (F z) code L tape t j A).part s.val
  let bottom (v:V)(j:ℕ):=(peek dvd_rfl (T v) code L tape t j A).part s.val
  have identical(a:Names C V D):WilsonEmittedFiledGerm.price model (fun _=>code)
      (fun _=>t) lag s (fun _=>L) (fun _=>tape) i v a =
      WilsonMeasuredTransitionCatalogue.slice pole₀ i (lag a) (WilsonMeasuredTransitionCatalogue.value top bottom a) := by
    cases a with
    | inl z =>
      unfold WilsonEmittedFiledGerm.price WilsonMeasuredTransitionCatalogue.slice
      simp only [rows,lag,WilsonMeasuredTransitionCatalogue.value,top]
      split
      · rw [WilsonMeasuredOriginalPeriodWord.literal (F z) code L tape t _ A]
        rfl
      · rfl
    | inr b =>
      rcases b with ⟨v,l⟩
      unfold WilsonEmittedFiledGerm.price WilsonMeasuredTransitionCatalogue.slice
      simp only [rows,lag,WilsonMeasuredTransitionCatalogue.value,bottom]
      split
      · rw [WilsonMeasuredOriginalPeriodWord.literal (T v) code L tape t _ A]
        rfl
      · rfl
  simp_rw [identical]

  rw [ledger r c top bottom pole₀ i hi]
  have sv := WilsonEmittedFiledMixedWindow.grading c₁ V₁ u well₁
  have sz := WilsonEmittedFiledMixedWindow.grading c₂ V₂ u well₂
  rw [t₁] at sv
  rw [t₂] at sz
  by_cases reached : pole₀ ≤ i
  · rw [if_pos reached]
    let e:=i-pole₀
    have ei : pole₀+e=i := by dsimp [e]; omega
    have attained₁ := WilsonEmittedFiledThermalGerm.ray c₁ V₁ u well₁ e A
    have attained₂ := WilsonEmittedFiledThermalGerm.ray c₂ V₂ u well₂ e A
    rw [t₁,ei] at attained₁
    rw [t₂,ei] at attained₂
    have exposed := read e (by dsimp [e]; omega) A
    change (r:ℂ)*(∑ z,top z e) -
      (∑v,∑l∈(Finset.HasAntidiagonal.antidiagonal e:Finset (ℕ×ℕ)), (c v l.1:ℂ)*bottom v l.2) =
        Assembly.jet (field c₁ V₁ u-field c₂ V₂ u) i (1,A)
    rw [show (r:ℂ)*(∑ z,top z e) -
      (∑v,∑l∈(Finset.HasAntidiagonal.antidiagonal e:Finset (ℕ×ℕ)), (c v l.1:ℂ)*bottom v l.2) =
        WilsonEmittedFiledDeckFare.row c₁ V₁ u e A-WilsonEmittedFiledDeckFare.row c₂ V₂ u e A from exposed]
    change _ = Tensor.diagonal (Tensor.coeff (field c₁ V₁ u-field c₂ V₂ u) i 0) (1,A)
    simp only [Tensor.diagonal,Tensor.coeff,iteratedFDeriv_sub_apply (sv.smooth.of_le le_top)
      (sz.smooth.of_le le_top),smul_sub,_root_.sub_apply]
    exact (congrArg₂ Sub.sub attained₁ attained₂).symm
  · rw [if_neg reached]
    simp [Assembly.jet,(sv.sub sz).vanish i (Nat.lt_of_not_ge reached)]

end YM.Integration.WilsonCapturedPrimaryWindingPeek
