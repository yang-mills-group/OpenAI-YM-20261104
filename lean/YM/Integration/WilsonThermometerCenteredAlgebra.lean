import YM.Integration.WilsonThermometerCourseHearing
import YM.Primitives.CONNECTED_GAUSSIAN_CUMULANTS.Algebra
import YM.Comparison.RG02.Algebra.Markers

/-! The finite three-source quotient and the signed row left after all
proper subtractions. Its inverse is fixed before any Wilson integration. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerCenteredAlgebra
open Finset Marker QuadraticLocal Extra.Trajectories Comparison.RG02 Comparison.RG02.Order
open Primitives.GCC.Anchor
open scoped Classical BigOperators
local notation "J" => Stock.census (Fin 3)

def full : (J).Mode := ⟨univ,mem_univ _⟩
def complement (s : (J).Mode) : (J).Mode := ⟨univ \ s.val,mem_univ _⟩

private theorem merges (s t : (J).Mode) : Poly.merges s t full ↔ t=complement s := by
  constructor
  · rintro ⟨dis,cover⟩
    apply Subtype.ext
    ext i
    change i∈t.val ↔ i∈univ \ s.val
    simp only [mem_sdiff,mem_univ,true_and]
    constructor
    · exact fun h k => disjoint_left.mp dis k h
    · intro outside
      have all : i∈s.val∪t.val := by rw [cover]; exact mem_univ _
      exact (mem_union.mp all).resolve_left outside
  · rintro rfl
    refine ⟨disjoint_left.mpr (fun i hi hx => (mem_sdiff.mp hx).2 hi),?_⟩
    ext i
    change i∈s.val∪(univ \ s.val) ↔ i∈univ
    simp only [mem_union,mem_sdiff,mem_univ,true_and,or_not]

def weight (Q : Poly J) (s : (J).Mode) : ℂ := (inverseMass Q).part (complement s)
def total (F Q : Poly J) := F*inverseMass Q

/-- Includes all seven faces and the vacuum. The complementary-mode
coefficient belongs to the one pre-filed inverse ordinary table. -/
theorem affine (F Q : Poly J) :
    (total F Q).part full=∑ s : (J).Mode,weight Q s*F.part s := by
  classical
  simp only [total,Poly.part_mul,merges,Finset.sum_ite_eq',mem_univ,if_true,weight]
  exact sum_congr rfl fun _ _ => mul_comm .. 

theorem restore (F Q : Poly J) (qu : Q.part (J).quiet=1) : total F Q * Q=F := by
  unfold total
  rw [mul_assoc,mul_comm (inverseMass Q),right_inverse qu,mul_one]

theorem normed (F Q : Poly J) (fu : F.part (J).quiet=1) (qu : Q.part (J).quiet=1) :
    (total F Q).part (J).quiet=1 := by
  have eq := congrArg (fun x : Poly J => x.part (J).quiet) (restore F Q qu)
  simpa only [Poly.quiet_mul,qu,fu,mul_one] using eq

/-- Subtract the whole and trivial components before charging the terms of
degree two and three, so only proper measured residuals enter their price. -/
def proper (M : Poly J) := M-1-Poly.send full (M.part full)

private theorem away : full≠(J).quiet := by
  intro h
  have eq : (univ:Finset (Fin 3))=∅ := congrArg Subtype.val h
  exact univ_nonempty.ne_empty eq

private theorem annihilates (x : Poly J) (hx : x.part (J).quiet=0) (c : ℂ) :
    x*Poly.send full c=0 := by
  rw [←Poly.studs x,Finset.sum_mul]
  apply sum_eq_zero
  intro s _
  by_cases h : s=(J).quiet
  · rw [h,hx,Poly.send_zero,zero_mul]
  · by_contra bad
    obtain ⟨_,joined⟩ := merges_of_tagged_mul bad
    apply h
    apply Subtype.ext
    apply eq_empty_iff_forall_notMem.mpr
    exact fun i hi => Finset.disjoint_left.mp joined.1 hi (mem_univ _)

private theorem three (X : Poly J) :
    (∑ i∈range 3, (-((↑(i+1):ℂ))⁻¹) • (-X)^(i+1)) =
      X - (2:ℂ)⁻¹ • X^2 + (3:ℂ)⁻¹ • X^3 := by
  have even : (-X)^2=X^2 := by ring
  have odd : (-X)^3= -(X^3) := by ring
  norm_num [Finset.sum_range_succ,even,odd,sub_eq_add_neg]
  abel

/-- Exact normalized connected extraction on the three actual occupied
names. The sole linear remainder is the full quotient face. -/
theorem connected (F Q : Poly J) (fu : F.part (J).quiet=1) (qu : Q.part (J).quiet=1) :
    (Extra.Trajectories.connected F).part full - (Extra.Trajectories.connected Q).part full =
      (total F Q).part full - (2:ℂ)⁻¹*((proper (total F Q))^2).part full +
      (3:ℂ)⁻¹*((proper (total F Q))^3).part full := by
  let M := total F Q
  let D := M-1
  let T := Poly.send full (M.part full)
  let E := proper M
  have mu : M.part (J).quiet=1 := normed F Q fu qu
  have dz : D.part (J).quiet=0 := by simp [D,sub_eq_add_neg,mu]
  have tz : T.part (J).quiet=0 := by simp [T,Poly.part_send,Ne.symm away]
  have ez : E.part (J).quiet=0 := by
    change (D-T).part (J).quiet=0
    simp [sub_eq_add_neg,dz,tz]
  have fullD : D.part full=M.part full := by simp [D,sub_eq_add_neg,away]
  have clean : D*T=0 := annihilates D dz _
  have self : T*T=0 := annihilates T tz _
  have crossed : E*T=0 := annihilates E ez _
  have square : D^2=E^2 := by change D^2=(D-T)^2; linear_combination 2*clean-self
  have asSum : D=E+T := by change D=D-T+T; abel
  have cube : D^3=E^3 := by
    rw [pow_succ D 2,pow_succ E 2,square,asSum,mul_add]
    rw [show E^2*T=0 from by rw [pow_two,mul_assoc,crossed,mul_zero],add_zero]
  have glued := congrArg (fun x : Poly J => x.part full)
    (Comparison.RG02.connected_product mu qu)
  rw [restore F Q qu] at glued
  change (Extra.Trajectories.connected F).part full =
    (Extra.Trajectories.connected M).part full+(Extra.Trajectories.connected Q).part full at glued
  have cap : ∀ s : (J).Mode, s.val.card≤3 := fun s => by simpa using s.val.card_le_univ
  have series := log_to M mu 3 cap
  have linear : D.part full=M.part full := fullD
  calc
    _ = (Extra.Trajectories.connected M).part full := by rw [glued]; ring
    _ = (logTo 3 M).part full := congrArg (fun x : Poly J => x.part full) series
    _ = _ := by
      change (logTo 3 M).part full=M.part full - (2:ℂ)⁻¹*(E^2).part full+(3:ℂ)⁻¹*(E^3).part full
      have negD : 1-M= -D := by dsimp [D]; abel
      rw [logTo,negD,three,square,cube]
      change D.part full - (2:ℂ)⁻¹*(E^2).part full + (3:ℂ)⁻¹*(E^3).part full = _
      rw [linear]

end YM.Integration.WilsonThermometerCenteredAlgebra
