import YM.Integration.WilsonThermometerCenteredAlgebra
import YM.Integration.WilsonFiniteOrdinaryInverse

/-! Extract a proper ordinary face of the same complete three-field numerator from
two affordable inverse tables. Both tables preserve the original blank channel. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerRegisteredFaceTable
open Finset Marker QuadraticLocal Extra.Trajectories Comparison.RG02 Comparison.RG02.Order
open Primitives.GCC.Anchor WilsonThermometerCenteredAlgebra WilsonFiniteOrdinaryInverse
open scoped Classical BigOperators
local notation "J" => Stock.census (Fin 3)

def table (s:(J).Mode) (a:ℂ) : Poly J := 1-Poly.send s a

private theorem nil (s:(J).Mode) (live:s≠(J).quiet) (a:ℂ) :
    Poly.send s a*Poly.send s a=0 :=by
  by_contra bad
  obtain ⟨_,joins⟩:=merges_of_tagged_mul bad
  apply live
  apply Subtype.ext
  exact Finset.eq_empty_iff_forall_notMem.mpr (fun z hz=>(Finset.disjoint_left.mp joins.1 hz hz))

theorem inverse (s:(J).Mode) (live:s≠(J).quiet) (a:ℂ) :
    inverseMass (table s a)=1+Poly.send s a :=by
  let X:=Poly.send s a
  have square:X*X=0:=nil s live a
  have one:(1+X)*(1-X)=1:=by
    calc
      _ = 1-X*X := by ring
      _ = _ := by rw [square,sub_zero]
  have in₀:(table s a).part (J).quiet=1 := by
    change (1:Poly J).part (J).quiet-(Poly.send s a).part (J).quiet=1
    rw [Poly.part_send,if_neg (Ne.symm live),sub_zero];rfl
  calc
    _ = ((1+X)*(1-X))*inverseMass (table s a):=by rw [one,one_mul]
    _ = (1+X)*((table s a)*inverseMass (table s a)):=mul_assoc ..
    _ = _:=by rw [right_inverse in₀,mul_one]

@[simp] theorem unit : inverseMass (1:Poly J)=1 :=by
  simpa using (right_inverse (m:=(1:Poly J)) (by rfl))

private theorem reverse (s:(J).Mode) : complement (complement s)=s:=by
  apply Subtype.ext
  ext v
  simp [complement]

theorem ordinary (F:Poly J) (t:(J).Mode) (live:t≠(J).quiet) (a:ℂ) :
    (total F (table t a)).part full-(total F 1).part full=a*F.part (complement t):=by
  rw [affine,affine,←Finset.sum_sub_distrib]
  have pick(s:(J).Mode):complement s=t ↔ s=complement t := by
    constructor
    · intro h;simpa [reverse] using congrArg complement h
    · rintro rfl;exact reverse t
  simp only [weight,inverse t live,unit,Poly.part_plus,Poly.part_send,add_mul,add_sub_cancel_left,pick]
  simp only [ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true]

theorem room_two : (2:ℝ)≤fee (J) :=by
  have h:0≤room (J):=Finset.sum_nonneg (fun s _=>mul_nonneg (by norm_num) (Nat.cast_nonneg _))
  have a:(0:ℝ)≤(1+room (J))^2:=sq_nonneg _
  have b:(0:ℝ)≤(1+room (J))^3:=pow_nonneg (by linarith) _
  norm_num [fee,Finset.sum_range_succ] 
  linarith

theorem fixed (w:Fin 3→ℝ) (positive:∀ v,0<w v) (s:(J).Mode) (live:s≠(J).quiet) (a:ℂ)
    (admitted:Poly.toll w s*‖a‖≤1) :
    Poly.price w (inverseMass (1:Poly J))≤fee (J) ∧
    Poly.price w (inverseMass (table s a))≤fee (J) :=by
  rw [unit,inverse s live]
  have cap:=Poly.addition positive (1:Poly J) (Poly.send s a)
  simp only [Poly.one_price,Poly.solo] at cap ⊢
  exact ⟨le_trans (by norm_num) room_two,cap.trans (le_trans (add_le_add (le_refl (1:ℝ)) admitted) (by linarith only [room_two]))⟩

def amp (w:Fin 3→ℝ) (s:(J).Mode) : ℝ := (1+Poly.toll w s)⁻¹

theorem priced (w:Fin 3→ℝ) (positive:∀ v,0<w v) (s:(J).Mode) (live:s≠(J).quiet) :
    0<amp w s ∧ Poly.price w (inverseMass (1:Poly J))≤fee (J) ∧
    Poly.price w (inverseMass (table s (amp w s)))≤fee (J) :=by
  have h:=Poly.worth positive s
  have g:0<1+Poly.toll w s:=by linarith
  have g₀:0<amp w s:=inv_pos.mpr g
  refine ⟨g₀,fixed w positive s live _ ?_⟩
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos g₀]
  change Poly.toll w s*(1+Poly.toll w s)⁻¹≤1
  rw [←div_eq_mul_inv,div_le_one g]
  linarith

end YM.Integration.WilsonThermometerRegisteredFaceTable
