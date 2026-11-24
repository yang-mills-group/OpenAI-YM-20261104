import YM.Integration.WilsonOriginalGalleryTwinBoard
import YM.Integration.WilsonMeasuredCompanionSoft

/-! The true field-independent peer factor spends only the original rooted wages of its marks. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCompanionClearRange
open Function Finset Lattice Wilson RG Labels Source Marker Multi QuadraticLocal QuadraticLocal.Earn Ac Push GridApprox.Nil
open MergeProof MergeProof.Accent Extra.Histories Extra.Trajectories Lodestar WilsonOriginalGalleryTwins
open private ordinary from YM.Integration.WilsonFullFaceSignedUnit
open private silent from YM.Integration.WilsonOriginalGalleryTwinBoard
open scoped Classical BigOperators
local notation "J" => Stock.census (Fin 3)
def ceiling:ℝ:=(Fintype.card (parts (J)).Mode:ℝ)*3^3
variable {G:Gauge}{n:Side}{T I:Type}{P:Rep G n}{o:Fin 3→Site n}
theorem upper (A:Gallery T I o P (J))(x:T)(w:Fin 3→ℝ)(pos:∀i,0<w i){a:ℝ}(expo:0≤a)
    (earned:A.E.Paid (fun i=>w i^2) P.p.B a 1):
    ∀s:(Marks (Fin 3×Bool)).Mode,Poly.toll (w ∘ Prod.fst) s*
      ‖(duplicate (Fin 3) (Poly.pass (clear A x))).part s‖≤ceiling:=by
  have wp(i):0<w i^2:=pow_pos (pos i) _
  have value:=WilsonPhysicalHistoryGroupedClear.priced A.E (fun i=>w i^2) wp expo earned x
  have bound:Poly.price (fun i=>w i^2) (clear A x)≤3:=by simpa [clear] using value
  intro s
  by_cases live:∃t,s=two t
  · obtain ⟨t,rfl⟩:=live
    rw [two_toll,seal_part]
    apply ordinary (fun i=>w i^2) wp t _ (silent A x w pos expo earned) (by norm_num : (1:ℝ)≤3)
    intro u
    exact (Poly.member wp u.val _).trans bound
  · rw [seal_miss _ s (fun t h=>live ⟨t,h⟩)]
    simp only [norm_zero,mul_zero]
    unfold ceiling
    positivity

variable {V:Type}[DecidableEq V]{J':Census V}
theorem product (w:V→ℝ)(pos:∀i,0<w i)(left right:Poly J'){C D:ℝ}(cp:0≤C)(dp:0≤D)
    (hc:∀j,Poly.toll w j*‖left.part j‖≤C)(hd:∀j,Poly.toll w j*‖right.part j‖≤D)
    (s:J'.Mode):
    Poly.toll w s*‖(left*right).part s‖≤(Fintype.card J'.Mode:ℝ)^2*C*D:=by
  let item(i j:J'.Mode):ℂ:=if Poly.merges i j s then left.part i*right.part j else 0
  have each(i j:J'.Mode):Poly.toll w s*‖item i j‖≤C*D:=by
    unfold item
    split
    · rename_i merge
      have weight:Poly.toll w s=Poly.toll w i*Poly.toll w j:=by
        unfold Poly.toll
        rw [←merge.2,prod_union merge.1]
      rw [weight,norm_mul]
      calc _=(Poly.toll w i*‖left.part i‖)*(Poly.toll w j*‖right.part j‖):=by ring
           _≤C*D:=mul_le_mul (hc i) (hd j)
             (mul_nonneg (Poly.worth pos _).le (norm_nonneg _)) cp
    · simpa only [norm_zero,mul_zero] using mul_nonneg cp dp
  calc _≤Poly.toll w s*(∑i,∑j,‖item i j‖):=by
          rw [Poly.part_mul]
          apply mul_le_mul_of_nonneg_left _ (Poly.worth pos _).le
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _=>norm_sum_le _ _)
       _=∑i,∑j,Poly.toll w s*‖item i j‖:=by simp only [Finset.mul_sum]
       _≤∑_i:J'.Mode,∑_j:J'.Mode,C*D:=Finset.sum_le_sum fun i _=>
             Finset.sum_le_sum fun j _=>each i j
       _=_:=by simp only [sum_const,card_univ,nsmul_eq_mul];ring

end YM.Integration.WilsonOriginalCompanionClearRange
end
