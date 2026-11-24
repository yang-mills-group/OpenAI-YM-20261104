import YM.Integration.FVA1Physical.Round2.MotionBasis

/-! Exact tensor decomposition of a physically calibrated mixed source
on the same positions and period, with a total coefficient mass bound
depending only on the finite field horizon and number of insertions. -/
set_option autoImplicit false
set_option maxHeartbeats 1900000
set_option maxRecDepth 4500
noncomputable section
namespace YM.Integration.FVA1Physical.Round2
open Function Finset Lattice RG YM.Wilson Source LocalLTE.Sail Extra.Histories Labels Next.Foundations
open RGComparison.Core16 Integration.FVA1Physical.Wilson
open scoped Classical BigOperators
variable {G : Gauge} {I : Type} [DecidableEq I] (B : Marker.Census I) {D : ℕ} (h : I → Fin (D+1))
    (s : B.Mode) (M : I → Motion) (v : ∀ i, ((frames G).level (h i).val).Coeff)
abbrev BasisChoice := (j : ↥s.val) → ((frames G).level (h j).val).Index
def basisWeight (t : BasisChoice (G:=G) B h s) : ℂ :=
  ∏ j : ↥s.val, (Motion.patch _ (M j) (v j)) (t j)
def basisOrbitCap (G : Gauge) (D : ℕ) := ∑ d : Fin (D+1), Motion.orbitCost ((frames G).level d.val)

theorem total_basis_weight [Fintype I] (unit : ∀ i, ((frames G).level (h i).val).coeffSize (v i) ≤ 1) :
    ∑ t, ‖basisWeight B h s M v t‖ ≤ (basisOrbitCap G D)^(Fintype.card I) := by
  have bounds (i : I) : Motion.orbitCost ((frames G).level (h i).val) ≤ basisOrbitCap G D :=
    single_le_sum (f:= fun d : Fin (D+1)=>Motion.orbitCost ((frames G).level d.val))
      (fun d _=>zero_le_one.trans (Motion.orbitCost_one_le _)) (mem_univ (h i))
  have atLeast : 1 ≤ basisOrbitCap G D := (Motion.orbitCost_one_le ((frames G).level 0)).trans
    (single_le_sum (f:=fun d : Fin (D+1)=>Motion.orbitCost ((frames G).level d.val))
      (fun d _=>zero_le_one.trans (Motion.orbitCost_one_le _)) (mem_univ (0:Fin (D+1))))
  calc
    _ = ∏ j : ↥s.val, ((frames G).level (h j).val).coeffSize (Motion.patch _ (M j) (v j)) := by
      simp only [basisWeight,norm_prod,Frame.coeffSize,Fintype.prod_sum]
    _ ≤ ∏ _j : ↥s.val,basisOrbitCap G D := Finset.prod_le_prod (fun i _=>Work.G08.size_nonneg ..)
      fun j _=>(Motion.patch_cost _ _ _).trans
        ((mul_le_of_le_one_right (zero_le_one.trans (Motion.orbitCost_one_le _)) (unit j)).trans (bounds j))
    _ ≤ _ := by
      rw [prod_const,card_univ,Fintype.card_coe]
      exact pow_le_pow_right₀ atLeast (card_le_univ _)

variable (A : StencilFamily G) (N n : ℕ) (o : ∀ j,I → Site (A.family.side j n))

def assignedBatch : Batch A.path N n I := ⟨fun i=>(h i).val,v,M,o⟩
def choiceLabels (t : BasisChoice (G:=G) B h s) : I → FieldLabel A.family D := fun j=>
  ⟨h j,if hj:j∈s.val then t ⟨j,hj⟩ else 0⟩

theorem mixed_basis_read (U : Config G (A.family.side N n)) :
    fullProduct (assignedBatch h M v A N n o).wavelengths s.val U =
      ∑ t, basisWeight B h s M v t * fullProduct (basisBatch A (choiceLabels B h s A t) N n o).wavelengths s.val U := by
  unfold fullProduct
  rw [←prod_attach]
  change (∏ j : ↥s.val, primProbe A.path N n (v j) (M j) (fun k=>o k j) U) = _
  calc
    _ = ∏ j : ↥s.val, ∑ k, (Motion.patch _ (M j) (v j)) k *
        primProbe A.path N n (Size.axis ((frames G).level (h j).val) k) Motion.nil (fun a=>o a j) U :=
      prod_congr rfl fun j _=>primProbe_basis A.path N n (M j) (fun a=>o a j) U (v j)
    _ = _ := ?_
  rw [Fintype.prod_sum]
  apply sum_congr rfl
  intro t _
  rw [prod_mul_distrib]
  apply congrArg (basisWeight B h s M v t * ·)
  calc
    _ = ∏ j : ↥s.val, (basisBatch A (choiceLabels B h s A t) N n o).wavelengths j U := by
      apply prod_congr rfl
      intro j _
      have leg : (choiceLabels B h s A t j.val).2 = t j := dif_pos j.property
      change primProbe A.path N n (Pi.single (t j) 1) Motion.nil (fun a=>o a j) U =
        primProbe A.path N n (Pi.single (choiceLabels B h s A t j.val).2 1) Motion.nil (fun a=>o a j) U
      rw [leg]
      rfl
    _ = _ := prod_attach s.val (fun j=>(basisBatch A (choiceLabels B h s A t) N n o).wavelengths j U)
end YM.Integration.FVA1Physical.Round2
