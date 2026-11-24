import YM.Integration.FVA1Physical.Round2.CP5PhysicalFleet
import YM.Integration.FVA1Physical.Round2.CP5EngineeringRow

/-! A pre-period analytic input with the actual graded field insertions.
Each rank-r monomial in a field of grade h burns the same g^(-h) and
retains its original footprint and independent positional test. The fees
and their positivity are inherited from the unscaled physical atoms. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.CP5
open Function Finset Lattice YM.Wilson RG Source Labels Marker QuadraticLocal.Earn QuadraticLocal.Affinity
open Next.Foundations YM.Integration.FVA1Physical.Round2.Curvature
open scoped Classical BigOperators
variable {G:Gauge} {I:Type} [Fintype I] [DecidableEq I] {d:ℕ}
variable {E:I→Type} [∀ i,AddCommGroup (E i)] [∀ i,Module ℝ (E i)]

def nativeGrade (a:CoverLabel G d) := (((frames G).level a.1.val).grades a.2).2

theorem engineering_fleet (J:Census I) (a:I → CoverLabel G d) (σ:ℝ)
    (test:∀ i,E i→ₗ[ℝ]ℂ) (A:∀ i,Set (E i)) (bounded:∀ i x,x∈A i→‖test i x‖≤1) :
    ∃ w:ℝ, 0<w ∧
      ∀ (n:Side) (o:I→Site n), ∃ X:(Σ i,Fin (fieldCount (a i)))→Row (stencilPassport a o) J G (Wallet A),
      Scene.Armada X (fun _=>w) (fun i=>fieldToll (nativeGrade (a i))) σ 1 (fieldHorizon a)
          (Fintype.card I) (∑ i,fieldToll (nativeGrade (a i))) ∧
      Tableau (fun i=>(test i).ker) A X ∧
      (∀ i t (g:ℝ) (U:Config G n),
        (((g^(nativeGrade (a i)))⁻¹:ℝ):ℂ) * (test i (t i).val *
          (localSection G (a i).1.val).places (Pi.single (a i).2 1) (o i) U) =
          ∑ j:Fin (fieldCount (a i)),(X ⟨i,j⟩).nominal g t U) ∧
      (∀ p,(X p).mode=J.fire p.1) := by
  obtain ⟨w,hw,base⟩ := physical_analytic_fleet J a σ test A bounded
  refine ⟨w,hw,fun n o=>?_⟩
  obtain ⟨M,pay,table,read,modes⟩ := base n o
  let X (p:Σ i,Fin (fieldCount (a i))) := engineeringRow (M p) (nativeGrade (a p.1)) (modes p).2.1
  refine ⟨X,?_,⟨fun p=>table.bill p⟩,?_,fun p=>(modes p).1⟩
  · refine ⟨⟨pay.quota,fun s=>sum_le_sum_of_subset_of_nonneg (subset_univ s.val) (fun i _ _=>Nat.zero_le _)⟩,
      pay.positive,pay.suggests,⟨pay.purchases.spend,fun p=>⟨?_,?_⟩⟩,pay.honor⟩
    · exact (Nat.sub_le _ _).trans ((modes p).2.2 ▸ (pay.purchases.usable p).1)
    · change fieldToll (nativeGrade (a p.1)) = ∑ i∈(M p).mode.val,fieldToll (nativeGrade (a i))
      rw [(modes p).1]
      simp [Census.fire]
  intro i t g U
  rw [read,Finset.mul_sum]
  apply sum_congr rfl
  intro j _
  exact (engineering_payload _ _ _ (modes ⟨i,j⟩).2.2 g t U).symm

end YM.Integration.FVA1Physical.Round2.CP5
