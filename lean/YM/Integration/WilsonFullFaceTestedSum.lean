import YM.Integration.WilsonThermometerAncestralCapture
import YM.Extra.SOURCE_HISTORIES.Unit
import YM.Extra.SOURCE_HISTORIES.Pencil

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonFullFaceTestedSum
open Finset MeasureTheory Lattice Wilson RG Labels Source Extra.Histories
open scoped BigOperators

theorem cells {ι : Type*} [Fintype ι] {G:Gauge} {n:Side} {d:ℕ} {F:Frame G d}
    (P:Rep G n) (B:SectionData F) (Y:Hol G) (y:Site n) {κ σ c Λ δ η : ℝ}
    (hk:0<κ) (law:P.Lawful σ c Λ δ η) (mass:ι → ℂ)
    (actual filed:ι → Config G n → ℂ) (H:ι → Coefficient F n) {fare sizeBill:ℝ}
    (fmt:∀j,(H j).Format y Y P) (cost:∀j,(H j).remBound y P κ fare)
    (sizes:∀j,F.coeffSize (H j).x ≤ sizeBill)
    (reads:∀j U,(H j).density y B P U=actual j U-(P.eval U:ℂ)*filed j U) :
    ∃h:Coefficient F n,h.Format y Y P ∧ h.remBound y P κ ((∑j,‖mass j‖)*fare) ∧
    F.coeffSize h.x ≤ (∑j,‖mass j‖)*sizeBill ∧
    ∀U,h.density y B P U=(∑j,mass j*actual j U)-(P.eval U:ℂ)*(∑j,mass j*filed j U) := by
  classical
  rcases isEmpty_or_nonempty ι with h | h
  · letI:IsEmpty ι:=h
    refine ⟨primary y (0:F.Coeff),primary_format _,?_,?_,?_⟩
    · simpa using (primary_rem (o:=y) (R:=P) (0:F.Coeff) hk)
    · simp [primary,Frame.coeffSize]
    · intro U
      simp [primary_density]
  · letI:Nonempty ι:=h
    let part (j:ι):=stretch (mass j) (H j)
    have bill (j:ι):(part j).remBound y P κ (‖mass j‖*fare):=stretch_rem _ (cost j)
    let whole:=merge (code ι) part
    refine ⟨whole,merge_format (code ι) part (fun j=>stretch_format _ (fmt j)),?_,?_,?_⟩
    · have paid:=(merge_budget (code ι) part hk bill (hasSum_fintype _).summable).1
      simpa only [tsum_fintype,Finset.sum_mul] using paid
    · have coord:whole.x=∑j,mass j • (H j).x:=tsum_fintype _
      rw [coord]
      refine (Size.finite F univ (fun j=>mass j • (H j).x)).trans ?_
      rw [Finset.sum_mul]
      apply sum_le_sum
      intro j _
      simpa only [Frame.coeffSize,Pi.smul_apply,norm_smul,←Finset.mul_sum] using
        (mul_le_mul_of_nonneg_left (sizes j) (norm_nonneg (mass j)))
    · intro U
      have series:=merge_density (code ι) part hk law bill (hasSum_fintype _).summable
        (hasSum_fintype _).summable B U
      change (merge (code ι) part).density y B P U=_
      rw [←series.tsum_eq,tsum_fintype,Finset.mul_sum,←Finset.sum_sub_distrib]
      apply sum_congr rfl
      intro j _
      rw [show (part j).density y B P U=mass j*(H j).density y B P U from
        stretch_density B P y (mass j) (H j) U,reads]
      ring

end YM.Integration.WilsonFullFaceTestedSum
