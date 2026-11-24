import YM.Integration.WilsonOriginalOrdinaryFlatHulls
import YM.Integration.WilsonEmittedFiledCatalogue

/-! Change the numerical Laurent units of one filed crop while preserving
its actual two group functions, guard, derivatives and long tail. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalFiledRowScale
open Function Finset Lattice RG Wilson Marker QuadraticLocal
open Comparison.Density Comparison.Density.Mirrors Comparison.Density.Transport
open AnalyticBridge.SectorAffine.Offset WilsonOriginalOrdinaryFlatHulls
open scoped Topology BigOperators ContDiff
variable {G:Gauge}{n:Side}{p:BudgetPoint}{link:LinkTube G}{o:Site n}
  {f h F H:Config G n→ℂ}

def priced (r:Row p link o f h)(c:ℝ)(same:F-H=c • (f-h)):Row p link o F H where
  tail:=c • r.tail
  retained:=r.retained
  depth:=r.depth
  width:=r.width
  jet:=|c| *r.jet
  high:=|c| *r.high
  tailJet:=|c| *r.tailJet
  tailValue:=|c| *r.tailValue
  crop:=by
    have short:F-H-c • r.tail=c • (f-h-r.tail):=by rw [same,smul_sub c (f-h) r.tail]
    have full:(F-H) ∘ increment 1=fun A=>c • ((f-h) ∘ increment 1) A:=by rw [same];rfl
    obtain ⟨k,hk,uniform⟩:=r.crop.radius
    refine ⟨⟨k,hk,?_⟩,?_,r.crop.room,r.crop.order,?_,?_,?_,?_,?_,mul_nonneg (abs_nonneg _) r.crop.nonnegative⟩
    · rw [short]
      intro U V sameField
      exact congrArg (fun a:ℂ=>c • a) (uniform U V sameField)
    · rw [short]
      intro z U
      exact congrArg (fun a:ℂ=>c • a) (r.crop.ward z U)
    · intro A hA
      rw [short]
      exact (r.crop.salary A hA).scale c
    · rw [full]
      exact r.crop.smooth.const_smul c
    · intro i hi
      rw [full,iteratedFDeriv_const_smul_apply' (a:=c)
        (r.crop.smooth.of_le (by exact_mod_cast (hi.le.trans r.crop.order))),norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (r.crop.low i hi) (abs_nonneg _)
    · exact r.crop.long.scale c
    · intro U
      simp only [Pi.smul_apply,norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (r.crop.outside U) (abs_nonneg _)

theorem price (r:Row p link o f h)(c:ℝ)(same:F-H=c • (f-h)):
    (priced r c same).price=|c| *r.price:=by
  dsimp only [priced,Row.price]
  ring

end YM.Integration.WilsonOriginalFiledRowScale
end
