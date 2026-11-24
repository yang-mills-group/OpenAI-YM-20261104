import YM.Integration.WilsonOriginalPublicFigureCatalogue

/-! The complete numerical bill of the pole-cleared physical trial in the
independent catalogue. Its signed change is paid only after the two rows are compared. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
namespace YM.Integration.WilsonOriginalPublicFigureCharges
open Finset Lattice Wilson RG Labels PhysicalNext.Repeat.Legato PowerSeries
open WilsonPositionProgramInversionMaterial (Axes)
open WilsonPositionProgramSeriesRead (Terms)
open WilsonOriginalPublicFigureCatalogue (plain filed)
open WilsonThermometerPositionTunedSlope (Columns)
open WilsonOriginalMicroscopicGuardedPageSchool (Indexed)
open WilsonOriginalPublicTrialInput (salary vector fitted)
open scoped Classical ENNReal BigOperators
variable {G:Gauge}(R:Run G){I:Type}[Fintype I][LinearOrder I](d:I → ℕ)
local notation "F" i:max =>R.family.labels.level (d i)
def charge (q:ℕ)(ζ:Axes R d → PowerSeries ℂ):ℝ≥0∞:=
  ∑u:Terms R d q,‖WilsonPositionProgramSeriesRead.weight R d q ζ u‖ₑ

theorem difference (q:ℕ)(Z T:Axes R d → PowerSeries ℂ):
    charge R d q (fun a=>Z a-T a) ≤ charge R d q Z+charge R d q T:=by
  rw [charge,charge,charge,←sum_add_distrib]
  apply sum_le_sum
  intro u _
  simp only [WilsonPositionProgramSeriesRead.weight,map_sub]
  exact enorm_sub_le .. 

variable (grades j:Fin 3→ℕ)(K target:ℕ)(η:ℝ)(M:Fin 3→ℝ)(Y:∀a:Fin 3,ℕ×ℕ→R.family.label (grades a))
    (before:∀a,j a≤K)(registered:Indexed R grades j target η M Y)(child:I→Fin 3)
local notation "d₀" => grades ∘ child
def bill (q:ℕ):ℝ≥0∞:=
  (Fintype.card (Terms R d₀ q):ℝ≥0∞)*Fintype.card (Columns R d₀)*
    ENNReal.ofReal (∏i,2^WilsonOriginalPublicFigureIncome.height R (d₀ i)*salary R grades j K η M (child i))

theorem funded (N per:ℕ)(live:K<N)(q:ℕ):
    let v:=fun i:I=>vector R grades j K target η M Y before registered N per (child i)
    charge R d₀ q (filed R d₀ v) ≤ bill R grades j K η M child q:=by
  intro v
  let cap:=∏i,2^WilsonOriginalPublicFigureIncome.height R (d₀ i)*salary R grades j K η M (child i)
  have head:=(WilsonOriginalPublicTrialInput.original R grades j K target η M Y before registered N per live).1
  have stone (b:Columns R d₀):‖∏i,v i (b i)‖ ≤ cap:=by
    rw [norm_prod]
    apply prod_le_prod (fun _ _=>norm_nonneg _)
    intro i _
    have cut:‖v i (b i)‖≤(R.family.labels.level (d₀ i)).coeffSize (v i):=by
      exact Finset.single_le_sum (f:=fun a=>‖v i a‖) (fun a _=>norm_nonneg _) (mem_univ (b i))
    refine cut.trans ?_
    simp only [v,vector,if_pos live]
    exact (WilsonPositionProgramReportedField.purchased R (d₀ i) K (N,per) live.le _).trans
      (mul_le_mul_of_nonneg_left (head (child i)).2 (by positivity))
  let bnd:=(Fintype.card (Columns R d₀):ℝ≥0∞)*ENNReal.ofReal cap
  have row(u:Terms R d₀ q):‖WilsonPositionProgramSeriesRead.weight R d₀ q (filed R d₀ v) u‖ₑ ≤ bnd:=by
    rw [WilsonPositionProgramSeriesRead.weight,filed,map_sum]
    calc
      _ ≤ ∑b:Columns R d₀,‖coeff u.2.val.1 (if plain R d₀ b=u.1 then
          PowerSeries.C (∏i:I,v i (b i)) else 0)‖ₑ:=enorm_sum_le ..
      _ ≤ ∑_:Columns R d₀,ENNReal.ofReal cap:=by
        apply sum_le_sum
        intro b _
        split
        · rw [coeff_C]
          split
          · rw [←ofReal_norm];exact ENNReal.ofReal_le_ofReal (stone b)
          · simp
        · simp
      _ = _ :=by simp [bnd,nsmul_eq_mul]
  exact (sum_le_sum (fun u _=>row u)).trans_eq (by simp [bill,bnd,cap,nsmul_eq_mul,mul_assoc])

end YM.Integration.WilsonOriginalPublicFigureCharges
end
