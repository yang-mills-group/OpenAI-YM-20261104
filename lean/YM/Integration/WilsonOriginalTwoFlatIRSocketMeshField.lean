import YM.Integration.WilsonOriginalTwoFlatRoseCentered
import YM.Integration.WilsonOriginalTwoFlatRoseFaceLimits
import YM.Integration.WilsonSeparatedPrefixCellProfile
import YM.Integration.WilsonReflectedPublicAlignedPoints
import YM.Integration.WilsonReceivedChronologicalFixedRoseVariation

/-! A nonzero absolute compact-test cell evaluates the original Wilson product
at the same point in a fixed thickening of the continuum support. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRSocketMeshField
open Function Set Filter Finset Metric MeasureTheory Lattice Extraction OPE RG Wilson Source
open PhysicalNext.Repeat.Legato WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open WilsonOriginalTwoFlatRoseFaceLimits (raw)
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)
local notation "C" => R.family

theorem original (φ:Test 3){r τ:ℝ}(rp:0<r){f N per:ℕ}(live:f≤N)
    (mesh:4*(3:ℝ)*(C).S.a f≤τ*r)(cell:WilsonReceivedChronologicalFixedRoseVariation.cells R φ r (f,per)):
    ∃x∈cthickening τ (tsupport (φ:Points 3→ℂ)),∀A:Group C 6,∀s:Finset (Fin 3),
      WilsonOriginalTwoFlatRoseCentered.ordinary R A N per
        (fun i=>((C).S.toDepth live per).embed (cell.val i)) s=raw R A r (N,per) x s:=by
  obtain ⟨x,placed,hit⟩:=WilsonSeparatedPrefixCellProfile.active φ ((C).S.a f) r ((C).side f per)
    ((C).S.a_pos f) cell.val (WilsonReceivedChronologicalFixedRoseVariation.charged R φ r (f,per) cell)
  let o:=address ((C).S.a f) (r • x)
  let y:=r⁻¹ • tag ((C).S.a f) o
  have actual:r • y=tag ((C).S.a f) o:=by simp [y,smul_smul,rp.ne']
  have err:=Extraction.approximate ((C).S.a_pos f) (r • x)
  have scale:dist (tag ((C).S.a f) o) (r • x)=r*dist y x:=by
    rw [←actual,dist_eq_norm,←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos rp,dist_eq_norm]
  have near:dist y x≤τ:=(mul_le_mul_iff_right₀ rp).mp (by rw [←scale];exact err.trans (mesh.trans_eq (mul_comm _ _)))
  refine ⟨y,mem_cthickening_of_dist_le y x τ _ (subset_tsupport _ hit) near,?_⟩
  intro A s
  have pins(i:Fin 3):wrap ((C).side N per) (address ((C).S.a N) (r • y) i)=((C).S.toDepth live per).embed (cell.val i):=by
    have atF:wrap ((C).side f per) (o i)=cell.val i:=congrFun placed i
    rw [actual,←atF]
    exact WilsonReflectedPublicAlignedPoints.grid R live per o i
  unfold WilsonOriginalTwoFlatRoseCentered.ordinary WilsonOriginalTwoFlatRoseFaceLimits.raw
  congr 1
  funext U
  apply Finset.prod_congr rfl
  intro i _
  dsimp only [Function.comp_apply]
  rw [pins i]

end YM.Integration.WilsonOriginalTwoFlatIRSocketMeshField
end
