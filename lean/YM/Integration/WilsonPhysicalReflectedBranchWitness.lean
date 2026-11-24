import YM.Integration.WilsonPhysicalPositiveHome
import Mathlib.GroupTheory.CosetCover

/-! One real input separates a finite family of nonidentity transformations of
the retained public field basis. Its separation has a strict ε₀ in the
actual reflected Maxwell form at the already fixed two-point positions. -/

noncomputable section
namespace YM.Integration.WilsonPhysicalReflectedBranchWitness
open Function Finset Set Filter WilsonPositionProgramPublicContrast WilsonPositionProgramPublicWickGram
open WilsonPhysicalPositiveHome (appointed)
open Lattice Wilson RG Source FVA2 FVA2.Register Maxwell Maxwell.Wick MS MS.Menus MS.Land MS.Theater Local.Physical
open scoped Classical BigOperators Topology
variable {I:Type}[Fintype I]{P:Type}[Fintype P]

omit [Fintype I] in
theorem direction (k:P→Module.End ℝ (I→ℝ))(moves:∀i,k i≠LinearMap.id):
    ∃v:I→ℝ,∀i,k i v≠v:=by
  classical
  by_contra! all
  let fixed:=fun i:P=>(k i-LinearMap.id).ker
  have cover:(⋃i,(fixed i:Set (I→ℝ)))=Set.univ:=by
    apply Set.eq_univ_of_forall
    intro v
    obtain ⟨i,hit⟩:=all v
    apply Set.mem_iUnion.mpr
    refine ⟨i,?_⟩
    change k i v-v=0
    exact sub_eq_zero.mpr hit
  obtain ⟨i,whole⟩:=Subspace.exists_eq_top_of_iUnion_eq_univ cover
  exact moves i (sub_eq_zero.mp (LinearMap.ker_eq_top.mp whole))

def realColumn (v:I→ℝ):I→ℂ:=fun i=>(v i:ℂ)

theorem original {G:Gauge}(B:Local.Physical.Deck G)(h:ℕ)(a:Axis)
    (k:P→Module.End ℝ (Glyph B h→ℝ))(moves:∀i,k i≠LinearMap.id):
    ∃v:Glyph B h→ℝ,∃ε₀:ℝ,0<ε₀ ∧ ∀i,
      4*ε₀≤(assay (realColumn v-realColumn (k i v)) (realColumn v-realColumn (k i v))
        (reading a (nodes a) (id:Glyph B h→Glyph B h))).re:=by
  classical
  obtain ⟨v,apart⟩:=direction k moves
  let floor:=appointed B h a
  let gap:=fun i:P=>floor.k*‖realColumn v-realColumn (k i v)‖^2
  have pos(i:P):0<gap i:=by
    have ne:realColumn v-realColumn (k i v)≠0:=by
      intro flat
      apply apart i
      have same:=sub_eq_zero.mp flat
      funext j
      have hj:= (congrFun same j).symm
      change (((k i v) j:ℝ):ℂ)=((v j:ℝ):ℂ) at hj
      exact Complex.ofReal_inj.mp hj
    exact mul_pos floor.positive (pow_pos (norm_pos_iff.mpr ne) 2)
  let bills:=insert (1:ℝ) (Finset.univ.image gap)
  have live:bills.Nonempty:=Finset.insert_nonempty ..
  have mp:0<bills.min' live:=by
    obtain eq|fromIndex:=Finset.mem_insert.mp (Finset.min'_mem bills live)
    · rw [eq];exact zero_lt_one
    · obtain ⟨i,_,eq⟩:=Finset.mem_image.mp fromIndex
      rw [←eq];exact pos i
  refine ⟨v,bills.min' live/4,by positivity,fun i=>?_⟩
  have best:bills.min' live≤gap i:=Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem gap (Finset.mem_univ i)))
  have actual:=floor.paid (reading a (nodes a) (id:Glyph B h→Glyph B h))
    (by simpa only [sub_self,norm_zero] using floor.aperture.le) (realColumn v-realColumn (k i v))
  rw [show 4*(bills.min' live/4)=bills.min' live by ring]
  exact best.trans actual

end YM.Integration.WilsonPhysicalReflectedBranchWitness
