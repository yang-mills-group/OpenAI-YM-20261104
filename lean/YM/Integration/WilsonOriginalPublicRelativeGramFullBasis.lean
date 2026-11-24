import YM.Integration.WilsonOriginalPublicRelativeGramFreePanel

/-! The original public horizon has a single genuine reflected determining
family before any signed accuracy, on every cutoff sequence realizing the
screened placements. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.Integration.WilsonOriginalPublicRelativeGramFullBasis
open Filter Finset Function Lattice Wilson RG Source Labels PhysicalNext.Repeat.Legato
open Extraction Extraction.Banks RG17 Spec Table Table.Pairing Climb
open XSpace XSpace.Normalize XSpace.Structure1 Maxwell Maxwell.Wick MS MS.Menus MS.Land MS.Theater Local.Physical
open WilsonOriginalPublicRelativeGramFreePanel (named incidence pointsAt)
open WilsonOriginalPublicRelativeGramPins (matrix)
open WilsonPositionProgramPublicWickGram (reading nodes vertex)
open scoped Classical Topology BigOperators Matrix Matrix.Norms.Operator
variable {G:Gauge}(B:Local.Physical.Deck G)(h:ℕ)(a:Axis)

theorem original {L Z:Type}[Fintype L]:
    ∃K:ℝ,0<K ∧ ∀(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Spec.Final R.family f S)
    (J:ℝ→PhysMS.tower S)(l:Filter Z)(r:Z→ℝ)(site:Z→ℕ)(addresses:Z→L→Fin 2→ Cover)
    (weight:Z→L→ℂ)(μ:L→ℂ)(shape:Z→L→Points 2),
    PhysMS.Leading F J → Tendsto r l (𝓝[>] (0:ℝ)) →
    (∀ᶠ z in l,∀m,Extraction.Order.grid R.family (site z) (addresses z m)=r z • shape z m) →
    (∀m,Tendsto (fun z=>shape z m) l (𝓝 (pointsAt a))) →
    (∀m,Tendsto (fun z=>weight z m) l (𝓝 (μ m))) → ∑m,μ m=1 →
    ∀ᶠ z in l,let M:=matrix R F a (fun _:Glyph B h=>h) J (fun i=>named R B h i) (r z) (r z) (site z) (addresses z) (weight z) false
      IsUnit M.det ∧ ‖M⁻¹‖≤K:=by
  classical
  obtain ⟨K,kp,rank⟩:=WilsonOriginalPublicRelativeGramRank.original (L:=L) (Z:=Z)
    a (id:Glyph B h→Glyph B h) injective_id
  refine ⟨K,kp,?_⟩
  intro R f S F J l r site addresses weight μ shape lead fine placed pin mass total
  have pos:vertex a≠-(vertex a):=by
    intro eq
    have bad:=congrArg norm ((WilsonPositionProgramPublicWickGram.apart a).symm.trans (sub_eq_zero.mpr eq))
    simp [basis_norm] at bad
  have ident: (fun i j=>WilsonOriginalPublicRelativeGramLeading.free R a (fun _:Glyph B h=>h)
      (fun t=>named R B h t) (fun _:L=>pointsAt a) μ i j)=reading a (nodes a) (id:Glyph B h→Glyph B h):=by
    funext i j
    change (∑m,μ m*PhysMS.WickGoal (C:=R.family)
      (WilsonOriginalPublicRelativeGramLeading.fields R a (fun _:Glyph B h=>h) (fun t=>named R B h t) i j)
      (pointsAt a))=_
    rw [←Finset.sum_mul, total,one_mul]
    exact incidence R B h a i j
  have trueRank:=rank R F (fun _:Glyph B h=>h) J (fun i=>named R B h i) l r site addresses weight
    shape (fun _=>pointsAt a) μ lead fine placed pin (fun _=>Extra.FD.couple_ok (Ne.symm pos)) mass ident
  filter_upwards [trueRank] with z fund
  dsimp only at fund ⊢
  convert fund using 1 <;> congr! 4

end YM.Integration.WilsonOriginalPublicRelativeGramFullBasis
