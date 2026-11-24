import YM.Integration.WilsonOriginalPublicRelativeGramLeading

/-! The free reflected detector fixes the inverse tariff before any signed
order. The original reference points may be individually screened. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicRelativeGramRank
open Filter Finset Function Lattice Wilson RG Source Labels PhysicalNext.Repeat.Legato
open Extraction Extraction.Banks Spec Table Table.Pairing Climb
open XSpace XSpace.Normalize XSpace.Structure1 Maxwell Maxwell.Wick MS MS.Menus MS.Land MS.Theater Local.Physical
open WilsonOriginalPublicRelativeGramPins (matrix)
open WilsonOriginalPublicRelativeGramLeading (free)
open WilsonPositionProgramPublicWickGram (reading nodes)
open scoped Classical Topology BigOperators Matrix Matrix.Norms.Operator
variable {G:Gauge}{I:Type}[Fintype I]{B:Local.Physical.Deck G}{h:ℕ}
  (a:Axis)(leg:I→Glyph B h)(independent:Injective leg)

include independent in
theorem original {L Z:Type}[Fintype L]:
    ∃K:ℝ,0<K ∧ ∀(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Spec.Final R.family f S)
    (d:I→ℕ)(J:ℝ→PhysMS.tower S)(w:(i:I)→(Spin.comparator R.family.book).Field (d i))
    (l:Filter Z)(r:Z→ℝ)(site:Z→ℕ)(addresses:Z→L→Fin 2→ Cover)(weight:Z→L→ℂ)
    (shape:Z→L→Points 2)(limit:L→Points 2)(μ:L→ℂ),PhysMS.Leading F J → Tendsto r l (𝓝[>] (0:ℝ)) →
    (∀ᶠ z in l,∀m,Extraction.Order.grid R.family (site z) (addresses z m)=r z • shape z m) →
    (∀m,Tendsto (fun z=>shape z m) l (𝓝 (limit m))) → (∀m,limit m∈conf 2) →
    (∀m,Tendsto (fun z=>weight z m) l (𝓝 (μ m))) →
    (fun i j=>free R a d w limit μ i j)=reading a (nodes a) leg →
    ∀ᶠ z in l,let M:=matrix R F a d J w (r z) (r z) (site z) (addresses z) (weight z) false
      IsUnit M.det ∧ ‖M⁻¹‖≤K:=by
  classical
  obtain ⟨k,δ,kp,dp,pass⟩:=WilsonOriginalPublicRelativeGramReference.original a leg independent
  let bound:ℝ:=∑_i:I,∑_j:I,(Fintype.card I:ℝ)/k
  have nn:0≤bound:=by dsimp [bound]; positivity
  refine ⟨bound+1,by linarith,?_⟩
  intro R f S F d J w l r site addresses weight shape limit μ lead small placed position clear mass identified
  let actual:=fun z=>matrix R F a d J w (r z) (r z) (site z) (addresses z) (weight z) false
  have cv:Tendsto (fun z i j=>actual z i j) l (𝓝 (reading a (nodes a) leg)):=by
    rw [←identified]
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    exact WilsonOriginalPublicRelativeGramLeading.original R F a d J w r site addresses weight shape limit μ lead small placed position clear mass i j
  filter_upwards [(Metric.tendsto_nhds.mp cv) δ dp] with z near
  have sell:=pass (actual z) (by simpa only [dist_eq_norm] using near.le)
  exact ⟨sell.1,sell.2.trans (by linarith)⟩

end YM.Integration.WilsonOriginalPublicRelativeGramRank
