import YM.Integration.WilsonOriginalNullColumnSplit
import YM.Integration.WilsonMatrixOriginalGermBasis
import YM.Trace.Physicalv2.GermSplit

/-! Recover a unique complex-linear physical germ from all held
group fields on one received Wilson carrier and one actual site.
Independent choices of native hard presentations give the same map. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullPlacedGermMap
open Function Filter Lattice RG Wilson Source Labels Extra.Histories Extra.Histories.Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open scoped Classical Topology BigOperators
variable {G:Gauge} (C:Family G) (d N p i:ℕ) (o:Site (C.side i p))
local notation "F₀" => C.labels.level d
local notation "S₀" => C.localSection d
local notation "P₀" => C.path.rep N p i
local notation "Ω" => Config G (C.side i p) → ℂ

structure Printed (q:Coefficient F₀ (C.side i p)) (f:Ω) : Prop where
  form : q.Format o C.params P₀
  bought : ∃ B:ℝ,q.remBound o P₀ (safety C i) B
  fields : q.density o S₀ P₀=f

theorem intrinsic (H:C.Makes) (home:Opened C d i p) (live:i ≤ N) {q v:Coefficient F₀ (C.side i p)} {f:Ω}
    (first:Printed C d N p i o q f) (other:Printed C d N p i o v f) :
    projection F₀ C.params (P₀).p.threshold o q=projection F₀ C.params (P₀).p.threshold o v := by
  obtain ⟨a,fa⟩:=first.bought
  obtain ⟨b,fb⟩:=other.bought
  have terms:=dimensions d N p i H home.post live
  exact Germ.intrinsic_at F₀ C.params S₀ (H.sections d) o (H.places d i p home.post) terms.1 terms.2
    (ProjectorNext.Equivariance.sections_visit H home.post o) q v first.form other.form ⟨_,a,fa⟩ ⟨_,b,fb⟩
    (Filter.EventuallyEq.of_eq (first.fields.trans other.fields.symm))

theorem linear (H:C.Makes) (home:Opened C d i p) (live:i ≤ N) (panel:C.label d →ₗ[ℂ] Ω)
    (supplier:∀ x:C.label d, ∃ q:Coefficient F₀ (C.side i p), Printed C d N p i o q (panel x)) :
    ∃ M:C.label d →ₗ[ℂ] C.label d, ∀ (x:C.label d) (q:Coefficient F₀ (C.side i p)),
      Printed C d N p i o q (panel x) →
      M x=projection F₀ C.params (P₀).p.threshold o q := by
  let q:=fun x=> (supplier x).choose
  let readout:=projection F₀ C.params (P₀).p.threshold o
  have ink (x:C.label d):Printed C d N p i o (q x) (panel x):=(supplier x).choose_spec
  have terms:=dimensions d N p i H home.post live
  have law:=(H.wilson.represents N p i live).good
  let M:C.label d →ₗ[ℂ] C.label d:={
    toFun:=fun x=>readout (q x)
    map_add':=by
      intro x y
      obtain ⟨a,ax⟩:=(ink x).bought
      obtain ⟨b,by'⟩:=(ink y).bought
      have paid:=presentation (ink x).form ax (ink y).form by'
      have word:Printed C d N p i o (beside (q x) (q y)) (panel (x+y)):=by
        refine ⟨paid.1,⟨_,paid.2⟩,?_⟩
        exact (plus law ax by' S₀).trans (((congrArg₂ (·+·) (ink x).fields (ink y).fields).trans (panel.map_add x y).symm))
      exact (intrinsic C d N p i o H home live (ink (x+y)) word).trans
        (GermGraph.add_projection d (q x) (q y) (ink x).form (ink y).form terms.1 terms.2 ⟨_,_,ax⟩ ⟨_,_,by'⟩)
    map_smul':=by
      intro s x
      obtain ⟨a,ax⟩:=(ink x).bought
      have word:Printed C d N p i o (stretch s (q x)) (panel (s • x)):=by
        refine ⟨stretch_format s (ink x).form,⟨_,stretch_rem s ax⟩,?_⟩
        calc
          _ = s • (q x).density o S₀ P₀ := funext (stretch_density S₀ P₀ o s (q x))
          _ = panel (s • x) := (congrArg (s • ·) (ink x).fields).trans (panel.map_smul s x).symm
      exact (intrinsic C d N p i o H home live (ink (s • x)) word).trans
        (WilsonOriginalNullColumnSplit.scale_page C.params P₀ o (q x) s terms.1 terms.2 (ink x).form ax) }
  exact ⟨M,fun x z cert=>intrinsic C d N p i o H home live (ink x) cert⟩

end YM.Integration.WilsonOriginalNullPlacedGermMap
