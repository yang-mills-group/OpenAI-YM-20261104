import YM.Integration.WilsonOriginalNullPlacedOffset

/-! Combine complete original P presentations at their common physical site.
The arithmetic is on the original Wilson density before applying the germ. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullPlacedBlend
open Function Filter Lattice RG Wilson Extra.Histories Source Labels
open Extra.Histories.Relay Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato RG05Readout RG05Readout.Address
open WilsonOriginalNullPlacedGermMap
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) (d N p i:ℕ)
local notation "C₀" => R.family
local notation "F₀" => (C₀).labels.level d
local notation "S₀" => (C₀).localSection d
local notation "P₀" => (C₀).path.rep N p i

theorem joint (home:Opened C₀ d i p) (live:i ≤ N) (o:Site ((C₀).side i p))
    {q v:Coefficient F₀ ((C₀).side i p)} {f g:Config G ((C₀).side i p)→ℂ}
    (old:Printed C₀ d N p i o q f) (incoming:Printed C₀ d N p i o v g) :
    let read:=projection F₀ (C₀).params (P₀).p.threshold o
    Printed C₀ d N p i o (beside q v) (f+g) ∧ read (beside q v)=read q+read v := by
  let law:=(R.makes.wilson.represents N p i live).good
  obtain ⟨a,qa⟩:=old.bought;obtain ⟨b,vb⟩:=incoming.bought
  have ready:=presentation old.form qa incoming.form vb
  have admits:=dimensions d N p i R.makes home.post live
  exact ⟨⟨ready.1,⟨_,ready.2⟩,(plus law qa vb S₀).trans (congrArg₂ (·+·) old.fields incoming.fields)⟩,
    GermGraph.add_projection d q v old.form incoming.form admits.1 admits.2 ⟨_,a,qa⟩ ⟨_,b,vb⟩⟩

theorem column (home:Opened C₀ d i p) (live:i ≤ N) (o:Site ((C₀).side i p)) (x:(C₀).label d) :
    ∃ z:Coefficient F₀ ((C₀).side i p),
      Printed C₀ d N p i o z (calValues (C:=C₀) d N p i x ∘ Lattice.translate o) ∧
      projection F₀ (C₀).params (P₀).p.threshold o z=fitting d N p i R.makes home live x := by
  let q:=((C₀).factory d N p).entries i x
  let move:=Tour.placard C₀ R.makes N p live o
  let z:=Drift.stamp o move q
  obtain ⟨zf,zp,_,fields⟩:=WilsonOriginalNullFactoryRoute.entrance R d live home o x
  have same:=WilsonOriginalNullRelocation.page F₀ (C₀).params (P₀).p.threshold 0 o move q
  rw [zero_add] at same
  have native:(P₀).p=(C₀).path.levels.budget i:=(R.makes.wilson.represents N p i live).vac
  have base:projection F₀ (C₀).params (P₀).p.threshold 0 q=fitting d N p i R.makes home live x:=by
    rw [native];exact (fitting_apply (C:=C₀) d N p i R.makes home live x).symm
  exact ⟨z,⟨zf,⟨_,zp⟩,fields⟩,same.trans base⟩

end YM.Integration.WilsonOriginalNullPlacedBlend
