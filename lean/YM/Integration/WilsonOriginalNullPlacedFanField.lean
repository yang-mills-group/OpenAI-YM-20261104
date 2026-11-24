import YM.Integration.WilsonOriginalNullPlacedGermMap
import YM.Integration.WilsonOriginalNullRelocation
import YM.Integration.WilsonThermometerOwnOffsetField

/-! One genuine enrolled cutoff column on its own ancestry, with the true
placed germ and the original once-divided fee. The engineered true
transition takes the full cutoff density to the same normalized density
at the adjacent running scale. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullPlacedFanField
open Function Filter Set MeasureTheory Lattice Wilson RG Source Labels RG12 Extra.Histories Relay
open RG05Readout Native Address Many Records Harvest Push.GridApprox Push.Local
open PhysicalNext Repeat Legato Graces Roost Org MergeProof Accent
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue
open WilsonOriginalNullPlacedGermMap
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) (d N p j:ℕ)
local notation "C₀" => R.family
local notation "F₀" => (C₀).labels.level d
local notation "S₀" => (C₀).localSection d
local notation "P₀" => (C₀).path.rep N p j

theorem push (live:j<N) (f:Config G ((C₀).side N p)→ℂ) :
    transition (C:=C₀) d N p j (dyes C₀ (j+1) N p live (((C₀).S.a (j+1):ℂ)^d • f))=
      dyes C₀ j N p live.le (((C₀).S.a j:ℂ)^d • f) := by
  let χ:=((C₀).S.block j).val
  have units:(χ:ℂ)^d*((C₀).S.a (j+1):ℂ)^d=((C₀).S.a j:ℂ)^d:=by
    simpa [χ,WilsonThermometerOffsetCylinder.units] using WilsonThermometerOffsetPrimary.scale R j d 1
  let g:=((C₀).S.a (j+1):ℂ)^d • f
  calc
    _=(χ:ℂ)^d • dyes C₀ j N p live.le g:=by
      unfold transition blast
      congr 1
      exact (gust_step (C₀).path N p N _ live).symm
    _=dyes C₀ j N p live.le ((χ:ℂ)^d • g):=(dye_pitch (C:=C₀) (p:=p) g live.le ((χ:ℂ)^d)).symm
    _=_:=by dsimp only [g];rw [smul_smul,units]

theorem rooted (live:j ≤ N) (home:Opened C₀ d j p) (o:Site ((C₀).side j p))
    (X q:store C₀ d p j) {B:ℝ} (xf:X.Format 0 (C₀).params P₀) (xp:X.remBound 0 P₀ (safety C₀ j) B)
    (qf:q.Format o (C₀).params P₀) (qp:q.remBound o P₀ (safety C₀ j) B)
    (field:q.density o S₀ P₀=(X.density 0 S₀ P₀) ∘ Lattice.pull 1 o) :
    projection F₀ (C₀).params (P₀).p.threshold o q=projection F₀ (C₀).params (P₀).p.threshold 0 X := by
  let move:=Tour.placard C₀ R.makes N p live o
  let v:=Drift.stamp o move X
  have vf:v.Format o (C₀).params P₀:=by simpa only [zero_add] using Drift.stamp_format o move X xf
  have vp:v.remBound o P₀ (safety C₀ j) B:=by simpa only [zero_add] using Drift.stamp_rem o move X xp
  have stamp:v.density o S₀ P₀=(X.density 0 S₀ P₀) ∘ Lattice.translate o:=by
    simpa only [v,move,zero_add,Function.comp_def] using WilsonOriginalNullRelocation.registered C₀ R.makes d N p j live 0 o X
  have eq:q.density o S₀ P₀=v.density o S₀ P₀:=by
    rw [field,stamp];funext U
    change X.density 0 S₀ P₀ (Lattice.pull 1 o U)=X.density 0 S₀ P₀ (Lattice.translate o U)
    rw [Lattice.pull_one]
  have a:Printed C₀ d N p j o q (q.density o S₀ P₀):=⟨qf,⟨B,qp⟩,rfl⟩
  have b:Printed C₀ d N p j o v (q.density o S₀ P₀):=⟨vf,⟨B,vp⟩,eq.symm⟩
  have same:=WilsonOriginalNullPlacedGermMap.intrinsic C₀ d N p j o R.makes home live a b
  have cut:=WilsonOriginalNullRelocation.page F₀ (C₀).params (P₀).p.threshold 0 o move X
  rw [zero_add] at cut
  exact same.trans cut

theorem original {base:ℕ} {D:Rail C₀} {B:ℕ→ℕ→ℝ} {V:Sight C₀ d p} {r:Emblems C₀ d}
    {z:Site ((C₀).side N p)} (H:Enrolled R.makes D B base N p d (digits R N p z) V r)
    (entered:base≤j) (live:j≤N) (home:Opened C₀ d j p) (starts:∀e≤d,(C₀).ref e≤N)
    (y:Palette C₀ d) :
    let t:=WilsonThermometerOwnOffsetField.primaryLetter d
    let o:=((C₀).S.toDepth live p).parent z
    let x:=((C₀).factory d N p).terminal (finer r live y t)
    ∃ q:store C₀ d p j, q.Format o (C₀).params P₀ ∧ q.remBound o P₀ (safety C₀ j) (B d j*size y) ∧
      projection F₀ (C₀).params (P₀).p.threshold o q=y t ∧
      q.density o S₀ P₀=dyes C₀ j N p live (((C₀).S.a j:ℂ)^d • (C₀).O N p x z) := by
  intro t o x
  obtain ⟨X,q,seen,xf,xp,qf,qp,moved,word⟩:=WilsonThermometerOwnOffsetField.actual R N p j z H entered live starts y
  exact ⟨q,qf,qp,(rooted R d N p j live home o X q xf xp qf qp moved).trans seen,word⟩

end YM.Integration.WilsonOriginalNullPlacedFanField
