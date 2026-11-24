import YM.Integration.WilsonOriginalNullOriginGrid

/-! The original centered inverse and the measured matrix on an arbitrary
finite corridor. The matrix acts on the same bare word at all placements.
Its primary includes feeds from the projection-null part of every true
intermediate transfer. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullOriginGridMatrix
open Function Filter Lattice RG Wilson Source Labels MeasureTheory Extra.Histories Extra.Histories.Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open RG05Readout RG05Readout.Address RG05Readout.Records WilsonOriginalNullCorridor
open WilsonOriginalNullPlacedGermMap WilsonOriginalNullPlacedFullMatrix
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) (d N p m n:ℕ)
local notation "C₀" => R.family
local notation "F₀" => (C₀).labels.level d
local notation "S₀" => (C₀).localSection d

def centered (live:m+n ≤ N) (home:Opened C₀ d m p) (high:Opened C₀ d (m+n) p):
    (C₀).label d ≃ₗ[ℂ] (C₀).label d:=
  (fitting (C:=C₀) d N p (m+n) R.makes high live).symm.trans
    (fitting (C:=C₀) d N p m R.makes home (by omega))

def measured (live:m+n ≤ N) (home:Opened C₀ d m p) (high:Opened C₀ d (m+n) p)
    (A:(C₀).label d →ₗ[ℂ] (C₀).label d):(C₀).label d →ₗ[ℂ] (C₀).label d:=
  (fitting (C:=C₀) d N p m R.makes home (by omega)).toLinearMap.comp
    (A.comp (fitting (C:=C₀) d N p (m+n) R.makes high live).symm.toLinearMap)

theorem inverse (live:m+n ≤ N) (home:Opened C₀ d m p) (high:Opened C₀ d (m+n) p)
    (A:(C₀).label d →ₗ[ℂ] (C₀).label d) (e:(C₀).label d):
    measured R d N p m n live home high A ((centered R d N p m n live home high).symm e)=
      fitting (C:=C₀) d N p m R.makes home (by omega)
        (A ((fitting (C:=C₀) d N p m R.makes home (by omega)).symm e)) := by
  simp [measured,centered]

theorem zero (η:ℝ) (live:m+n ≤ N) (home:Opened C₀ d m p) (high:Opened C₀ d (m+n) p)
    (y:∀j,Site ((C₀).side j p)) (A:(C₀).label d →ₗ[ℂ] (C₀).label d)
    (report:Heard R d η N p m n live home y A)
    (grid:y (m+n)=((C₀).S.toDepth (show m ≤ m+n by omega) p).embed (y m)):
    A=LinearMap.id ∧ measured R d N p m n live home high A=(centered R d N p m n live home high).toLinearMap := by
  have full (x:(C₀).label d):WilsonOriginalNullPlacedFlowPanel.field R d N p m n (y (m+n)) x=
      calValues (C:=C₀) d N p m x ∘ Lattice.translate (y m):=by
    rw [grid]
    exact WilsonOriginalNullOriginGrid.aligned R d N p home.post (y m) x n live
  let P:=(C₀).path.rep N p m
  have age:m ≤ N:=by omega
  let φ:=fitting (C:=C₀) d N p m R.makes home age
  have raw:A=LinearMap.id:=by
    apply LinearMap.ext;intro x
    let origin:=((C₀).factory d N p).entries m x
    let move:=Tour.placard C₀ R.makes N p age (y m)
    let z:=Drift.stamp (y m) move origin
    obtain ⟨zf,zp,_,field⟩:=WilsonOriginalNullFactoryRoute.entrance R d age home (y m) x
    have ink:Printed C₀ d N p m (y m) z (WilsonOriginalNullPlacedFlowPanel.field R d N p m n (y (m+n)) x):=
      ⟨zf,⟨_,zp⟩,field.trans (full x).symm⟩
    have found:projection F₀ (C₀).params P.p.threshold (y m) z=φ (A x):=report.intrinsic x z ink
    have same:=WilsonOriginalNullRelocation.page F₀ (C₀).params P.p.threshold 0 (y m) move origin
    rw [zero_add] at same
    have native:P.p=(C₀).path.levels.budget m:=(R.makes.wilson.represents N p m age).vac
    have old:projection F₀ (C₀).params P.p.threshold 0 origin=φ x:=by
      rw [native];rfl
    exact φ.injective (found.symm.trans (same.trans old))
  refine ⟨raw,?_⟩
  ext x
  rw [raw]
  rfl

theorem site (η:ℝ) (live:m+n ≤ N) (home:Opened C₀ d m p) (high:Opened C₀ d (m+n) p)
    (y:∀ j,Site ((C₀).side j p)) (A:(C₀).label d →ₗ[ℂ] (C₀).label d)
    (report:Heard R d η N p m n live home y A) (e:(C₀).label d):
    let g:=(fitting (C:=C₀) d N p m R.makes home (by omega)).symm e
    let vref:=((C₀).factory d N p).terminal g
    let top:=((C₀).S.toDepth live p).embed (y (m+n))
    let prior:=dyes C₀ (m+n) N p live (((C₀).S.a (m+n):ℂ)^d • (C₀).O N p vref top)
    let P:=(C₀).path.rep N p m
    let full:=flow C₀ d N p m n prior
    let coord:=measured R d N p m n live home high A ((centered R d N p m n live home high).symm e)
    ∃z,Printed C₀ d N p m (y m) z full ∧ projection F₀ (C₀).params P.p.threshold (y m) z=coord ∧
      ∀ b,Printed C₀ d N p m (y m) b full → projection F₀ (C₀).params P.p.threshold (y m) b=coord := by
  intro g vref top prior P full coord
  have fine:prior=calValues (C:=C₀) d N p (m+n) g ∘ Lattice.translate (y (m+n)):=
    WilsonOriginalNullOriginGrid.public_grid R d N p live high.post (y (m+n)) g
  have fused:full=WilsonOriginalNullPlacedFlowPanel.field R d N p m n (y (m+n)) g:=
    congrArg (flow C₀ d N p m n) fine
  have read (z) (ink:Printed C₀ d N p m (y m) z full):
      projection F₀ (C₀).params P.p.threshold (y m) z=coord:=by
    rw [show coord=fitting (C:=C₀) d N p m R.makes home (by omega) (A g) from inverse R d N p m n live home high A e]
    exact report.intrinsic g z ⟨ink.form,ink.bought,ink.fields.trans fused⟩
  obtain ⟨v,z,zf,zp,_,_,_,_,whole,_⟩:=report.deposited g
  have ink:Printed C₀ d N p m (y m) z full:=⟨zf,⟨_,zp⟩,whole.symm.trans fused.symm⟩
  exact ⟨z,ink,read z ink,read⟩

end YM.Integration.WilsonOriginalNullOriginGridMatrix
