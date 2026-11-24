import YM.Integration.WilsonOriginalNullFactoryRoute
import YM.Integration.WilsonMatrixOriginalGermBasis

/-! Complex linearity of one true Wilson child transition on the
physically normalized factory field translated to an arbitrary fine site. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullPlacedLinearPanel
open Function Filter Lattice RG Wilson Extra.Histories Source Labels
open Extra.Histories.Relay Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato RG05Readout RG05Readout.Address MeasureTheory
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) (d:ℕ)
local notation "C₀" => R.family
local notation "F₀" => (C₀).labels.level d
local notation "S₀" => (C₀).localSection d

def held (N p i:ℕ) (y:Site ((C₀).side (i+1) p)) (x:(C₀).label d) : Config G ((C₀).side i p)→ℂ :=
  transition (C:=C₀) d N p i (calValues (C:=C₀) d N p (i+1) x ∘ Lattice.translate y)

theorem tested {N p t:ℕ} (live:t ≤ N) (home:Opened C₀ d t p) (y:Site ((C₀).side t p)) (x:(C₀).label d) :
    Integrable (calValues (C:=C₀) d N p t x ∘ Lattice.translate y) (prior G _) := by
  let z:=Drift.stamp y (Tour.placard C₀ R.makes N p live y) (((C₀).factory d N p).entries t x)
  obtain ⟨zf,zp,_,real⟩:=WilsonOriginalNullFactoryRoute.entrance R d live home y x
  have fields:z.density y S₀ ((C₀).path.rep N p t)=calValues (C:=C₀) d N p t x ∘ Lattice.translate y:=real
  rw [←fields];exact (z.envelope S₀ (R.makes.wilson.represents N p t live).good zp zf).integrableC _

def panel {N p i:ℕ} (live:i<N) (home:Opened C₀ d (i+1) p) (y:Site ((C₀).side (i+1) p)) :
    (C₀).label d →ₗ[ℂ] (Config G ((C₀).side i p)→ℂ) where
  toFun:=held R d N p i y
  map_add' x z:=by
    unfold held
    rw [cal_add (C:=C₀) d N p (i+1) R.makes home.post live x z]
    exact transition_add (C:=C₀) d N p (tested R d live home y x) (tested R d live home y z)
  map_smul' a x:=by
    have scale:calValues (C:=C₀) d N p (i+1) (a • x) =
        a • calValues (C:=C₀) d N p (i+1) x :=
      (WilsonMatrixOriginalGermBasis.density C₀ R.makes d N p (i+1) home.post live).map_smul a x
    unfold held
    rw [scale]
    change transition (C:=C₀) d N p i (a • (calValues (C:=C₀) d N p (i+1) x ∘ Lattice.translate y))=
      a • transition (C:=C₀) d N p i (calValues (C:=C₀) d N p (i+1) x ∘ Lattice.translate y)
    unfold transition blast
    rw [StepData.push_smul _ _ _ _ (tested R d live home y x)]
    exact smul_comm ..

end YM.Integration.WilsonOriginalNullPlacedLinearPanel
