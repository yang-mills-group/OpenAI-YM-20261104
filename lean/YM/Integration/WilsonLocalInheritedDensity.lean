import YM.Integration.WilsonLocalInheritedRatio

/-! The approximating absolute integrand at one reporting fiber contains
the old effective gas and the original transition evaluated at the sampled
field, the original coarse denominator, and the genuine unperturbed pivot. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalInheritedDensity
open Finset Set Lattice RG Wilson Tree RG16 Precision PertExtension PertExtension.Series
open PhysicalNext.Repeat.Legato WilsonPhysicalRegisteredForestAction WilsonReportingForestPivots
open WilsonLocalConditionalResidue
open scoped Classical BigOperators Matrix.Norms.Frobenius
variable {G:Gauge}

def model (P:ChartRatio G) (p:ℕ) (R:Run G) (N per m:ℕ) (V:Config G (R.family.side m per))
    (T:Forest (R.family.path.levels.clock.op m per).ratio) (B:Finset T.Free)
    (v:({e:T.Free|e∉moving T B}:Set T.Free)→G.El) (g:ℝ) (X:↥(moving T B)→G.Color) :=
  let E:=moving T B
  let β:=R.family.path.β N per (m+1)
  let U:=WilsonLocalConditionalResidue.position T B v g
  Chart.jacobian P (0:↥E→G.Color)*WilsonLocalInheritedRatio.rest R.family N per m V (U X)*
    bare β (U 0)/(R.family.path.rep N per m).eval V*Real.exp (score P p β g T B v X 0)

theorem cancel (a k l u z h:ℝ) (hl:0 < l) : (a*(l*u/z))*(k/l*h) = a*k*u/z*h := by
  have inv:l*(k/l)=k:=by field_simp [hl.ne']
  calc _=a*(l*(k/l))*u/z*h:=by ring
       _=_:=by rw [inv]

theorem field (P:ChartRatio G) (p:ℕ) (R:Run G) (N per m:ℕ) (hm:m < N) (V:Config G (R.family.side m per))
    (T:Forest (R.family.path.levels.clock.op m per).ratio) (B:Finset T.Free)
    (v:({e:T.Free|e∉moving T B}:Set T.Free)→G.El) (g:ℝ) (X:↥(moving T B)→G.Color) :
    weight P (actualConditionalDensity R.family N per m V) T B v g 0*
    fitted P p (R.family.path.β N per (m+1)) g (WilsonLocalInheritedRatio.rest R.family N per m V) T B v X 0=
    model P p R N per m V T B v g X := by
  let U:=WilsonLocalConditionalResidue.position T B v g
  dsimp only [WilsonLocalConditionalResidue.weight,fitted,model]
  rw [smul_zero,WilsonLocalInheritedRatio.split]
  exact cancel _ _ _ _ _ _ (WilsonLocalInheritedRatio.positive R N per m hm V (U 0)).1

end YM.Integration.WilsonLocalInheritedDensity
