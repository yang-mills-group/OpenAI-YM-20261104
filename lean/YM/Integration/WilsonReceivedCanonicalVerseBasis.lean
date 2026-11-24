import YM.Integration.WilsonThermometerSeedReading
import YM.Integration.WilsonOriginalStarSceneRead
import YM.Integration.WilsonPositionProgramBlockedTrialAddBack
import YM.Integration.WilsonDepositedFreshFiniteHistory

/-! Each canonical blocked Wilson section is opened on its actual finite stencil.
The real invariant socket and its Laurent grade are fixed before the original cutoff;
the exact inherited complex coordinates stay outside the independent word. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCanonicalVerseBasis
open Function Finset Lattice Wilson Laurent RG Source Labels Marker
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Winding
open IndependentSourcePathFamily OriginalMarkedSourceComet WilsonOriginalStarSceneWords
open WilsonThermometerDeclaredSeeds WilsonOriginalStarSceneRead ActualRunPhysicalPages
open PhysicalNext.Repeat.Legato Pert.Asymptotics
open scoped Classical BigOperators
variable {G:Gauge}{V:Type}(R:Run G)(d:V → ℕ){D:V → ℕ}
variable (knob:(j:V) → Knob (D j))(point:V → Chamber)

def basis (j:V)(c:Choice R d j):Seed G (D j):=
  let i:=entry R d j c
  ⟨rank R d i,rank R d i-pole R d i,(raw R d i).leg,key R d i,1,Complex.reCLM,knob j,point j⟩

theorem grade (j:V)(c:Choice R d j):(basis R d knob point j c).rank ≤ d j+(basis R d knob point j c).head:=by
  have h:=WilsonOriginalStarGradedScene.pole_grade R d (entry R d j c)
  rw [site] at h
  change rank R d _ ≤ d j+(rank R d _-pole R d _)
  omega

theorem field {n:Side}(j:V)(c:Choice R d j)(U:Config G n)(z:Site n):
    let p:=basis R d knob point j c
    (colour p.path p.color p.weight p.quadrant).unmasked U z=(raw R d (entry R d j c)).unmasked U z:=by
  intro p
  let i:=entry R d j c
  let u:=fun a=>(raw R d i).leg a |>.atSite U z
  change (colour (raw R d i).leg (key R d i) 1 Complex.reCLM).poly u=(raw R d i).poly u
  rw [colour_poly,←WilsonThermometerSeedReading.native R d i]
  simp

def dose (N p b:ℕ)(v:(j:V)→R.family.label (d j))(j:V)(c:Choice R d j):ℂ:=
  scalar R d (regulatorRun R.family N p b) (R.family.path.rep N p b).p.threshold v (entry R d j c)

def restored (g:ℝ){n:Side}(j:V)(c:Choice R d j)(z:Site n)(U:Config G n):ℂ:=
  let b:=basis R d knob point j c
  (g:ℂ)^(-(pole R d (entry R d j c):ℤ))*↑((colour b.path b.color b.weight b.quadrant).unmasked U z)

variable [DecidableEq V][Fintype V]
theorem letter (N p b:ℕ)(cut:b ≤ N)(v:(j:V)→R.family.label (d j))(o:V→Site (R.family.side b p))(j:V)(U:Config G (R.family.side b p)):
    WilsonPositionProgramBlockedTrialAddBack.uncut R (d j) N p b (o j) (v j) U=
      ∑z:Choice R d j,dose R d N p b v j z*restored R d knob point (regulatorRun R.family N p b) j z (o j) U:=by
  let g:=regulatorRun R.family N p b
  let θ:=(R.family.path.rep N p b).p.threshold
  let test:=fun (_:V) (_:Unit)=>(1:ℂ)
  let row:=WilsonOriginalStarSceneRows.rows R d o 1 g θ v test
  have flat:=scalar_read R d o 1 g θ v test j () U
  have polys:=monomials R d 1 v test N p b cut o j () U
  have numer (z:Choice R d j):
      (row (entry R d j z)).nominal g () U=dose R d N p b v j z*restored R d knob point g j z (o j) U:=by
    rw [show (row (entry R d j z)).nominal g () U=_ from nominal R d o 1 g θ v test (entry R d j z) () U]
    simp only [test,one_mul,site,restored,field,dose,g,θ]
    ring
  rw [←sum_congr rfl (fun a _=>numer a),Fintype.sum_sum_type]
  simp only [WilsonThermometerDeclaredSeeds.entry,Fintype.sum_unique,row]
  rw [flat,polys]
  simpa only [test,one_mul] using
    (show WilsonPositionProgramBlockedTrialAddBack.uncut R (d j) N p b (o j) (v j) U=
       v j 0+ActualRunPhysicalPages.kernel R N p b (d j) ((R.family.labels.level (d j)).core (v j)) (o j) U from rfl)

theorem faces (N p b:ℕ)(cut:b ≤ N)(v:(j:V)→R.family.label (d j))(o:V→Site (R.family.side b p))(S:Finset V)(U:Config G (R.family.side b p)):
    (∏j:S,WilsonPositionProgramBlockedTrialAddBack.uncut R (d j) N p b (o j) (v j) U)=
      ∑q:(j:S)→Choice R d j,(∏j:S,dose R d N p b v j (q j))*
        ∏j:S,restored R d knob point (regulatorRun R.family N p b) j (q j) (o j) U:=by
  simp only [letter R d knob point N p b cut v o]
  rw [Fintype.prod_sum]
  exact sum_congr rfl (fun _ _=>prod_mul_distrib)

end YM.Integration.WilsonReceivedCanonicalVerseBasis
