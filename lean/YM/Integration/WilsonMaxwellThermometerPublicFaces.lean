import YM.Integration.WilsonMaxwellThermometerPublicPocket
import YM.Integration.WilsonPositionThermometerStationUnit

/-! The public lower Schur contrast is the genuine Wilson connected
three-field measurement with all three sources in the grade-four space.
Two independent child residues and the integrated center are retained. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerPublicFaces
open Filter Lattice Wilson Labels RG Source MeasureTheory PhysicalNext.Repeat.Legato Maxwell Maxwell.Free
open RG17 XSpace XSpace.Normalize OPE OPE.Orbits Climb Table Spec Extraction Trace Trace.Pilot Next.UVStress PhysMS
open WilsonPositionThermometerCapStation WilsonMaxwellThermometerNominatedCofactor
open WilsonMaxwellThermometerPublicPocket WilsonThermometerAlignedCells
open private sum_triples from YM.Integration.WilsonThermometerAlignedCells
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) {f:Extraction.Order} {S:Table R.family.book}
  (F:Final R.family f S) (J:ℝ→tower S) (V:Store G) (K:Rose.Pick V) (A:ℝ→Group R.family 6)

def upper (r:ℝ) (e:RG17.Free R.family 4) (i:Fin 3):RG17.Free R.family 4:=
  if i=0 then e else WilsonPositionPrescribedFrame.change F J V 4 r
    ((fields R.family.labels 4).symm (WilsonPositionThermometerGradedSource.lower G))

def station (r:ℝ) (e:RG17.Free R.family 4) (i:Fin 3):RG17.Free R.family 4:=(A r).change 4 (upper R F J V r e i)

def faces (r:ℝ) (e:RG17.Free R.family 4) (z:(ℕ×ℕ)) (x:Fin 3→Site (R.family.side z.1 z.2)):Finset (Fin 3)→ℂ:=
  WilsonPositionThermometerStationUnit.face (A r).station (index (A r) (⟨4,by decide⟩:Fin 7)) (station R F J V A r e) z x

private theorem product {N p:ℕ} (s:Finset (Fin 3)) (X:Fin 3→C(Config G (R.family.side N p),ℂ)) :
    mean R N p (∏j∈s,X j)=R.family.omega N p (fun U=>∏j∈s,X j U) := by
  change R.family.omega N p (⇑(∏j∈s,X j))=_
  congr 1
  funext U
  induction s using Finset.induction_on with
  | empty=>rfl
  | insert j s hj ih=>rw [Finset.prod_insert hj,Finset.prod_insert hj];exact congrArg (X j U * ·) ih

theorem subgroup (r:ℝ) (e:RG17.Free R.family 4) (z:(ℕ×ℕ)) (o:Site (R.family.side z.1 z.2) × Site (R.family.side z.1 z.2)) (s:Finset (Fin 3)):
    WilsonMaxwellThermometerNominatedCofactor.table R (WilsonPositionCorrectedCap.adjusted F J V A r) z.1 z.2 o (shoulder R (A r) z e) s=
      R.family.omega z.1 z.2 (fun U=>∏j∈s,R.family.O z.1 z.2
        ((A r).station.wheel.atCut z (index (A r) (⟨4,by decide⟩:Fin 7)) (station R F J V A r e j)) (atOrigin o j) U) := by
  let Z:=WilsonPositionCorrectedCap.adjusted F J V A r
  let X (i:Fin 3):=file R z.1 z.2 ((A r).station.wheel.atCut z (index (A r) (⟨4,by decide⟩:Fin 7)) (station R F J V A r e i)) (atOrigin o i)
  have center:shoulder R (A r) z e=X 0:=rfl
  have off (i:Fin 3) (hi:i≠0):native R Z z.1 z.2 o i=X i:=by fin_cases i <;> first | contradiction | rfl
  have rest:companions R Z z.1 z.2 o s=∏i∈s.erase 0,X i:=Finset.prod_congr rfl fun i hi=>off i (Finset.ne_of_mem_erase hi)
  change WilsonMaxwellThermometerNominatedCofactor.table R Z z.1 z.2 o _ s=R.family.omega z.1 z.2 (fun U=>∏j∈s,X j U)
  rw [←product]
  by_cases hs:(0:Fin 3)∈s
  · simp only [WilsonMaxwellThermometerNominatedCofactor.table,if_pos hs,marked,LinearMap.coe_mk,AddHom.coe_mk,rest,center,Finset.mul_prod_erase s X hs]
  · simp only [WilsonMaxwellThermometerNominatedCofactor.table,if_neg hs,held,rest,Finset.erase_eq_of_notMem hs]

theorem literal (r:ℝ) (e:RG17.Free R.family 4) {H:(Bel R.family.book).Hierarchy}
    (ready:(A r).station.checked f H (A r).horizon):
    ∀ᶠz:(ℕ×ℕ) in f.fuse,WilsonMaxwellThermometerPublicPocket.measured R F J V K A r z e=
      (Rose.test K).applyTo (fun x=>WilsonPositionThermometerConnected.value
        (faces R F J V A r e z (WilsonSeparatedOriginalThermometerCells.positions (R:=R) r z x))) := by
  have part:=WilsonPositionThermometerStationUnit.subproducts (A r).station (index (A r) (⟨4,by decide⟩:Fin 7))
    R.makes ready (station R F J V A r e)
  filter_upwards [part,large_mesh f (R.family.ref 4)] with z charged ref
  let T:=Site (R.family.side z.1 z.2)
  let Z:=WilsonPositionCorrectedCap.adjusted F J V A r
  let χ:=WilsonSeparatedOriginalThermometerCells.positions (R:=R) r z
  let Φ:=Rose.test K
  let f₀:=faces R F J V A r e z
  have shift (y:T×T) (c:T):f₀ (placedAt y c)=f₀ (atOrigin y):=by
    funext s
    let rows (i:Fin 3):R.family.book.Token:=⟨4,(A r).station.wheel.atCut z (index (A r) (⟨4,by decide⟩:Fin 7))
      (WilsonPositionThermometerStationUnit.slot (index (A r) (⟨4,by decide⟩:Fin 7)) (station R F J V A r e) s i)⟩
    exact R.family.anchored (p:=z.2) R.makes rows (fun _=>ref) c (atOrigin y)
  have origin (y:T×T):WilsonMaxwellThermometerNominatedCofactor.reading R Z z.1 z.2 y (shoulder R (A r) z e)=
      WilsonPositionThermometerConnected.value (f₀ (atOrigin y)):=by
    rw [←connected]
    congr 1
    funext s
    exact (subgroup R F J V A r e z y s).trans (charged (atOrigin y) s).symm
  change (∑y,mass (R:=R) r z Φ y • WilsonMaxwellThermometerNominatedCofactor.reading R Z z.1 z.2 y) (shoulder R (A r) z e)=
    Φ.applyTo (fun x=>WilsonPositionThermometerConnected.value (f₀ (χ x)))
  rw [WilsonSeparatedOriginalThermometerCells.tested Φ χ (WilsonSeparatedOriginalThermometerCells.placed (R:=R) r z)
    (fun x=>WilsonPositionThermometerConnected.value (f₀ x)),sum_triples]
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul,origin]
  apply Finset.sum_congr rfl
  intro y _
  rw [mass,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _
  rw [shift]
end YM.Integration.WilsonMaxwellThermometerPublicFaces
