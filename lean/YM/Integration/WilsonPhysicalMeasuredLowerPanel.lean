import YM.Integration.WilsonPhysicalActualPositiveMenu

/-! Original reflected lower and mixed entries before the position change, at their actual booked physical home. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalMeasuredLowerPanel
open Function Set Filter Finset Lattice Wilson RG Source Cells
open PhysicalNext.Repeat.Legato Extraction RG17 Spec Table Table.Pairing Climb Trace.Pilot PhysMS
open GapsContact.Seams Trace.Terrace
open Maxwell Maxwell.Wick XSpace XSpace.Normalize XSpace.Structure1
open MS MS.Land MS.Menus MS.Theater Local.Physical
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonOriginalPublicRelativeGramFreePanel (pointsAt)
open WilsonOriginalPublicRelativeGramAddresses (ports shape)
open WilsonOriginalPublicRelativeGramPins (matrix cutoff)
open scoped Classical Topology BigOperators Matrix Matrix.Norms.Operator
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    (J:ℝ→tower S){H:(Bel R.family.book).Hierarchy}{arch:Trace.Terrace.Arch R.family}
    {ℓ:Ultrafilter (ℕ×ℕ)} (a:Axis)(avoid:Finset E4)
variable {D T:ℕ}{I:Type}(d:I→Fin (D+1))(v:(i:I)→(Bel R.family.book).Field (d i))

def reported (m:ℕ)(r:ℝ):Matrix I I ℂ:=
  matrix R F a (fun i=>(d i).val) J v r r m (fun _:Unit=>ports R avoid (pointsAt a) m r)
    (fun _=>(1:ℂ)) false

def born:Matrix I I ℂ:=fun i j=>WickGoal
  (WilsonOriginalPublicRelativeGramLeading.fields R a (fun i=>(d i).val) v i j) (pointsAt a)

def filed (m:ℕ){r:ℝ}(B:Book F (l:=ℓ) H arch D T r)(w:I→Bool)(z:ℕ×ℕ):Matrix I I ℂ:=
  cutoff R a (fun i=>(d i).val) m (fun _:Unit=>ports R avoid (pointsAt a) m r) (fun _=>(1:ℂ))
    (fun _ t i=>((B.rows (d i)).arm (w i) (J r (d i) (v i))).source t) false z

/-- Each side of each mixed pair is the booked microscopic original field. -/
theorem original (bliss:Bliss F ℓ arch H)(m:ℕ){r:ℝ}(rp:0<r)
    (B:Book F (l:=ℓ) H arch D T r)(w:I→Bool):
    Tendsto (filed R F J a avoid d v m B w) (ℓ:Filter (ℕ×ℕ)) (𝓝 (reported R F J a avoid d v m r)):=by
  let A(i:I):=(B.rows (d i)).arm (w i) (J r (d i) (v i))
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  exact WilsonOriginalPublicRelativeGramPins.limit R F a (fun i=>(d i).val) J v r r m
    (fun _:Unit=>ports R avoid (pointsAt a) m r) (fun _=>(1:ℂ)) (fun _ z k=>(A k).source z)
    (fun _ k=>(A k).label) (fun _ k=>(A k).approaches) (fun b k=>by cases b <;> exact (A k).represents)
    bliss.lies (fun _ _=>WilsonOriginalPublicRelativeGramAddresses.screened R avoid (pointsAt a) m rp) false i j

/-- The same mixed entries at the admitted mesh converge on the real home scale. -/
theorem leading (lead:Leading F J)(m:ℝ→ℕ)
    (mesh:Tendsto (fun r=>R.family.S.a (m r)/r) trail (𝓝 0)):
    Tendsto (fun r=>reported R F J a avoid d v (m r) r) trail (𝓝 (born R a d v)):=by
  let grid:=fun r (_:Unit)=>ports R avoid (pointsAt a) (m r) r
  let sites:=fun r (_:Unit)=>shape avoid (pointsAt a) (R.family.S.a (m r)/r)
  have pos:∀ᶠr in trail,0<R.family.S.a (m r)/r:=
    (show ∀ᶠr:ℝ in trail,0<r from self_mem_nhdsWithin).mono fun r hr=>div_pos (R.family.S.a_pos _) hr
  have approach:=WilsonOriginalPublicRelativeGramAddresses.limit avoid (pointsAt a) pos mesh
  have clear:pointsAt a∈conf 2:=Extra.FD.couple_ok (WilsonAddressedPublicWideMeasure.distinct a)
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have result:=WilsonOriginalPublicRelativeGramLeading.original R F a (fun i=>(d i).val) J v
    id m grid (fun (_:ℝ) (_:Unit)=>(1:ℂ)) sites (fun _:Unit=>pointsAt a) (fun _=>(1:ℂ)) lead tendsto_id
    ((show ∀ᶠr:ℝ in trail,0<r from self_mem_nhdsWithin).mono fun r hr _=>WilsonOriginalPublicRelativeGramAddresses.placed R avoid (pointsAt a) (m r) hr)
    (fun _=>approach) (fun _=>clear) (fun _=>tendsto_const_nhds) i j
  simpa only [reported,born,WilsonOriginalPublicRelativeGramLeading.free,Fintype.sum_unique,one_mul,
    grid,id_eq] using result

end YM.Integration.WilsonPhysicalMeasuredLowerPanel
