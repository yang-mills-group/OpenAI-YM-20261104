import YM.Integration.WilsonIndependentMatchedFourUnitProjection

noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialPublicJointFourScalarBlock
open WilsonCoeffUV WilsonCoeffUV.RootLaw
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Supply Ticket Polestar Shard Plan Mer
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{D k:ℕ}{F:Frame G 4}{T:SectionData F}{p:4<D}{H:Hol G}

open WilsonIndependentMatchedFourUnitCourse WilsonIndependentMatchedFourUnitProjection
variable {e m N:ℕ}{E W:Credit}

/-- The whole scalar-sheet sector, including the constant unit and every test derivative. -/
def band (F:Frame G 4)(i:Alma F):ℕ:=if Cosmos.sheet F i=0 then 0 else 1

theorem crossing (i j:Alma F):band F j < band F i ↔ Cosmos.sheet F i≠0 ∧ Cosmos.sheet F j=0:=by
  classical
  by_cases a:Cosmos.sheet F i=0 <;> by_cases b:Cosmos.sheet F j=0 <;> simp [band,a,b]

theorem bare_entry (L:Theatre H T p e E W)(live:m≤N)(i j:Alma F)
    (outside:Cosmos.sheet F i≠0)(inside:Cosmos.sheet F j=0):
    prismata F (RootLaw.bare L.V.draws L.V.paid T p N m).2 i j=0:=by
  classical
  ext1 a
  change lineS (prismata F (RootLaw.bare L.V.draws L.V.paid T p N m).2) a i j=_
  rw [WilsonIndependentMatchedFourUnitProjection.original L live i j inside a]
  have distinct:i≠unitAt i:=fun same=>outside (congr_arg (Cosmos.sheet F) same)
  simp [lineS,Matrix.one_apply_ne distinct]

theorem bare (L:Theatre H T p e E W)(live:m≤N):
    Matrix.BlockTriangular (prismata F (RootLaw.bare L.V.draws L.V.paid T p N m).2) (band F):=by
  intro i j h
  obtain ⟨a,b⟩:=(crossing i j).mp h
  exact bare_entry L live i j a b

theorem inverse {S:Type*}[CommRing S](A:Matrix (Alma F) (Alma F) S)(ok:IsUnit A.det)
    (h:Matrix.BlockTriangular A (band F)):Matrix.BlockTriangular A⁻¹ (band F):=by
  classical
  letI : Invertible A:=((Matrix.isUnit_iff_isUnit_det _).2 ok).invertible
  exact Matrix.blockTriangular_inv_of_blockTriangular h

theorem changed (z:Cost)(B:Coil F)(h:Matrix.BlockTriangular B (band F)):
    Matrix.BlockTriangular (Chars F z B) (band F):=by
  intro i j h'
  change Bank.reel z (B i j)=0
  rw [h h',map_zero]

theorem original (L:Theatre H T p e E W)(firstDate:L.V.anchor ≤ m)(between:m ≤ k)(live:k ≤ N):
    let A:=L.V.draws
    let Ñ:=L.V.paid
    let B j:=prismata F (RootLaw.bare A Ñ T p N j).2
    let C:=CurNames A Ñ T p N m (k-m) false
    Matrix.BlockTriangular ((B m)⁻¹) (band F) ∧ Matrix.BlockTriangular ((B k)⁻¹) (band F) ∧
      Matrix.BlockTriangular C (band F) ∧ Matrix.BlockTriangular (bindingS A Ñ T p N m (k-m) false) (band F):=by
  classical
  intro A Ñ B C
  obtain ⟨mUnit,kUnit,eye,_⟩:=matrices_from_actual_root L firstDate between live
  have bm:=bare L (between.trans live)
  have bk:=bare L live
  let re:=Chars F (relativeF A Ñ N m (k-m))
  have u:IsUnit (re (B k)).det:=(Matrix.isUnit_iff_isUnit_det _).1 (((Matrix.isUnit_iff_isUnit_det _).2 kUnit).map re)
  have hc:Matrix.BlockTriangular C (band F):=by
    change Matrix.BlockTriangular (CurNames A Ñ T p N m (k-m) false) _
    rw [eye]
    exact bm.mul (inverse _ u (changed _ _ bk))
  have big:=ebbing L firstDate (show m+(k-m)≤N by omega) false
  exact ⟨inverse _ mUnit bm,inverse _ kUnit bk,hc,big.2 ▸ inverse _ big.1 hc⟩

end YM.Integration.WilsonPositionProgramTrialPublicJointFourScalarBlock
