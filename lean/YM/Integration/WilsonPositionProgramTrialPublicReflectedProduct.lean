import YM.Integration.WilsonPositionProgramTrialPublicCellProduct
import YM.Integration.WilsonPositionProgramReflectedPurse
import YM.Integration.WilsonPositionProgramPublicWideHearing

/-! The actually used reflected physical packet gives both Rarities on the
same public inventory, with its first mirrored coordinate and common mass. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicReflectedProduct
open Function Filter Finset Set MeasureTheory WithLp Lattice Extraction RG
open Wilson Source Extra.Histories Spec PhysicalNext.Repeat.Legato
open Table.Pairing PhysMS MS MS.Menus XSpace Local.Physical
open WilsonCoeffUV WilsonCoeffUV.Layout WilsonCoeffUV.Mer WilsonCoeffUV.Embroider
open WilsonPositionProgramReflectedPurse (shape)
open private domain oneSite singlePoint from YM.Integration.WilsonPositionProgramReflectedPurse
open WilsonMaxwellThermometerReflectedIncidence (site)
open WilsonPositionProgramPublicReflectedRead (center)
open WilsonPositionProgramPublicWideHearing (profile)
open WilsonThermometerUnitFilingFourSquare
open WilsonPositionProgramTrialPublicCellProduct (price)
open WilsonMeasuredPublicEntranceCoverCells (cube mass)
open scoped Classical BigOperators
variable {G:Gauge}{I:Type} [Fintype I] {C:Family G}{S:Table C.book}
  {l:Filter (ℕ×ℕ)} [l.NeBot] {d:ℕ} {v:I→S.Field d}
  (arm:(i:I)→Bool→Arm C S l d (v i))

omit [Fintype I] [l.NeBot] in
theorem printed (a:Axis)(B:Bulb (center a) a)(i j:I)(t:Points 2):
    profile arm a B i j t=((∏k,shape a ((center a) 0) B k (fun e=>t k e):ℝ):ℂ):=by
  have left:shape a ((center a) 0) B 0 (fun e=>t 0 e)=B.r (earlier a (n:=1) (m:=1) t):=by
    apply congr_arg B.r
    apply PiLp.ext
    intro k
    fin_cases k
    rfl
  have right:shape a ((center a) 0) B 1 (fun e=>t 1 e)=B.r (after (n:=1) (m:=1) t):=by
    apply congr_arg B.r
    apply PiLp.ext
    intro k
    fin_cases k
    rfl
  have rejoin:closedUp a (earlier a (n:=1) (m:=1) t) (after (n:=1) (m:=1) t)=t:=
    (pairIso (n:=1) (m:=1) a).symm_apply_apply t
  rw [Fin.prod_univ_two,left,right]
  exact (congrArg (fun s=>profile arm a B i j s) rejoin.symm).trans
    (WilsonPositionProgramPublicWideHearing.read arm a B i j _ _)

omit [Fintype I] [l.NeBot] in
theorem original (R:Run G)(Q:Fin 2→SealR G)(a:Axis)(B:Bulb (center a) a)(y:ℝ):
    ∃T:Wilt Q,(∃fees:Fin 2→ℝ,∀ᶠZ:ℝ in atTop,Bough Q T y Z fees) ∧
      ∀(i j:I){r:ℝ}(rp:0<r)(m K:ℕ)(o:CellR)(z:Fin 2 → Cover),
        mass (profile arm a B i j) (R.family.S.a K) r z=
          ∫ξ in cube 1 1 (0:Fin 2 → Cover),
            ((∏k,price R (T k) (Q k).h rp m K y o (z k) (fun e=>ξ k e):ℝ):ℂ):=by
  obtain ⟨T,write,fees⟩:=WilsonPositionProgramReflectedPurse.original Q a ((center a) 0) B y
  refine ⟨T,fees,?_⟩
  intro i j r rp m K o z
  apply WilsonPositionProgramTrialPublicCellProduct.original R (fun k=>(Q k).D) (fun k=>(Q k).h) T rp m K y o z
  intro t
  simpa only [write] using printed arm a B i j t

end YM.Integration.WilsonPositionProgramTrialPublicReflectedProduct
end
