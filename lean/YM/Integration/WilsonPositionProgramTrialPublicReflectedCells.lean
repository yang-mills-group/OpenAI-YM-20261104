import YM.Integration.WilsonPositionProgramTrialPublicCellRoom

/-! A single reflected public packet before all dates and cell offsets. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicReflectedCells
open Function Filter Finset Set MeasureTheory WithLp Lattice Extraction RG Wilson Source
open Extra.Histories Spec PhysicalNext.Repeat.Legato Table.Pairing PhysMS MS MS.Menus XSpace Local.Physical
open WilsonCoeffUV WilsonCoeffUV.Layout WilsonCoeffUV.Mer WilsonCoeffUV.Embroider
open WilsonPositionProgramReflectedPurse (shape)
open WilsonPositionProgramPublicReflectedRead (center)
open WilsonPositionProgramPublicWideHearing (profile)
open WilsonThermometerUnitFilingFourSquare
open WilsonPositionProgramTrialPublicCellProduct (price)
open WilsonPositionProgramTrialPublicCellPulse (placed)
open WilsonPositionProgramTrialPublicCellRoom (room)
open WilsonMeasuredPublicEntranceCoverCells (cube mass)
open scoped Classical BigOperators
variable {G:Gauge}{I:Type}{C:Family G}{S:Table C.book}
  {l:Filter (ℕ×ℕ)} {d:ℕ} {v:I→S.Field d}
  (arm:(i:I)→Bool→Arm C S l d (v i))

theorem bounded {n:ℕ}{ξ:Points n}(live:ξ∈cube 1 1 (0:Fin n → Cover))(i:Fin n):
    ‖(fun e=>ξ i e:Point4)‖≤1:=by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).2
  intro e
  have each:=congrFun (congrFun (show Extraction.address 1 ((1:ℝ) • ξ)=(0:Fin n → Cover) from live) i) e
  have whole:⌈ξ i e⌉=0:=by simpa [Extraction.address] using each
  have low:=Int.ceil_lt_add_one (ξ i e)
  have high:=Int.le_ceil (ξ i e)
  rw [whole,Int.cast_zero] at low high
  change |ξ i e|≤1
  exact abs_le.mpr ⟨by linarith only [low],by linarith only [high]⟩

theorem original (R:Run G)(Q:Fin 2→SealR G)(a:Axis)(B:Bulb (center a) a):
    ∃(T:Wilt Q)(M:Fin 2→ℝ)(Z:ℝ),Bough Q T 0 Z M ∧
      ∀{r:ℝ}(rp:0<r)(m K:ℕ)(y:ℝ)(o:CellR),
        let x:=paceT R.family.S m K
        let σ:=r/R.family.S.a m
        let sp:=div_pos rp (R.family.S.a_pos m)
        (∀(i j:I)(z:Fin 2 → Cover),mass (profile arm a B i j) (R.family.S.a K) r z=
          ∫ξ in cube 1 1 (0:Fin 2 → Cover),
            ((∏k,price R (T k) (Q k).h rp m K y o (z k) (fun e=>ξ k e):ℝ):ℂ)) ∧
        (|y|≤Z→4*x≤σ*Z⁻¹→∀ξ∈cube 1 1 (0:Fin 2 → Cover),
          Bough Q (fun i=>placed (T i) x y σ sp o (fun e=>ξ i e)) y (room y Z x σ o)
            (fun i=>σ⁻¹^4*((max 1 σ⁻¹)^(Q i).D*M i))):=by
  obtain ⟨T,write,M,late⟩:=WilsonPositionProgramReflectedPurse.original Q a ((center a) 0) B 0
  obtain ⟨Z,original⟩:=late.exists
  refine ⟨T,M,Z,original,?_⟩
  intro r rp m K y o x σ sp
  constructor
  · intro i j z
    apply WilsonPositionProgramTrialPublicCellProduct.original R (fun k=>(Q k).D) (fun k=>(Q k).h) T rp m K y o z
    intro t
    simpa only [write] using WilsonPositionProgramTrialPublicReflectedProduct.printed arm a B i j t
  · intro fit fine ξ live
    have rephased:Bough Q T y Z M:=⟨original.pos,original.lanes,original.rents,fit,original.seats⟩
    exact WilsonPositionProgramTrialPublicCellRoom.original Q T y Z x σ o M rephased (pace_pos ..).le
      sp fine (fun i e=>ξ i e) (bounded live)

end YM.Integration.WilsonPositionProgramTrialPublicReflectedCells
end
