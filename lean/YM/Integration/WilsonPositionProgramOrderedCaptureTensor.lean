import YM.Integration.WilsonPositionProgramNormalizedMaster

/-! Choose the truncated microscopic history at a fixed report and tolerance.
The same submitted field, proper mask and profile are used in both programs.
Their two top cutoffs may be chosen after the bound. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonPositionProgramOrderedCaptureTensor
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Bank.PathCost
open WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider Source Source.Drops Labels
open scoped Topology BigOperators Classical
variable {G:Gauge}{a h D k u e:ℕ}

open WilsonMarkedIndependentNormalizedElection (deck normalized)



theorem original (R:Run G)(simple:G.Simple)(v:ℕ→Gear G→ℝ)(paid:FundedMarkedCoverRows.prices v R.kit)
    (big:h<D)(rails:Rails h k u e)(l d:Fin (a+1)→ℕ)(fit:∀i,l i<d i)
    (cap:capP (deck (G:=G) l d fit) ≤ k):
    let Q:=deck (G:=G) l d fit
    let L:=R.family.path.levels
    ∃c wallet:Credit,∀ᶠ j:ℕ in atTop,∀m:ℕ, j ≤ m → ∀F ε:ℝ, 0 ≤ F → 0 < ε →
    ∃K:ℕ,m ≤ K ∧ F * trailC L.S m K < ε ∧
    ∀N M:ℕ,K ≤ N → K ≤ M → ∀X:Herit Q,
    ∀b:ℕ,j ≤ b → b ≤ m → ∀(φ:Wilt Q)(B:Fin (a+1)→ℝ)(y Z:ℝ)(o:CellR),
    Compar L.S (zz L) b m ≤ Z → Bough Q φ y Z B →
    c.buy Z * ∏i,B i*(wallet.buy (zz L m)*WilsonPositionProgramNormalizedMaster.fee X e i) ≤ F →
    let capture:=fun n=>locale o (LodeStar L R.metals.O φ
      (normalized L R.metals.O Q X m n) m b n y)
    Fringed (capP Q) e u 1 F (trailC L.S m K) (capture N) (capture M) := by
  intro Q L
  obtain ⟨c,capture⟩:=Captures (hol G) Q Credit.leanC Credit.leanC Credit.leanC Credit.leanC Credit.leanC e u
  obtain ⟨wallet,lens⟩:=steering (hol G) Q e Credit.leanC Credit.leanC Credit.leanC Credit.leanC
  refine ⟨c,wallet,?_⟩
  filter_upwards [WilsonMarkedIndependentNormalizedElection.original R simple v paid big rails l d fit cap]
    with j full
  obtain ⟨W,Y,level,ratio,clock,date,_,dorm,spring,frames,ready⟩:=full
  have funded:∀m:ℕ,Y.L.V.anchor ≤ m → ∀F ε:ℝ,0 ≤ F → 0<ε →
      ∃K:ℕ,m ≤ K ∧ F*trailC Y.L.V.draws.S m K<ε ∧
      ∀N M:ℕ,K ≤ N → K ≤ M → ∀X:Herit Q,∀b:ℕ,Y.L.V.anchor ≤ b → b ≤ m →
      ∀(φ:Wilt Q)(B:Fin (a+1)→ℝ)(y Z:ℝ)(o:CellR),
      Compar Y.L.V.draws.S Y.L.V.y b m ≤ Z → Bough Q φ y Z B →
      c.buy Z*∏i,B i*(wallet.buy (Y.L.V.y m)*WilsonPositionProgramNormalizedMaster.fee X e i) ≤ F →
      let read:=fun n=>locale o (LodeStar Y.L.V.draws Y.L.V.paid φ
        (normalized Y.L.V.draws Y.L.V.paid Q X m n) m b n y)
      Fringed (capP Q) e u 1 F (trailC Y.L.V.draws.S m K) (read N) (read M) := by
    intro m allowed F ε _ pos
    have decays:Tendsto (fun n=>F*trailC Y.L.V.draws.S m n) atTop (𝓝 0):=by
      simpa using (fade Y.L.V.draws.S m).const_mul F
    have good:∀ᶠ n in atTop,F*trailC Y.L.V.draws.S m n<ε:=decays (Iio_mem_nhds pos)
    obtain ⟨n,enough⟩:=eventually_atTop.mp good
    let K:=max m n
    have stop:m ≤ K:=le_max_left ..
    refine ⟨K,stop,enough K (le_max_right ..),?_⟩
    intro N M old old' X b start later φ B y Z o room shape wage
    let prices:=WilsonPositionProgramNormalizedMaster.fee X e
    have shipped:=lens Y.L.V frames m allowed prices (fun _=>X)
      (WilsonPositionProgramNormalizedMaster.shipped X e Y.L.V.draws.S m)
    have dates:=PadRank.frugal Y.L.V start later
    have pad:PadRank Y.L.V b m Z:=⟨fun i hi hj=>(dates.year i hi hj).trans room,dates.lengthS.trans room⟩
    exact (capture Y.L.V ready spring dorm m K b N M φ _ _ _ B Z y _ o start later stop
      old old' pad shape le_rfl (shipped N M K stop old old')).pay wage
  rwa [level,ratio,clock,date] at funded

end YM.Integration.WilsonPositionProgramOrderedCaptureTensor
end
