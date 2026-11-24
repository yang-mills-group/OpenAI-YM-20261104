import YM.Integration.WilsonOriginalPublicTwoTopSplice
import YM.Integration.WilsonPositionProgramNormalizedMaster

/-! A common finite measured input is expanded on each top's own normalized bank. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonOriginalPublicTwoTopJoined
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider Source Source.Drops Labels
open WilsonMarkedIndependentNormalizedElection (deck normalized)
open scoped Topology BigOperators Classical
variable {G : Gauge} {a h D k u e : ℕ}

def Hearing (Q : Fin (a+1) → SealR G) (L : Levels G) (Ñ : ChartRatio G) (clock : ℕ → ℝ)
    (j e u : ℕ) (C C' wallet : Credit) : Prop :=
  ∀ (m K N : ℕ) (X : Herit Q) (F : Wilt Q) (B : Fin (a+1) → ℝ) (Z y : ℝ) (o : CellR),
    j ≤ m → m ≤ K → K ≤ N → clock m ≤ Z → Bough Q F y Z B →
    let V := normalized L Ñ Q X m
    let T := ∏ i, B i * (wallet.buy (clock m) * WilsonPositionProgramNormalizedMaster.fee X e i)
    let δ := trailC L.S m K
    loadK L Ñ F (V N) m N N y o = loadK L Ñ F (V N) m K N y o +
      ∑ i ∈ range (N-K), stopX L Ñ F (V N) m (K+i) N y o ∧
    Fringed (capP Q) e u 1 (2*(C.buy Z*T)) δ
      (loadK L Ñ F (V N) m N N y o) (loadK L Ñ F (V N) m K N y o) ∧
    ∀ i, K ≤ i → Fringed (capP Q) e u 1 (C'.buy Z * trailC L.S m i*T) δ
      (stopX L Ñ F (V N) m i N y o) 0

theorem original (R : Run G) (simple : G.Simple) (v : ℕ → Gear G → ℝ)
    (funded : FundedMarkedCoverRows.prices v R.kit) (p : h < D)
    (rails : Rails h k u e) (l d : Fin (a+1) → ℕ) (admit : ∀ i, l i < d i)
    (cap : capP (deck (G:=G) l d admit) ≤ k) :
    let Q := deck (G:=G) l d admit
    let L := R.family.path.levels
    ∃ C C' wallet : Credit, ∀ᶠ j : ℕ in atTop, Hearing Q L R.metals.O (zz L) j e u C C' wallet := by
  intro Q L
  obtain ⟨C,C',split⟩ := WilsonOriginalPublicTwoTopSplice.original (hol G) Q Credit.leanC Credit.leanC
    Credit.leanC Credit.leanC Credit.leanC e u
  obtain ⟨wallet,lens⟩ := steering (hol G) Q e Credit.leanC Credit.leanC Credit.leanC Credit.leanC
  refine ⟨C,C',wallet,?_⟩
  filter_upwards [WilsonMarkedIndependentNormalizedElection.original R simple v funded p rails l d admit cap]
    with j filed
  obtain ⟨W,Y,level,cash,clock,date,agree,dorm,spring,frames,ready⟩ := filed
  have heard : Hearing Q Y.L.V.draws Y.L.V.paid Y.L.V.y Y.L.V.anchor e u C C' wallet := by
    intro m K N X F B Z y o awake base fine room bough
    let A := WilsonPositionProgramNormalizedMaster.fee X e
    let T := normalized Y.L.V.draws Y.L.V.paid Q X m
    have both := lens Y.L.V frames m awake A (fun _=>X)
      (WilsonPositionProgramNormalizedMaster.shipped X e Y.L.V.draws.S m)
    have priced := split Y.L.V ready spring dorm m K N F (T N) (T K)
      (fun i => wallet.buy (Y.L.V.y m)*A i) B Z y (trailC Y.L.V.draws.S m K) o
      awake base fine room bough le_rfl (both N K K base fine le_rfl)
    exact ⟨WilsonOriginalPublicTwoTopSplice.history ready F (T N) y o awake base fine,priced⟩
  rwa [level,cash,clock,date] at heard

end YM.Integration.WilsonOriginalPublicTwoTopJoined
end
