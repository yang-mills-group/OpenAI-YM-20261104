import YM.Integration.WilsonPositionProgramTrialNativeHome
import YM.Integration.WilsonIndependentMatchedPhysicalReturn
/-! Reading the fitted peer in the same normalized public coordinates without a power of the planting depth. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentMatchedPhysicalPeer
open Function Filter Finset Matrix Lattice Wilson RG RG.Supply Precision Source Labels Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato XSpace PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Power WilsonCoeffUV.Embroider
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank.PathCost
open WilsonPositionProgramTrialAccrued (home)
open WilsonIndependentMatchedFittedSeat (dose)
open WilsonMarkedIndependentNormalizedElection (deck)
open scoped BigOperators Classical
variable {G:Gauge}{h D k u e:ℕ}
local notation "CC" => Credit.leanC

def reading (q:ℕ)(g:ℝ):PowerSeries ℝ→ₗ[ℝ]ℝ:=
  ∑i∈Finset.range (q+1),g^i • (coeff i:PowerSeries ℝ→ₗ[ℝ]ℝ)

def amount {Q:SealR G}(φ:PowerSeries ℝ→ₗ[ℝ]ℝ)(x:Q.Rider):ℝ:=
  ∑i:Alma Q.F,‖φ (x i)‖

theorem bound (Q:SealR G){H:Hol G}{v:Rails Q.h k u e}{E W V U:Credit}
    (X:CutsP H Q.ans Q.path v E W V U)(φ:PowerSeries ℝ→ₗ[ℝ]ℝ)(D:ℝ)
    (paid:∀i j,‖(Wray X.ax X.tx Q.ans Q.path X.N X.m)⁻¹ i j‖ ≤ D):
    amount (Q:=Q) φ (dose X 1) ≤ (Fintype.card (Alma Q.F):ℝ)*D*amount (Q:=Q) φ (home Q X):=by
  have same:= (WilsonPositionProgramTrialHomeDose.original Q X 1).1
  rw [WilsonPositionProgramTrialHomeDose.scaled,one_smul] at same
  rw [←same]
  let M:=(Wray X.ax X.tx Q.ans Q.path X.N X.m)⁻¹
  have row i:‖φ ((PermuteLens X.ax X.tx Q X.N X.m (home Q X)) i)‖ ≤ D*amount (Q:=Q) φ (home Q X):=by
    unfold PermuteLens
    simp only [map_sum,map_smul,smul_eq_mul]
    change ‖∑j,M i j*φ (home Q X j)‖ ≤ _
    unfold amount
    rw [Finset.mul_sum]
    apply (norm_sum_le ..).trans
    apply Finset.sum_le_sum
    intro j _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (paid i j) (norm_nonneg _)
  calc
    _  ≤  ∑_i:Alma Q.F,D*amount (Q:=Q) φ (home Q X):=Finset.sum_le_sum (fun i _=>row i)
    _ = _:=by simp [mul_assoc]

theorem original (R:Run G)(simple:G.Simple)(v:ℕ → Gear G → ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (fit:h<D)(rails:Rails h k u e):
    let Q:=WilsonPositionProgramTrialNativeHome.reporter (G:=G) fit
    let L:=R.family.path.levels
    ∃B:Credit,∀ᶠ j:ℕ in atTop,∀m K N,j ≤ m → m ≤ K → K ≤ N → 
    ∀X:CutsP (hol G) Q.ans Q.path rails CC CC CC CC,X.ax=L  →  X.tx=R.metals.O  →  X.N=N  →  X.m=m  → 
    ∀φ:PowerSeries ℝ→ₗ[ℝ]ℝ,amount (Q:=Q) φ (dose X 1) ≤ 
      (Fintype.card (Alma Q.F):ℝ)*B.buy (zz L m)*amount (Q:=Q) φ (home Q X):=by
  intro Q L
  obtain ⟨B,inv⟩:=belt (C:=CC) (T:=Q.ans) (p:=Q.path) (e:=e) (H:=hol G) (E:=CC) (W:=CC)
  let labels:Fin 1 → ℕ:=fun _=>h
  let dims:Fin 1 → ℕ:=fun _=>D
  have count:capP (deck (G:=G) labels dims (fun _=>fit)) ≤ k:=by
    simpa [capP,asp,deck,BayV,labels,dims] using rails.hk
  refine ⟨B,?_⟩
  filter_upwards [WilsonMarkedIndependentNormalizedElection.original R simple v funded fit rails labels dims
    (fun _=>fit) count] with j sale
  obtain ⟨_,chair,levels,clock,calendar,start,_,_,_,frames,_⟩:=sale
  intro m K N early before live X lx ox nN mM φ
  let bidder:AheadT (hol G) chair.L.V CC CC Q CC:=(frames 0).some
  have awake:bidder.p.f.arch.V.anchor ≤ m:=bidder.p.tap ▸ (start ▸ early)
  apply bound
  intro i s
  rw [lx,ox,nN,mM]
  have quote:=(inv bidder.p.f.arch bidder.stamps m m N N awake le_rfl (before.trans live) (before.trans live) i s).main
  simpa only [Realm.cash,bidder.p.lands,bidder.p.modes,bidder.p.depths,levels,clock,calendar] using quote

end YM.Integration.WilsonIndependentMatchedPhysicalPeer
