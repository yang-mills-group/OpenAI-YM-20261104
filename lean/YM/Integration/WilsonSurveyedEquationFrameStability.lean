import YM.Integration.WilsonSurveyedEquationFrameRegulated
import YM.Integration.WilsonIndependentMatchedKernelResidual

/-! At the actual appointed fresh top compare an arbitrary submitted group
section with its measured coordinates in the surveyed physical/Ward section.
The quarter-power multiplies the submitted rooted salary. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
namespace YM.Integration.WilsonSurveyedEquationFrameStability
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Bank.PathCost
open WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider Source Source.Drops Labels XSpace
open WilsonSurveyedEquationFrameInlet (bank master loan price)
open WilsonIndependentMatchedFiledIncome (plate charge)
open WilsonMarkedIndependentNormalizedElection (deck)
open scoped Topology BigOperators Classical
variable {G : Gauge} (R : Run G) (W : Initialize G) {h D k u e : ℕ}
local notation "L" => R.family.path.levels
local notation "O" => R.metals.O
local notation "CC" => Credit.leanC

def Outpost (w : h < D) (v : Rails h k u e) (j : ℕ) : Prop :=
  ∃(Y : Torch (hol G) (bank W h).joined w v CC CC CC)
   (A : ChorusLine (hol G) (bank W h).joined w e CC CC CC),
    Y.L.V.draws = L ∧ Y.L.V.paid = O ∧ Y.L.V.y = zz L ∧ Y.L.V.anchor = j ∧ A.arch = Y.L

theorem course (simple : G.Simple) (v : ℕ → Gear G → ℝ)
    (funded : FundedMarkedCoverRows.prices v R.kit) (granted : price W R.kit)
    (w : h < D) (rails : Rails h k u e) (cap : capP (deck (G:=G)
      (fun _ : Fin 1=>h) (fun _=>D) (fun _=>w)) ≤ k) :
    ∀ᶠ j:ℕ in atTop, Outpost R W w rails j := by
  let Q := fun _ : Fin 1 => loan W h D w
  have invoice := reported (hol G) (master W) granted.1 granted.2
  have capacity : capP Q ≤ k := cap
  filter_upwards [PortsTogether simple (chart_ok G) R.alloy.B.valid invoice tendsto_id
    w rails Q (fun _ => rfl) capacity] with j sur
  obtain ⟨A,Y,ax,tx,clk,j0,_,joined,_⟩ := sur
  exact ⟨Y,A,joined ▸ ax,joined ▸ tx.trans funded.1.symm,joined ▸ clk,joined ▸ j0,joined⟩

/-- The purchased incoming group need not be the section of the fitted
physical pivots. Its submitted function determines the complete measured tally. -/
theorem original (simple : G.Simple) (v : ℕ → Gear G → ℝ)
    (funded : FundedMarkedCoverRows.prices v R.kit) (granted : price W R.kit)
    (w : h < D) (rails : Rails h k u e) (cap : capP (deck (G:=G)
      (fun _ : Fin 1=>h) (fun _=>D) (fun _=>w)) ≤ k)
    {d : ℕ} {F : Frame G d} (S : SectionData F) (s : d < D) (height : d ≤ k)
    {H : Hol G} (sound : S.Sound H) (printed : Bid.pop S) :
    ∃(C : Credit) (A : Alma F → ℝ), (∀i,0 ≤ A i) ∧ ∀ᶠ j:ℕ in atTop,
      ∀m K, j ≤ m → m ≤ K → ∀c : Verse F,
      ∃ X : CutsP (hol G) (bank W h).joined w rails CC CC CC CC,
        X.ax = L ∧ X.tx = O ∧ X.m = m ∧ X.ceilC = K ∧ X.N = K ∧
        X.pt = Shrine (plate S s) c ∧ X.fuel = charge e c A ∧
        X.Ntop = plate (bank W h).joined w ∧
        X.springP X.i = X.pt - Shrine X.Ntop X.tileP ∧
        (∀i<X.i, Spout L O K (m+i) h k (X.springP (i+1)) = X.springP i) ∧
        ∀t≤e,∀i≤X.i,∀r:ℕ, Fruit 0 1 u ((X.springP i).2 t r)
          (C.buy X.Age * Real.exp (-((L).S.scale K - (L).S.scale (m+i))/4) * charge e c A) := by
  obtain ⟨C,stable⟩ := WilsonIndependentMatchedKernelResidual.original (hol G) (bank W h).joined w rails CC CC CC CC
  obtain ⟨A,nn,source⟩ := WilsonIndependentMatchedFiledIncome.original S s H sound printed height e u
  refine ⟨C,A,nn,?_⟩
  filter_upwards [course R W simple v funded granted w rails cap] with j appointments
  obtain ⟨l,a,levels,clock,_,start,joint⟩ := appointments
  intro m K late here c
  let X := WilsonIndependentMatchedKernelResidual.diagonal l a joint m (K-m) K
    (start.trans_le late) (by omega) (Shrine (plate S s) c) (source c).1
    (charge e c A) (source c).2.1 (source c).2.2
  have date : X.ceilC = K := Nat.add_sub_of_le here
  have film : X.Ntop = plate (bank W h).joined w := by
    change Peaks l.L.V.draws l.L.V.paid (bank W h).joined w K X.ceilC = _
    rw [date,Peak_initial]
    rfl
  obtain ⟨dropped,next,bill⟩ := stable X
  refine ⟨X,levels,clock,rfl,date,rfl,rfl,rfl,film,dropped,?_,?_⟩
  · intro i hi
    have value := next i hi
    change Spout l.L.V.draws l.L.V.paid K (m+i) h k (X.springP (i+1)) = X.springP i at value
    rwa [levels,clock] at value
  · intro t ht i hi r
    have fee := bill t ht i hi r
    change Fruit 0 1 u _ (C.buy X.Age * Real.exp (-(l.L.V.draws.S.scale X.ceilC -
      l.L.V.draws.S.scale (m+i))/4) * charge e c A) at fee
    rwa [levels,date] at fee

end YM.Integration.WilsonSurveyedEquationFrameStability
