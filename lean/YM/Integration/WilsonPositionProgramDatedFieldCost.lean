import YM.Integration.WilsonPositionProgramNormalizedMaster
import YM.WilsonCoeffUV.Marked.Bounds.Independent

/-! The finite filed upper series costs polynomially in its actual measured
clock interval, including the inversion of the normalized master at its reporter. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true

namespace YM.Integration.WilsonPositionProgramDatedFieldCost
open Function Finset Filter Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Shard WilsonCoeffUV.Soil
open WilsonCoeffUV.Blue WilsonCoeffUV.Embroider WilsonCoeffUV.Power
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open Source Source.Drops Labels PowerSeries
open scoped BigOperators Classical Topology
variable {G : Gauge} {a h D k u e : ℕ}
local notation "c₀" => Credit.leanC

theorem priced (P : SealR G) (e : ℕ) :
    ∃ C B : Credit, ∀ (S : Realm G (e+1) c₀) (_stamp : AheadT (hol G) S c₀ c₀ P c₀),
      ∀ m M, S.anchor ≤ m → m ≤ M → ∀ X : P.Rider, ∀ A : ℝ, 0≤A →
      (∀ i≤e, ∀ s, ‖coeff i (X s)‖ ≤ A) →
      let x := PermuteLens S.draws S.paid P M m X
      ∀ i≤e, ∀ s, ‖coeff i (steep S.draws S.paid P.ans P.path M m (M-m) x s)‖ ≤
        C.buy (Compar S.draws.S S.y m M) * (B.buy (S.y m)*A) := by
  obtain ⟨C,stepped⟩ := agesQuote (hol G) P.ans P.path e c₀ c₀ c₀
  obtain ⟨B,chart⟩ := colormoon (hol G) P e c₀ c₀ c₀ c₀
  refine ⟨C,B,?_⟩
  intro S stamp m M active later X A hA cash x i hi s
  let V := stamp.p.f.arch.V
  let W : CourseS (hol G) P.ans P.path e c₀ c₀ c₀ :=
    ⟨stamp.p.f,⟨V,m,M-m,M,M,M,stamp.p.tap.symm ▸ active,by omega,le_rfl,le_rfl⟩,rfl⟩
  have x0 := chart S stamp X X m m M M active le_rfl later later A hA
    (fun i hi s => twain.one _ _ (trail_pos ..).le (cash i hi s))
  have hcost : 0 ≤ B.buy (S.y m)*A := mul_nonneg (zero_le_one.trans (B.purchase (S.depth m active))) hA
  have out := (stepped W x x (B.buy (S.y m)*A) W.cab hcost le_rfl
    (fun t ht y => twain.one _ _ (trail_pos ..).le (x0 t ht y).main) i hi s).main
  change ‖coeff i (steep V.draws V.paid P.ans P.path M m (M-m) x s)‖ ≤ C.buy W.Age * _ at out
  have age : W.Age = Compar S.draws.S S.y m M := by
    change V.y m + (V.draws.S.scale (m+(M-m))-V.draws.S.scale m) + (M-m:ℕ) = _
    rw [Nat.add_sub_of_le later,show V.draws=S.draws from stamp.p.lands,
      show V.y=S.y from stamp.p.depths]
    rfl
  rwa [show V.draws=S.draws from stamp.p.lands,show V.paid=S.paid from stamp.p.modes,age] at out

open WilsonMarkedIndependentNormalizedElection (deck)
variable (R : Run G)
theorem original (simple : G.Simple) (v : ℕ → Gear G → ℝ)
    (funded : FundedMarkedCoverRows.prices v R.kit) (p : h < D)
    (rails : Rails h k u e) (l d : Fin (a+1) → ℕ) (admit : ∀ i,l i < d i)
    (cap : capP (deck (G:=G) l d admit) ≤ k) :
    let Q := deck (G:=G) l d admit
    let L := R.family.path.levels
    ∃ C B : Fin (a+1) → Credit, ∀ᶠ j : ℕ in atTop, ∀ (m M : ℕ), j ≤ m → m ≤ M → ∀ X : Herit Q,
      ∀ b, let x := PermuteLens L R.metals.O (Q b) M m (X b)
      ∀ i≤e, ∀ s, ‖coeff i (steep L R.metals.O (Q b).ans (Q b).path M m (M-m) x s)‖ ≤
        (C b).buy (Compar L.S (zz L) m M) *
          ((B b).buy (zz L m)*WilsonPositionProgramNormalizedMaster.fee X e b) := by
  intro Q L
  choose C B rates using fun b => priced (Q b) e
  refine ⟨C,B,?_⟩
  filter_upwards [WilsonMarkedIndependentNormalizedElection.original R simple v funded p rails l d admit cap]
    with j acquired
  obtain ⟨W,Y,levels,ratio,calendar,start,_,_,_,frames,_⟩ := acquired
  intro m M hm hM X b x i hi s
  let A := WilsonPositionProgramNormalizedMaster.fee X e
  have X0 := WilsonPositionProgramNormalizedMaster.shipped X e L.S m M M m le_rfl hM hM
  obtain ⟨stamp⟩ := frames b
  have out := rates b Y.L.V stamp m M (start ▸ hm) hM (X b) (A b) (X0.stock b)
    (fun t ht y => (X0.track b t ht y).main) i hi s
  rwa [levels,ratio,calendar] at out

end YM.Integration.WilsonPositionProgramDatedFieldCost
end
