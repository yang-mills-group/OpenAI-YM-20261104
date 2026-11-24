import YM.Integration.WilsonIndependentMatchedFiledIncome
import YM.Integration.WilsonIndependentMatchedCoverProfile

/-! The complete appointed finite source and its fitted complement enter a common horizon.
The weight-four column is filed at its own engineering weight before its inverse is restored. -/
set_option autoImplicit false
set_option maxHeartbeats 9500000
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedFiledAtSix
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open PhysicalNext.Repeat.Legato XSpace.Rose XSpace.Cirrus XSpace
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical
variable {G:Gauge}{d D k e u:ℕ}{F:Labels.Frame G 6}

def decay {H:Hol G}{T:SectionData F}{p:6<D}{v:Rails 6 k u e}{E W K U:Credit}
    (X:CutsP H T p v E W K U)(i:ℕ):ℝ:=
  Real.exp (-(X.vesselsC.draws.S.scale X.ceilC-X.vesselsC.draws.S.scale (X.m+i))/4)

/-- The two optical endpoints and the upper fitted verse belong to the same
dated cover. Its stable part has the restored, unamplified fee at every held rank. -/
theorem original (R:Run G)(W₀:Initialize G)(survey:Bool)(hd:d≤6)(p:6<D)
    (capacity:d≤k)(H:Hol G)(T:SectionData F)(v:Rails 6 k u e)(E W K U:Credit):
    let Td:=WilsonIndependentMatchedNamedPair.sectionAt R W₀ survey d
    let P:=Shrine (WilsonIndependentMatchedFiledIncome.plate Td (hd.trans_lt p))
    ∃ A:Alma (R.family.labels.level d)→ℝ,(∀i,0≤A i) ∧ ∃ C:Credit,
    ∀ (L:Torch H T p v E W K)(L':ChorusLine H T p e E W U)(_same:L'.arch=L.L)
      (m s:ℕ)(_live:L.L.V.anchor ≤ m)(c:Verse (R.family.labels.level d))(δ:ℝ)(_hd:0<δ),
      let a:=δ^(6-d)
      let fee:=WilsonIndependentMatchedFiledIncome.charge e c A
      ∃ X:CutsP H T p v E W K U,
      X.L=L ∧ X.m=m ∧ X.i=s ∧ X.N=m+s ∧ X.pt=a • P c ∧ X.fuel=a*fee ∧
      X.springP X.i=a • P c-Shrine X.Ntop X.tileP ∧
      (∀i:ℕ,i<X.i→Spout X.ax X.tx X.N (X.m+i) 6 k (X.springP (i+1))=X.springP i) ∧
      ∀(i:ℕ)(_hi:i≤X.i)(φ:Rarity D)(x y:ℝ)(o:CellR)(l:ℕ)(S:Patch)
        (_hx:0<x)(_hx':x≤1)(B:ℝ)(_hf:Amplitude φ B),
        Income (word (a⁻¹ • X.springP i) φ x y o l) k e u (OrbP S φ x y o)
          (WilsonIndependentMatchedCoverProfile.charge φ u l x y (C.buy X.Age*decay X i*fee) B) := by
  dsimp only
  obtain ⟨A,nn,admitted⟩:=WilsonIndependentMatchedFiledIncome.named R W₀ survey d
    (hd.trans_lt p) capacity e u
  obtain ⟨C,read⟩:=WilsonIndependentMatchedCoverProfile.original H T p v E W K U
  refine ⟨A,nn,C,?_⟩
  intro L L' same m s live c δ hd'
  let a:=δ^(6-d)
  have ha:0<a:=pow_pos hd' _
  let P:=Shrine (WilsonIndependentMatchedFiledIncome.plate
    (WilsonIndependentMatchedNamedPair.sectionAt R W₀ survey d) (hd.trans_lt p)) c
  let fee:=WilsonIndependentMatchedFiledIncome.charge e c A
  have paid:=admitted c
  let X:=WilsonIndependentMatchedKernelResidual.diagonal L L' same m s (m+s) live le_rfl
    (a • P) (paid.1.μ a) (a*fee) (mul_nonneg ha.le paid.2.1) (by
      intro j r hj
      have row:=(show Award (P.2 j r) _ fee from paid.2.2 j r hj).μ a
      rw [abs_of_pos ha] at row
      exact row)
  refine ⟨X,rfl,rfl,rfl,rfl,rfl,rfl,X.carve1,fun _ hi=>X.carve2 hi,?_⟩
  intro i hi φ x y o l S hx hx' B hf
  have cost : price X C i a⁻¹=C.buy X.Age*decay X i*fee := by
    unfold WilsonIndependentMatchedCoverProfile.price decay
    rw [show X.fuel=a*fee from rfl,abs_of_pos (inv_pos.mpr ha)]
    field_simp [ha.ne']
  simpa only [cost] using read X i hi a⁻¹ φ x y o l S hx hx' B hf

end YM.Integration.WilsonIndependentMatchedFiledAtSix
