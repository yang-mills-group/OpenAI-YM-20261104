import YM.Integration.WilsonIndependentFittedShrineFaces
import YM.Integration.WilsonIndependentMatchedFiledAtHorizon

/-! The complete fitted verse and its stable complement have a common earned salary at any fixed horizon. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentFittedCommonHorizon
open Finset Lattice RG Wilson Source Labels PhysicalNext.Repeat.Legato XSpace XSpace.Rose XSpace.Cirrus
open WilsonCoeffUV WilsonCoeffUV.Cosmos WilsonCoeffUV.Soil WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Bank WilsonCoeffUV.Power PowerSeries PertExtension Orb.SlotEvaluation FVA2
open Function Matrix Laurent Bloch Metric FreeResolvent Work.F08 Tree
open Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source.Drops Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Realm PathCost Ore
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonIndependentMatchedTopFilm (dose)
open WilsonIndependentMatchedCoverProfile (Income word)
open WilsonPhysicalMarkedDefect.RawProduct (belt)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(W:Initialize G){d h D k e u:ℕ}
    (survey target:Bool)(hd:d≤h)(p:h<D)(capacity:d≤k)(H:Hol G)(v:Rails h k u e)(E A K U:Credit)
local notation "T" => sectionAt R W target h

private theorem scale (Q:ℕ)(c:ℂ)(f:PowerSeries ℂ):
    belt Q (PowerSeries.C c*f)=‖c‖*belt Q f:=by
  unfold WilsonPhysicalMarkedDefect.RawProduct.belt
  rw [mul_sum]
  apply sum_congr rfl
  intro j _
  rw [coeff_C_mul,norm_mul]

/-- Each top, thermal table, derivative tap, and signed scalar dose is selected after the
credit has been assigned. This can be applied to a top selected by another enrolled receiver. -/
theorem salary:
    ∃V:Credit,∀X:CutsP H T p v E A K U,∀b:Volume D,∀Q≤e,
    ∀a fee:ℝ,0<a → X.fuel=a*fee → ∀z:ℂ,
      (∑i,belt Q (PowerSeries.C (z*((a⁻¹:ℝ):ℂ))*dose R p X.tileP b i))≤
        ((Q+1:ℕ):ℝ)*V.buy X.Age*(‖z‖*fee)*(∑i:Alma (R.family.labels.level h),|jewelBloom p i b|):=by
  obtain ⟨V,book⟩:=WilsonIndependentFittedShrineSalary.portfolio R W target p H v E A K U
  refine ⟨V,fun X b Q cap a fee warm actual z=>?_⟩
  simp_rw [scale]
  rw [←mul_sum]
  refine (mul_le_mul_of_nonneg_left (book X b Q cap) (norm_nonneg _)).trans_eq ?_
  rw [actual,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_inv,abs_of_pos warm]
  field_simp

include capacity in
/-- The same returned X pays the whole stable marked field at the downstream real tests
and the entire signed, compensated numerical coordinate list. -/
theorem original:
    let Td:=sectionAt R W survey d
    let P:=Shrine (WilsonIndependentMatchedFiledIncome.plate Td (hd.trans_lt p))
    ∃F:Alma (R.family.labels.level d)→ℝ,(∀i,0≤F i) ∧ ∃C V:Credit,
    ∀(B:Torch H T p v E A K)(B':ChorusLine H T p e E A U)(_same:B'.arch=B.L)
      (m s:ℕ)(_live:B.L.V.anchor ≤ m)(c:Verse (R.family.labels.level d))(δ:ℝ)(_pos:0<δ),
      let a:=δ^(h-d)
      let fee:=WilsonIndependentMatchedFiledIncome.charge e c F
      ∃X:CutsP H T p v E A K U,
      X.L=B ∧ X.m=m ∧ X.i=s ∧ X.N=X.ceilC ∧ X.pt=a • P c ∧ X.fuel=a*fee ∧
      X.springP X.i=a • P c-Shrine X.Ntop X.tileP ∧
      (∀i:ℕ,i<X.i→Spout X.ax X.tx X.N (X.m+i) h k (X.springP (i+1))=X.springP i) ∧
      (∀(i:ℕ)(_hi:i≤X.i)(φ:Rarity D)(x y:ℝ)(o:CellR)(l:ℕ)(S:Patch)
        (_hx:0<x)(_hx':x≤1)(B₀:ℝ)(_hf:Amplitude φ B₀),
        Income (word (a⁻¹ • X.springP i) φ x y o l) k e u (OrbP S φ x y o)
          (WilsonIndependentMatchedCoverProfile.charge φ u l x y
            (C.buy X.Age*WilsonIndependentMatchedFiledAtHorizon.decay X i*fee) B₀)) ∧
      ∀b:Volume D,∀Q≤e,∀z:ℂ,
        (∑i,belt Q (PowerSeries.C (z*((a⁻¹:ℝ):ℂ))*dose R p X.tileP b i))≤
          ((Q+1:ℕ):ℝ)*V.buy X.Age*(‖z‖*fee)*(∑i:Alma (R.family.labels.level h),|jewelBloom p i b|):=by
  obtain ⟨V,priced⟩:=salary R W target p H v E A K U
  obtain ⟨F,nn,C,book⟩:=WilsonIndependentMatchedFiledAtHorizon.original R W survey hd p capacity H T v E A K U
  refine ⟨F,nn,C,V,?_⟩
  intro B B' same m s live c δ pos
  obtain ⟨X,real,mx,sx,nx,input,actual,stable,consecutive,heard⟩:=book B B' same m s live c δ pos
  refine ⟨X,real,mx,sx,?_,input,actual,stable,consecutive,heard,?_⟩
  · exact nx.trans (by change m+s=X.m+X.i;rw [mx,sx])
  · intro b Q cap z
    exact priced X b Q cap _ _ (pow_pos pos _) actual z

end YM.Integration.WilsonIndependentFittedCommonHorizon
