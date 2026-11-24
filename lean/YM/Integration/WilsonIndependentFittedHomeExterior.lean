import YM.Integration.WilsonIndependentFittedCommonHorizon

/-! Filing a homogeneous exterior at its own reporter on an already selected top. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentFittedHomeExterior
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

theorem charge_smul (a:ℝ)(c:Verse (R.family.labels.level d))(F:Alma (R.family.labels.level d)→ℝ):
    WilsonIndependentMatchedFiledIncome.charge e (a • c) F=
      |a| * WilsonIndependentMatchedFiledIncome.charge e c F:=by
  unfold WilsonIndependentMatchedFiledIncome.charge WilsonIndependentMatchedFiledIncome.allot
  simp only [Pi.smul_apply,PowerSeries.coeff_smul,smul_eq_mul,abs_mul,mul_assoc,mul_sum]

include capacity in
/-- The outer column is filed on the original torch at home t and top N.
The scalar ρ^h multiplies the entire submitted verse before its fit. -/
theorem original:
    let Td:=sectionAt R W survey d
    let P:=Shrine (WilsonIndependentMatchedFiledIncome.plate Td (hd.trans_lt p))
    ∃F:Alma (R.family.labels.level d)→ℝ,(∀i,0≤F i) ∧ ∃C V:Credit,
    ∀(B:Torch H T p v E A K)(B':ChorusLine H T p e E A U)(_same:B'.arch=B.L)
      (t N:ℕ)(_tN:t ≤ N)(_live:B.L.V.anchor ≤ t)(c:Verse (R.family.labels.level d))
      (ε T₀ ρ:ℝ)(_ε:0<ε)(_T:0<T₀)(_ρ:0<ρ),
      let a:=(ε/T₀)^(h-d)
      let boost:=ρ^h
      let fee:=boost*WilsonIndependentMatchedFiledIncome.charge e c F
      ∃X:CutsP H T p v E A K U,
      X.L=B ∧ X.m=t ∧ X.i=N-t ∧ X.N=N ∧ X.N=X.ceilC ∧
      X.pt=a • (boost • P c) ∧ X.fuel=a*fee ∧
      X.springP X.i=a • (boost • P c)-Shrine X.Ntop X.tileP ∧
      (∀i:ℕ,i<X.i→Spout X.ax X.tx X.N (X.m+i) h k (X.springP (i+1))=X.springP i) ∧
      (∀(i:ℕ)(_hi:i≤X.i)(φ:Rarity D)(x y:ℝ)(o:CellR)(l:ℕ)(S:Patch)
        (_hx:0<x)(_hx':x≤1)(B₀:ℝ)(_hf:Amplitude φ B₀),
        Income (word (a⁻¹ • X.springP i) φ x y o l) k e u (OrbP S φ x y o)
          (WilsonIndependentMatchedCoverProfile.charge φ u l x y
            (C.buy X.Age*WilsonIndependentMatchedFiledAtHorizon.decay X i*fee) B₀)) ∧
      ∀b:Volume D,∀Q≤e,∀z:ℂ,
        (∑i,belt Q (PowerSeries.C (z*((a⁻¹:ℝ):ℂ))*dose R p X.tileP b i))≤
          ((Q+1:ℕ):ℝ)*V.buy X.Age*(‖z‖*fee)*(∑i:Alma (R.family.labels.level h),|jewelBloom p i b|):=by
  obtain ⟨F,nn,C,V,book⟩:=WilsonIndependentFittedCommonHorizon.original R W survey target hd p capacity H v E A K U
  refine ⟨F,nn,C,V,?_⟩
  intro B B' same t N tN live c ε T₀ ρ hε hT hρ a boost fee
  have liveNorm:0<boost:=pow_pos hρ _
  obtain ⟨X,real,mx,sx,nx,input,actual,stable,consecutive,heard,priced⟩:=
    book B B' same t (N-t) live (boost • c) (ε/T₀) (div_pos hε hT)
  have charge:WilsonIndependentMatchedFiledIncome.charge e (boost • c) F=fee:=by
    rw [charge_smul,abs_of_pos liveNorm]
  rw [StableStrip.shrine_μ] at input stable
  rw [charge] at actual heard priced
  refine ⟨X,real,mx,sx,?_,nx,input,actual,stable,consecutive,heard,priced⟩
  rw [nx]
  change X.m+X.i=N
  omega

end YM.Integration.WilsonIndependentFittedHomeExterior
