import YM.Integration.WilsonIndependentFittedHomeExterior

/-! An exterior filing on the actual scales of the same chosen torch. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentFittedExteriorRung
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

/-- The complete stable and fitted incomes are on this one selected cut. -/
def Seated (F:Alma (R.family.labels.level d)→ℝ)(C V:Credit)(B:Torch H T p v E A K)
    (t N:ℕ)(c:Verse (R.family.labels.level d))(δ boost:ℝ):Prop:=
    let P:=Shrine (WilsonIndependentMatchedFiledIncome.plate (sectionAt R W survey d) (hd.trans_lt p))
    let a:=δ^(h-d)
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
          ((Q+1:ℕ):ℝ)*V.buy X.Age*(‖z‖*fee)*(∑i:Alma (R.family.labels.level h),|jewelBloom p i b|)

theorem mesh (S:Schedule)(t N m:ℕ):
    (S.a N/S.a m)/(S.a t/S.a m)=S.a N/S.a t:=by
  field_simp [(S.a_pos m).ne',(S.a_pos t).ne']

theorem gain (S:Schedule)(t N:ℕ):
    Real.exp (-(S.scale N-S.scale t)/4)=(S.a N/S.a t)^(1/4:ℝ):=by
  unfold Schedule.scale
  rw [Real.rpow_def_of_pos (div_pos (S.a_pos _) (S.a_pos _)),
    Real.log_div (S.a_pos _).ne' (S.a_pos _).ne',Real.log_inv,Real.log_inv]
  congr 1
  ring

include capacity in
/-- N and every displaced input verse may already be selected. The normalized
mesh and the external scale are taken on B itself. -/
theorem original:
    ∃F:Alma (R.family.labels.level d)→ℝ,(∀i,0≤F i) ∧ ∃C V:Credit,
    ∀(B:Torch H T p v E A K)(B':ChorusLine H T p e E A U)(_same:B'.arch=B.L)
      (t N m:ℕ)(_tN:t ≤ N)(_live:B.L.V.anchor ≤ t)(c:Verse (R.family.labels.level d))
      (reach:ℝ)(_reach:0<reach),
      let S:=B.L.V.draws.S
      Seated R W survey target hd p H v E A K U F C V B t N c (S.a N/S.a t)
        ((reach/(S.a t/S.a m))^h):=by
  obtain ⟨F,nn,C,V,book⟩:=WilsonIndependentFittedHomeExterior.original R W survey target hd p capacity H v E A K U
  refine ⟨F,nn,C,V,?_⟩
  intro B B' same t N m tN live c reach positive S
  let z:=S.a t/S.a m
  have hz:0<z:=div_pos (S.a_pos _) (S.a_pos _)
  have paid:=book B B' same t N tN live c (S.a N/S.a m) z (reach/z)
    (div_pos (S.a_pos _) (S.a_pos _)) hz (div_pos positive hz)
  unfold Seated
  simpa only [z,mesh] using paid

end YM.Integration.WilsonIndependentFittedExteriorRung
