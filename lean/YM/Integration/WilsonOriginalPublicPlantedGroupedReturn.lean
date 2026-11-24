import YM.Integration.WilsonOriginalPublicPlantedStableCredit
import YM.Integration.WilsonIndependentPublicPlateOptics
import YM.Integration.WilsonIndependentMatchedFiledIncome

/-! The actual fitted top stencil and its loss of a small power on the original
two-length auxiliary Wilson schedule. The reporting chart, kernel and
unmarked account are issued before any fitted source coefficients. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalPublicPlantedGroupedReturn
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open PhysicalNext.Repeat.Legato XSpace.Rose XSpace.Cirrus XSpace
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.AuxPlates
open WilsonIndependentEvenPassport (old young)
open WilsonIndependentExactPlate (Requests)
open WilsonOriginalPublicPlantedStableCredit (span)
open scoped BigOperators Topology Classical

variable {G:Gauge}{H:Hol G}(R:Master H)(chart:ChartRatio G)(kernel:KernelChoices)
    (V:XSpace.Run){j e height seats extra:ℕ}
    (B:WilsonIndependentEvenPassport.Menu R chart kernel V e height seats j extra)
    (phase:4 ≤ j)
variable (originalRun:Run G)(W₀:Initialize G)(survey:Bool){d h D k u:ℕ}
    (hd:d ≤ h)(p:h<D)(capacity:d ≤ k)(v:Rails h k u e)
local notation "credit" => Credit.leanC
local notation "trial" => WilsonIndependentMatchedNamedPair.sectionAt originalRun W₀ survey d
local notation "upperBasis" => WilsonIndependentMatchedFiledIncome.plate trial (hd.trans_lt p)

include capacity

/-- One unmarked history and one reporting scale for all fitted vectors in
this grade. At common horizon six the grade-four source is planted with its
two powers of spacing; its entire measured Shrine survives the subtraction. -/
theorem original (covered:h ≤ height)(dim:D ≤ seats)(pegs:k ≤ seats)(test:u ≤ seats)
    (θ:ℝ)(positive:0<θ):
    ∃ α:Alma (originalRun.family.labels.level d)→ℝ,(∀b,0 ≤ α b) ∧ ∀ᶠ j₀:ℕ in atTop,
      ∀i:Requests B.a,i.val=j₀ →
      let δ:=(V.step i.val).spacing
      let amp:=δ^(h-d)
      let cir:=WilsonIndependentExactPlate.S V B.a B.positive j phase
      let N:=WilsonIndependentEvenPassport.count V B.a i.val
      ∃(A:Levels G)(s:ℕ),A.clock.kernel=kernel ∧
        (∀ f:RegulatorIR.Ledger.Flap (WilsonIndependentExactPlate.M V B.a),f.volW=i →
          ∀ per:ℕ,(A.clock.op (s+(N-(f.offset+1))) per).patch=cir.pactP f) ∧
      ∃(L:Torch H (R.T h) p v credit credit credit)
        (L':ChorusLine H (R.T h) p e credit credit credit),
        L.L=L'.arch ∧ L.L.V.draws=A ∧ L.L.V.paid=chart ∧
        ∀c:Verse (originalRun.family.labels.level d),
          let fee:=WilsonIndependentMatchedFiledIncome.charge e c α
          ∃X:CutsP H (R.T h) p v credit credit credit credit,
            X.L=L ∧ X.m=s+old V B.a i.val ∧ X.N=s+N ∧ X.i=young B.a i.val ∧
            X.pt=amp • Shrine upperBasis c ∧ X.fuel=amp*fee ∧
            X.springP X.i=amp • Shrine upperBasis c-Shrine X.Ntop X.tileP ∧
            (∀o<X.i,Spout X.ax X.tx X.N (X.m+o) h k (X.springP (o+1))=X.springP o) ∧
            ∀ lag ≤ e,∀ o ≤ X.i,∀ r:ℕ,∀ moment ≤ u,
              Fruit 0 1 moment ((amp⁻¹ • X.springP o).2 lag r)
                (δ^(-θ)*(δ/Real.exp (-span X o))^(1/4:ℝ)*fee):=by
  obtain ⟨α,nonneg,admitted⟩:=WilsonIndependentMatchedFiledIncome.named originalRun W₀ survey d
    (hd.trans_lt p) capacity e u
  refine ⟨α,nonneg,?_⟩
  filter_upwards [WilsonOriginalPublicPlantedStableCredit.original H (R.T h) p v
    credit credit credit credit V B.cap θ positive] with j₀ spend i same δ amp cir N
  subst j₀
  obtain ⟨A,s,choices,patch,geometry,home,hall⟩:=WilsonIndependentPublicPlateOptics.on_plate
    V j phase R chart kernel B i
  obtain ⟨L',L,draw,clock,price,root,_,_,ident,_⟩:=hall h D k u 0 p v covered dim (by omega) test
  refine ⟨A,s,choices,patch,L,L',ident,ident ▸ draw,ident ▸ clock,?_⟩
  intro c fee
  let m:=s+old V B.a i.val
  let ℓ:=young B.a i.val
  have fixed:m+ℓ=s+N:=by dsimp only [m,ℓ,N,WilsonIndependentEvenPassport.count];omega
  have allowed:L.L.V.anchor ≤ m:=by rw [ident,root];exact Nat.le_add_right .. 
  have incurred:=admitted c
  have ap:0<amp:=pow_pos (V.step i.val).positive _
  let X:=WilsonIndependentMatchedKernelResidual.diagonal L L' ident.symm m ℓ (m+ℓ) allowed le_rfl
    (amp • Shrine upperBasis c) (incurred.1.μ amp) (amp*fee) (mul_nonneg ap.le incurred.2.1)
    (by intro lag r hl
        have word:=(show Fruit 0 1 u ((Shrine upperBasis c).2 lag r) fee from incurred.2.2 lag r hl).μ amp
        rwa [abs_of_pos ap] at word)
  refine ⟨X,rfl,rfl,fixed,rfl,rfl,rfl,X.carve1,fun _ ho=>X.carve2 ho,?_⟩
  have scale:span X X.i= -Real.log δ:=by
    change L.L.V.draws.S.scale (m+ℓ)-L.L.V.draws.S.scale m=_
    rw [ident,draw,fixed]
    exact geometry
  have income:X.vesselsC.y X.m ≤ B.cap:=by
    change L.L.V.y m ≤ _
    rw [ident,price,home _ (by change old V B.a i.val  ≤  N;dsimp [N,WilsonIndependentEvenPassport.count];omega)]
    exact (B.limits _).2
  intro lag hl o ho r moment hm
  have out:=(spend X income scale lag hl o ho r moment hm).μ amp⁻¹
  have wage:abs (amp⁻¹) *(δ^(-θ)*(δ/Real.exp (-span X o))^(1/4:ℝ)*X.fuel)=
      δ^(-θ)*(δ/Real.exp (-span X o))^(1/4:ℝ)*fee:=by
    rw [abs_of_pos (inv_pos.mpr ap),show X.fuel=amp*fee by rfl]
    field_simp [ap.ne']
  rw [wage] at out
  exact out

end YM.Integration.WilsonOriginalPublicPlantedGroupedReturn
