import YM.Integration.WilsonIndependentFittedExteriorPlate
import YM.Integration.WilsonIndependentFittedExteriorStable
import YM.Integration.WilsonIndependentTwoMomentPlate

/-! One concrete auxiliary programme, with the true original side and every incident dated kernel. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentFittedExteriorPlateBudget
open Filter Function Finset Lattice RG RG.Supply Wilson PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open XSpace XSpace.Rose XSpace.Cirrus Source Source.Drops Labels Precision Next.Foundations
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Bank.PathCost
open WilsonCoeffUV.Embroider WilsonCoeffUV.Shard WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.AuxPlates
open WilsonIndependentExactPlate (Requests)
open WilsonIndependentEvenPassport (old)
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonIndependentFittedExteriorRung (Seated mesh)
open scoped Classical Topology
variable {G:Gauge}(R:Run G)(W:Initialize G)(chart:ChartRatio G)(kernel:KernelChoices)(V:XSpace.Run)
    {j e height seats extra h D k u reserve:ℕ}{I:Type}(d:I→ℕ)(kind:I→Bool)
    (cap:∀i,d i ≤ h)(capacity:∀i,d i ≤ k)(p:h<D)(v:Rails h k u e)
local notation "F₀" => primes G
local notation "C" => Credit.leanC
local notation "T" => sectionAt R W false h
local notation "modes" i:arg => Alma (R.family.labels.level (d i))
local notation "Tally" i:arg => Verse (R.family.labels.level (d i))

include capacity in
theorem original (B:WilsonIndependentEvenPassport.Menu F₀ chart kernel V e height seats j extra)
    (earned:WilsonIndependentTwoMomentPlate.Approved F₀ chart kernel V e height seats j extra B)
    (phase:4 ≤ j)(high:h ≤ height)(dim:D ≤ seats)(ranks:k+reserve ≤ seats)(test:u ≤ seats):
    ∃F:(i:I)→modes i→ℝ,(∀i b,0 ≤ F i b) ∧ ∃C₁ C₂:I→Credit,∀i:Requests B.a,
      let cir:=WilsonIndependentExactPlate.S V B.a B.positive j phase
      let count:=WilsonIndependentExactPlate.M V B.a i
      let ε:=(V.step i.val).spacing
      ∃(L:Levels G)(s:ℕ),L.clock.kernel=kernel ∧
        (∀f:RegulatorIR.Ledger.Flap (WilsonIndependentExactPlate.M V B.a),f.volW=i →
          ∀ per:ℕ,(L.clock.op (s+(count-(f.offset+1))) per).patch=cir.pactP f) ∧
        ∃(torch:Torch (hol G) T p v C C C)(book:ChorusLine (hol G) T p e C C C),
          torch.L=book.arch ∧ torch.L.V.draws=L ∧ torch.L.V.paid=chart ∧ torch.L.V.anchor=s ∧
          (∀ moment ≤ u,∀ rank ≤ k,∀ z ≤ reserve,
            Dormitory torch.L.V rank moment C ∧ SpringD torch.L.V rank moment (rank+z) C) ∧
          (∀t,s ≤ t → t ≤ s+count → torch.L.V.y t ≤ B.cap) ∧
          let N:=s+count
          let m:=s+old V B.a i.val
          L.S.a N/L.S.a m=ε ∧
          ∀(t:I→ℕ)(_live:∀b,s ≤ t b)(_top:∀b,t b ≤ N)(c:(i:I)→Tally i)
            (reach:I→ℝ)(_pos:∀i,0<reach i),∀b,
              let ratio:=L.S.a (t b)/L.S.a m
              Seated R W (kind b) false (cap b) p (hol G) v C C C C (F b) (C₁ b) (C₂ b)
                torch (t b) N (c b) (ε/ratio) ((reach b/ratio)^h):=by
  choose F nn C₁ C₂ filed using fun i=>WilsonIndependentFittedExteriorRung.original R W (kind i) false
    (cap i) p (capacity i) (hol G) v C C C C
  refine ⟨F,nn,C₁,C₂,?_⟩
  intro i cir count ε
  obtain ⟨L,s,real,_,ops,geom,age,hall⟩:=WilsonIndependentTwoMomentPlate.optics
    F₀ chart kernel V e height seats j extra B earned phase i
  obtain ⟨book,torch,draw,clock,owned,start,_,_,same,pay⟩:=hall h D k u reserve p v high dim ranks test
  refine ⟨L,s,real,ops,torch,book,same,same ▸ draw,same ▸ clock,same ▸ start,same ▸ pay,?_,?_⟩
  · intro t late before
    have equal:s+(t-s)=t:=by omega
    rw [same,owned,←equal,age (t-s) (by omega)]
    exact (B.limits _).2
  intro N m
  have ruler:L.S.a N/L.S.a m=ε:=WilsonIndependentFittedExteriorPlate.spacing L.S N m (V.step i.val).positive geom
  refine ⟨ruler,?_⟩
  intro t live top c reach pos b ratio
  have seat:=filed b torch book same.symm (t b) N m (top b) (by rw [same,start];exact live b)
    (c b) (reach b) (pos b)
  rw [show torch.L.V.draws=L from same ▸ draw] at seat
  simpa only [←ruler,mesh,ratio] using seat

end YM.Integration.WilsonIndependentFittedExteriorPlateBudget
