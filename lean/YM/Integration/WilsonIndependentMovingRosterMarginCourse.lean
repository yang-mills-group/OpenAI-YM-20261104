import YM.Integration.WilsonIndependentMovingRosterLaneSeated
import YM.Integration.WilsonIndependentMovingRosterMarginBoard
import YM.Integration.WilsonIndependentFittedExteriorPlate

/-! A common election for the actual moved upper inputs and all receiver
and per-input credit factors on the stable mask sum. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMovingRosterMarginCourse
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
    {j e height seats extra h D k u:ℕ}{I J:Type}[Fintype I][Fintype J](d:I→ℕ)(kind:I→Bool)
    (cap:∀i,d i ≤ h)(capacity:∀i,d i ≤ k)(p:h<D)(v:Rails h k u e)
local notation "F₀" => primes G
local notation "C" => Credit.leanC
local notation "T" => sectionAt R W false h
local notation "modes" i:arg => Alma (R.family.labels.level (d i))
local notation "Tally" i:arg => Verse (R.family.labels.level (d i))

open WilsonIndependentMovingRosterMarginOptics (Billed)
open WilsonSeparatedPrefixMovingCalendar (epoch)
open scoped BigOperators

include capacity in
theorem original (B:WilsonIndependentEvenPassport.Menu F₀ chart kernel V e height seats j extra)
    (earned:WilsonIndependentCutJoinPlate.Approved F₀ chart kernel V e height seats j extra B)
    (phase:4 ≤ j)(high:h ≤ height)(dim:D ≤ seats)(ranks:k ≤ seats)(test:u ≤ seats):
    ∃F:(i:I)→modes i→ℝ,(∀i b,0 ≤ F i b) ∧ ∃C₁ C₂ price:I→Credit,
    ∀(receiver scale:J→Credit)(power:J→ℕ)(rates:I→Credit)(η:ℝ),0 < η →
    ∀ᶠ idx:ℕ in atTop,∀i:Requests B.a,i.val=idx →
      let cir:=WilsonIndependentExactPlate.S V B.a B.positive j phase
      let count:=WilsonIndependentExactPlate.M V B.a i
      let ε:=(V.step idx).spacing
      ∃(L:Levels G)(s:ℕ),L.clock.kernel=kernel ∧
        (∀f:RegulatorIR.Ledger.Flap (WilsonIndependentExactPlate.M V B.a),f.volW=i →
          ∀per:ℕ,(L.clock.op (s+(count-(f.offset+1))) per).patch=cir.pactP f) ∧
        ∃(torch:Torch (hol G) T p v C C C)(book:ChorusLine (hol G) T p e C C C),
          torch.L=book.arch ∧ torch.L.V.draws=L ∧ torch.L.V.paid=chart ∧ torch.L.V.anchor=s ∧
          WilsonIndependentMovingRosterAllFineSeats.Elected F₀ torch.L.V height seats ∧
          WilsonIndependentCutJoinNativeFrames.Funded F₀ torch.L.V height seats ∧
          (∀z ≤ count,torch.L.V.y (s+z)=B.price ⟨i.val%B.a,Nat.mod_lt _ B.positive⟩) ∧
          let N:=s+count
          let m:=s+old V B.a idx
          L.S.a N/L.S.a m=ε ∧
          (∀q:J,Billed torch.L.V (receiver q) (scale q) (power q) rates s N (ε^(-η))) ∧
          ∀(t:I→ℕ)(_live:∀b,s ≤ t b)(_top:∀b,t b ≤ N)(c:(b:I)→Tally b)(reach:I→ℝ)(_pos:∀b,0 < reach b),
            let r:=fun b:I=>L.S.a (t b)/L.S.a m
            ∃seat:∀b:I,Seated R W (kind b) false (cap b) p (hol G) v C C C C (F b) (C₁ b) (C₂ b)
                torch (t b) N (c b) (ε/r b) ((reach b/r b)^h),
              (∀b:I,WilsonIndependentMovingRosterLaneSeated.Certified R W (kind b) false (cap b) p (hol G) v
                C C C C (seat b) (price b)) ∧
              ∀(q:J)(m' day:ℕ),s ≤ m' → m' ≤ day → day ≤ N →
                (receiver q).buy (WilsonIndependentMatchedCoverDate.age torch.L.V m' day)*torch.L.V.cash (scale q) day*
                  ((ll L day).L.val:ℝ)^(power q)*(∏b,(rates b).buy ((seat b).choose.Age)) ≤ ε^(-η):=by
  choose F fnn C₁ C₂ file using fun b=>WilsonIndependentFittedExteriorRung.original R W (kind b) false
    (cap b) p (capacity b) (hol G) v C C C C
  choose price lane using fun b=>WilsonIndependentMovingRosterLaneSeated.original R W (kind b) false
    (cap b) p (hol G) v C C C C
  refine ⟨F,fnn,C₁,C₂,price,?_⟩
  intro receiver scale power rates η small
  filter_upwards [WilsonIndependentMovingRosterMarginBoard.original F₀ chart kernel V B earned phase
    receiver scale power rates η small] with idx receipt i eq cir count ε
  obtain ⟨L,s,real,patches,length,all⟩:=receipt i eq
  obtain ⟨book,draw,clock,_,start,quotes,_,faculty,tariff,frames,ledger⟩:=all h D p high dim
  obtain ⟨torch,same⟩:=faculty k u v ranks test
  have original:torch.L.V.draws=L:=same ▸ draw
  have anchor:torch.L.V.anchor=s:=same ▸ start
  refine ⟨L,s,real,patches,torch,book,same,original,same ▸ clock,anchor,same ▸ tariff,same ▸ frames,same ▸ quotes,?_⟩
  intro N m
  have ruler:L.S.a N/L.S.a m=ε:=WilsonIndependentFittedExteriorPlate.spacing L.S N m (V.step idx).positive length
  have bill:∀q:J,Billed torch.L.V (receiver q) (scale q) (power q) rates s N (ε^(-η)):=same ▸ ledger
  refine ⟨ruler,bill,?_⟩
  intro t live top c reach pos r
  have source (b:I):Seated R W (kind b) false (cap b) p (hol G) v C C C C (F b) (C₁ b) (C₂ b)
      torch (t b) N (c b) (ε/r b) ((reach b/r b)^h):=by
    have tube:=file b torch book same.symm (t b) N m (top b) (anchor ▸ live b) (c b) (reach b) (pos b)
    rw [original] at tube
    simpa only [←ruler,r,mesh] using tube
  have mounted (b:I):WilsonIndependentMovingRosterLaneSeated.Certified R W (kind b) false (cap b) p (hol G) v
      C C C C (source b) (price b):=by
    apply lane b
    change torch.L.V.draws.S.a N/torch.L.V.draws.S.a (t b)=ε/r b
    rw [original]
    dsimp only [r]
    rw [←ruler,mesh]
  refine ⟨source,mounted,?_⟩
  intro q m' day good mid fine
  have fitted (b:I):1 ≤ (source b).choose.Age ∧ (source b).choose.Age ≤ epoch torch.L.V s N:=by
    obtain ⟨_,home,_,last,ceil,_⟩:=(source b).choose_spec
    exact WilsonIndependentMovingRosterMarginLedger.source_age torch.L.V s N anchor.le
      _ (mounted b).1 (home.symm ▸ live b) last ceil
  have paid:=(bill q m' day good mid fine).2 (fun b=>(source b).choose.Age) fitted
  rw [original] at paid
  exact paid

end YM.Integration.WilsonIndependentMovingRosterMarginCourse

