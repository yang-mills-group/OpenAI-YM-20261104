import YM.Integration.WilsonIndependentMovingRosterMarginCourse
import YM.Integration.WilsonIndependentMovingRosterNormalizedWallet
import YM.Integration.WilsonIndependentMovingRosterNormalizedEarlier

/-! A stable correction with its prescribed reporter coordinate on genuinely
moved slots. The prior, receiver, day and all source fees are co-funded on
the single selected optical schedule. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMovingRosterNormalizedCourse
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

open WilsonIndependentMatchedCoverDate (age)
open WilsonIndependentMatchedRosterSlots (wallet)
open WilsonIndependentMovingRosterNormalizedWallet (amount rent)
open WilsonSeparatedPrefixMovingCalendar (epoch)
open scoped BigOperators

include capacity in
theorem original (B:WilsonIndependentEvenPassport.Menu F₀ chart kernel V e height seats j extra)
    (earned:WilsonIndependentCutJoinPlate.Approved F₀ chart kernel V e height seats j extra B)
    (phase:4 ≤ j)(high:h ≤ height)(dim:D ≤ seats)(ranks:k ≤ seats)(test:u ≤ seats)
    (taps moment:ℕ):
    ∃F:(i:I)→modes i→ℝ,(∀i b,0 ≤ F i b) ∧ ∃C₁ C₂ price:I→Credit,
    ∀(prior receiver scale:J→Credit)(power:J→ℕ)(η:ℝ),0 < η →
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
          ∀(t:I→ℕ)(_live:∀b,s ≤ t b)(_top:∀b,t b ≤ N)(c:(b:I)→Tally b)(reach:I→ℝ)(_pos:∀b,0 < reach b),
            let r:=fun b:I=>L.S.a (t b)/L.S.a m
            ∃seat:∀b:I,Seated R W (kind b) false (cap b) p (hol G) v C C C C (F b) (C₁ b) (C₂ b)
                torch (t b) N (c b) (ε/r b) ((reach b/r b)^h),
              (∀b:I,WilsonIndependentMovingRosterLaneSeated.Certified R W (kind b) false (cap b) p (hol G) v
                C C C C (seat b) (price b)) ∧
              ∀(reported:I→Verse (R.family.labels.level h))(flag:I→Bool)(q:J)(older m' day:ℕ),
                s ≤ older → older ≤ m' → m' ≤ day → day ≤ N →
                let X:=fun b:I=>(seat b).choose
                let fee:=fun b:I=>(reach b/r b)^h*WilsonIndependentMatchedFiledIncome.charge e (c b) (F b)
                let net:=(receiver q).buy (age torch.L.V m' day)*torch.L.V.cash (scale q) day*
                  ((ll L day).L.val:ℝ)^(power q)
                ((prior q).buy (age torch.L.V older m')*net)*
                  (∏b,wallet (flag b) (X b) (reported b) ((price b).buy (X b).Age*fee b) taps moment) ≤
                  ε^(-η)*(∏b,amount (flag b) e (reported b) (fee b)):=by
  obtain ⟨F,fnn,C₁,C₂,price,court⟩:=WilsonIndependentMovingRosterMarginCourse.original (I:=I) (J:=J) R W
    chart kernel V d kind cap capacity p v B earned phase high dim ranks test
  let rates:=fun b:I=>rent (hol G) T p e taps moment C C C (price b)
  refine ⟨F,fnn,C₁,C₂,price,?_⟩
  intro prior receiver scale power η small
  filter_upwards [court receiver scale power rates η small,
    WilsonIndependentMovingRosterNormalizedEarlier.original (G:=G) (e:=e) (E:=C)
      V B.a j B.positive phase prior receiver scale power rates B.cap η small]
      with idx draw olderBill i same cir count ε
  obtain ⟨L,s,real,patch,torch,book,stamp,school,clock,base,sold,frames,charges,ruler,_,source⟩:=draw i same
  have first:torch.L.V.y s=B.price ⟨i.val%B.a,Nat.mod_lt _ B.positive⟩:=by
    have head:=charges 0 (Nat.zero_le _)
    change torch.L.V.y s=_ at head
    exact head
  have maxBill:torch.L.V.y s ≤ B.cap:=first ▸ (B.limits _).2
  have ticket:=olderBill i same L s (fun f h=>patch f h 0) torch.L.V school base maxBill
  refine ⟨L,s,real,patch,torch,book,stamp,school,clock,base,sold,frames,charges,?_⟩
  intro N m
  refine ⟨ruler,?_⟩
  intro t live top c reach pos r
  obtain ⟨seat,cert,_⟩:=source t live top c reach pos
  refine ⟨seat,cert,?_⟩
  intro reported flags q older m' day start home ordered limit X fee net
  have ages (b:I):1 ≤ (X b).Age ∧ (X b).Age ≤ epoch torch.L.V s N:=by
    obtain ⟨_,atHome,_,last,ceil,_⟩:=(seat b).choose_spec
    exact WilsonIndependentMovingRosterMarginLedger.source_age torch.L.V s N base.le
      _ (cert b).1 (atHome.symm ▸ live b) last ceil
  have debit:=ticket q older m' day start home ordered limit (fun b=>(X b).Age) ages
  rw [school] at debit
  have dayLive:=base.le.trans (start.trans (home.trans ordered))
  have av:=WilsonIndependentMovingRosterNormalizedEarlier.ranked torch.L.V s older m' N base.le start home
    (ordered.trans limit)
  have dv:=WilsonIndependentMovingRosterNormalizedEarlier.ranked torch.L.V s m' day N base.le
    (start.trans home) ordered limit
  have green:0 ≤ net:=mul_nonneg (mul_nonneg (zero_le_one.trans ((receiver q).purchase dv.1))
    (zero_le_one.trans ((scale q).purchase (torch.L.V.depth day dayLive)))) (pow_nonneg (Nat.cast_nonneg _) _)
  have funded (b:I):0 ≤ fee b:=by
    have rp:0 < r b:=div_pos (L.S.a_pos _) (L.S.a_pos _)
    exact mul_nonneg (pow_nonneg (div_pos (pos b) rp).le _)
      (Finset.sum_nonneg fun j _=>WilsonIndependentMatchedFiledIncome.nonneg (fnn b j) (c b j) e)
  exact WilsonIndependentMovingRosterNormalizedWallet.roster X reported price fee funded flags taps moment
    _ (ε^(-η)) (mul_nonneg (zero_le_one.trans ((prior q).purchase av.1)) green) debit

end YM.Integration.WilsonIndependentMovingRosterNormalizedCourse

