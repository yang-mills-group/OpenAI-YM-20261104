import YM.Integration.WilsonIndependentMovingRosterUnitEscrow
import YM.Integration.WilsonIndependentMovingRosterNormalizedSchool

/-! A basis-direction hearing is paid on every previously seated school
with this original period, course and reference charge. The same result covers
the all-fitted choice and the choice with every residual present. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMovingRosterUnitCourse
open Filter Function Finset Matrix Lattice RG RG.Supply Wilson PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open XSpace XSpace.Rose XSpace.Cirrus Source Source.Drops Labels Precision Next.Foundations
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Bank.PathCost
open WilsonCoeffUV.Embroider WilsonCoeffUV.Shard WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.AuxPlates
open WilsonIndependentExactPlate (Requests)
open WilsonIndependentEvenPassport (old)
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonIndependentFittedExteriorRung (Seated)
open WilsonIndependentMovingRosterStableSale (homes centers)
open WilsonIndependentMatchedRosterMasks (Bits choose)
open WilsonIndependentMatchedRosterCuts (counts ranks)
open WilsonIndependentMatchedCoverDate (age)
open WilsonIndependentMovingRosterNormalizedWallet (amount rent)
open WilsonIndependentMovingRosterNormalizedPortfolio (returned)
open WilsonIndependentMovingRosterNormalizedEarnings (contract edge)
open WilsonSeparatedPrefixMovingCalendar (epoch)
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G)(W:Initialize G)(chart:ChartRatio G)(kernel:KernelChoices)(V:XSpace.Run)
    {j e height seats extra h D k u₀ n:ℕ}
local notation "F₀" => primes G
local notation "C" => Credit.leanC
local notation "T₀" => sectionAt R W false h
variable (d:Fin ((n+1)+1)→ℕ)(kind:Fin ((n+1)+1)→Bool)(cap:∀i,d i ≤ h)(p:h<D)(v:Rails h k u₀ e)

def Heard (out u b:ℕ)(court:Realm G (e+1) C)(X:Fin ((n+1)+1)→CutsP (hol G) T₀ p v C C C C)
    (a fee:Fin ((n+1)+1)→ℝ)(t m older N:ℕ)(col:Fin ((n+1)+1)→Verse (R.family.labels.level h))
    (φ:Fin ((n+1)+1)→Rarity D)(amp:Fin ((n+1)+1)→ℝ)(y z gap:ℝ)(o:CellR)(ε η:ℝ):Prop:=
  let zoom:=paceT court.draws.S m t
  ∀mask:Bits (n+1),
    let flag:=choose (n+1) mask
    let bill:=contract n k out e u b h mask gap z zoom amp*
      (∏s,if flag s then fee s else WilsonIndependentMatchedProxyIncome.cost e (col s))*ε^((counts flag:ℝ)/4-η)
    let row:=returned mask court X col a φ y o t m older N
    Auth (ranks flag k h) row ∧ ∀q ≤ e,∀ω:Fin 0→YForest G,‖row.2 q 0 ω‖ ≤ bill

theorem original (B:WilsonIndependentEvenPassport.Menu F₀ chart kernel V e height seats j extra)
    (phase:4 ≤ j)(test:u₀ ≤ seats)(hk:h ≤ k)(out u b:ℕ)(roster:(n+2)*k ≤ out)(depth:out ≤ b)
    (bond:b ≤ seats)(look:u+b ≤ u₀)(slack:1 ≤ (b:ℝ)-(((n+2)*h:ℕ):ℝ)-((n+2:ℕ):ℝ)/4)
    (price:Fin ((n+1)+1)→Credit)(η:ℝ)(gain:0 < η):
    ∀ᶠ idx:ℕ in atTop,∀i:Requests B.a,i.val=idx →
      let cir:=WilsonIndependentExactPlate.S V B.a B.positive j phase
      let levels:=WilsonIndependentExactPlate.M V B.a i
      let ε:=(V.step idx).spacing
      ∀(L:Levels G)(s:ℕ),
        (∀f:RegulatorIR.Ledger.Flap (WilsonIndependentExactPlate.M V B.a),f.volW=i →
          (L.clock.op (s+(levels-(f.offset+1))) 0).patch=cir.pactP f) →
        ∀(torch:Torch (hol G) T₀ p v C C C),torch.L.V.draws=L → torch.L.V.anchor=s →
          WilsonIndependentMovingRosterAllFineSeats.Elected F₀ torch.L.V height seats → torch.L.V.y s ≤ B.cap →
          let N:=s+levels
          let m:=s+old V B.a idx
          L.S.a N/L.S.a m=ε →
          ∀(t:ℕ),s ≤ t → t ≤ m → ∀(c:(i:Fin ((n+1)+1))→Verse (R.family.labels.level (d i)))
            (reach:Fin ((n+1)+1)→ℝ), (∀i,0 < reach i) →
            let r:=fun i:Fin ((n+1)+1)=>L.S.a (homes t m i)/L.S.a m
            ∀(F:(i:Fin ((n+1)+1))→Alma (R.family.labels.level (d i))→ℝ), (∀i l,0 ≤ F i l) →
            ∀(C₁ C₂:Fin ((n+1)+1)→Credit)
            (seat:∀i:Fin ((n+1)+1),Seated R W (kind i) false (cap i) p (hol G) v C C C C (F i) (C₁ i) (C₂ i)
                torch (homes t m i) N (c i) (ε/r i) ((reach i/r i)^h)),
              (∀i,WilsonIndependentMovingRosterLaneSeated.Certified R W (kind i) false (cap i) p (hol G) v
                C C C C (seat i) (price i)) →
              let X:=fun i:Fin ((n+1)+1)=>(seat i).choose
              let a:=fun i:Fin ((n+1)+1)=>((paceT torch.L.V.draws.S (homes t m i) N)^(h-d i))⁻¹
              let fee:=fun i:Fin ((n+1)+1)=>(reach i/r i)^h*WilsonIndependentMatchedFiledIncome.charge e (c i) (F i)
              ∀(older:ℕ),s ≤ older → older ≤ m →
                ∀(col:Fin ((n+1)+1)→Verse (R.family.labels.level h))(φ:Fin ((n+1)+1)→Rarity D)
                   (amp:Fin ((n+1)+1)→ℝ)(y z gap:ℝ)(o:CellR),
                let zoom:=paceT torch.L.V.draws.S m t
                0 < gap → (∀i,Amplitude (φ i) (amp i)) → (∀i,radiusH (φ i) 1 (centers y zoom i) ≤ z) →
                (∀i l:Fin (n+1),i≠l → ClearDay (φ i.succ) (φ l.succ) gap) →
                (∀i:Fin (n+1),∀x∈tsupport (φ i.succ).ψ.val,∀w∈tsupport (φ 0).ψ.val,gap ≤ dist x (zoom • w)) →
                Heard R W p v out u b torch.L.V X a fee t m older N col φ amp y z gap o ε η:=by
  classical
  obtain ⟨C₀,C',earns⟩:=WilsonIndependentMovingRosterUnitEscrow.original
    (H:=hol G) (T:=T₀) (p:=p) (v:=v) (n:=n) (E:=C) (W:=C) (K:=C) (U:=C) out u b C C
  let rank:=fun mask:Bits (n+1)=>(n+2)*h+counts (choose (n+1) mask)
  let rents:=fun i:Fin ((n+1)+1)=>rent (hol G) T₀ p e u b C C C (price i)
  let scale:=fun _:Bits (n+1)=>priceWG G e out u b C C
  filter_upwards [WilsonIndependentMovingRosterNormalizedEarlier.original (G:=G) (e:=e) (E:=C)
    V B.a j B.positive phase C' C₀ scale rank rents B.cap η gain] with idx board i hi cir levels ε L s patches
    torch draw base paid quote N m ruler t st tm c reach pos r F fnn C₁ C₂ seat cert X a fee older start prev
    col φ amp y z gap o zoom gpos costs radius separated far
  have till:m ≤ N:=by
    change s+old V B.a idx ≤ s+WilsonIndependentEvenPassport.count V B.a i.val
    rw [hi]
    unfold WilsonIndependentEvenPassport.count
    omega
  have live (i:Fin ((n+1)+1)):s ≤ homes t m i:= Fin.cases st (fun _=>st.trans tm) i
  have top (i:Fin ((n+1)+1)):homes t m i ≤ N:= Fin.cases (tm.trans till) (fun _=>till) i
  have authority (i:Fin ((n+1)+1)):=WilsonIndependentMovingRosterNormalizedSeats.original R W (kind i) false
    (cap i) p (hol G) v C C C C draw ruler (top i) (seat i) (price i) (cert i)
  obtain ⟨spring,dorm,limit,bound⟩:=WilsonIndependentMovingRosterNormalizedAdmissions.original F₀ torch.L.V
    paid hk roster depth bond (Nat.le_trans (Nat.le_add_right u b) (look.trans test)) slack
  have sep:1 ≤ zoom:=(one_le_div (torch.L.V.draws.S.a_pos m)).2 (torch.L.V.draws.S.strictAnti.antitone tm)
  have mesh:paceT torch.L.V.draws.S m N=ε:=by change torch.L.V.draws.S.a N/torch.L.V.draws.S.a m=ε;rw [draw,ruler]
  have ages (i:Fin ((n+1)+1)):1 ≤ (X i).Age ∧ (X i).Age ≤ epoch torch.L.V s N:=
    WilsonIndependentMovingRosterMarginLedger.source_age torch.L.V s N base.le _ (authority i).1
      ((authority i).2.1.symm ▸ live i) (authority i).2.2.1 (seat i).choose_spec.2.2.2.2.1
  have price0 (i:Fin ((n+1)+1)):0 ≤ fee i:=by
    have localScale:0 < r i:=div_pos (L.S.a_pos _) (L.S.a_pos _)
    exact mul_nonneg (pow_nonneg (div_pos (pos i) localScale).le _)
      (Finset.sum_nonneg fun l _=>WilsonIndependentMatchedFiledIncome.nonneg (fnn i l) (c i l) e)
  let A:=fun i:Fin ((n+1)+1)=>(price i).buy (X i).Age*fee i
  have schedule:=board i hi L s patches torch.L.V draw base quote
  have seen:=earns torch.L.V X spring dorm older t m N tm prev till (base.le.trans start) col a A amp φ y z gap
    o η fee sep gpos limit look bound (fun i=>(authority i).1) (fun i=>(authority i).2.1)
    (fun i=>(authority i).2.2.1) (fun i=>(authority i).2.2.2.1) (fun i=>(authority i).2.2.2.2) costs radius
    separated far (fun mask day mj jN=>by
      have debit:=schedule mask older m day start prev mj jN (fun i=>(X i).Age) ages
      have lv:=base.le.trans (start.trans (prev.trans mj))
      have av:=WilsonIndependentMovingRosterNormalizedEarlier.ranked torch.L.V s older m N base.le start prev till
      have green:0 ≤ (C' mask).buy (WilsonIndependentMatchedCoverDate.age torch.L.V older m)*edge torch.L.V (C₀ mask) (scale mask) (rank mask) m day:=
        mul_nonneg (zero_le_one.trans ((C' mask).purchase av.1))
          (zero_le_one.trans (WilsonIndependentMovingRosterNormalizedEarnings.wealth torch.L.V _ _ _
            (base.le.trans (start.trans prev)) mj))
      have purchased:=WilsonIndependentMovingRosterNormalizedWallet.roster X col price fee price0 (choose (n+1) mask)
        u b _ (ε^(-η)) green debit
      simpa only [mesh,amount] using purchased)
  intro mask
  simpa only [mesh] using seen mask

end YM.Integration.WilsonIndependentMovingRosterUnitCourse

