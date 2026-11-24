import YM.Integration.WilsonIndependentMovingRosterNormalizedEscrow
import YM.Integration.WilsonIndependentMovingRosterNormalizedSeats
import YM.Integration.WilsonIndependentMovingRosterNormalizedAdmissions

/-! The selected public inversion board, its complete cuts at the two reports,
and their older normalized scalar with all source and receiver charges paid. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMovingRosterNormalizedSchool
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
open WilsonIndependentMatchedRosterMasks (Bits choose quiet)
open WilsonIndependentMatchedRosterCuts (counts ranks)
open WilsonIndependentMovingRosterNormalizedEarnings (contract)
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G)(W:Initialize G)(chart:ChartRatio G)(kernel:KernelChoices)(V:XSpace.Run)
    {j e height seats extra h D k u₀ n:ℕ}
local notation "F₀" => primes G
local notation "C" => Credit.leanC
local notation "T₀" => sectionAt R W false h
variable (d:(Fin ((n+1)+1))→ℕ)(kind:(Fin ((n+1)+1))→Bool)(cap:∀i,d i ≤ h)(p:h<D)(v:Rails h k u₀ e)

def Hearing (out u b:ℕ)(court:Realm G (e+1) C)(X:(Fin ((n+1)+1))→CutsP (hol G) T₀ p v C C C C)
    (a fee:(Fin ((n+1)+1))→ℝ)(t m older N:ℕ)(col:(Fin ((n+1)+1))→Verse (R.family.labels.level h))(φ:(Fin ((n+1)+1))→Rarity D)(amp:(Fin ((n+1)+1))→ℝ)
    (y z gap:ℝ)(o:CellR)(ε η:ℝ):Prop:=
  let zoom:=paceT court.draws.S m t
  let bill:=((Finset.univ.erase (quiet (n+1))).sum fun mask=>
    contract n k out e u b h mask gap z zoom amp*
      ∏s,if choose (n+1) mask s then fee s else WilsonIndependentMatchedProxyIncome.cost e (col s))*
    ε^(1/4-η:ℝ)
  ∀q ≤ e,∀ω:Fin 0→YForest G,
    let raw:=(WilsonIndependentMovingRosterNormalizedBook.raw court X a col φ y o t m older N).2 q 0 ω
    let prescribed:=(WilsonIndependentMovingRosterNormalizedBook.prescribed court X col φ y o t m older N).2 q 0 ω
    ‖raw-prescribed‖ ≤ bill ∧ ‖raw‖ ≤ ‖prescribed‖+bill

theorem original (B:WilsonIndependentEvenPassport.Menu F₀ chart kernel V e height seats j extra)
    (earned:WilsonIndependentCutJoinPlate.Approved F₀ chart kernel V e height seats j extra B)
    (phase:4 ≤ j)(high:h ≤ height)(dim:D ≤ seats)(ranks₀:k ≤ seats)(test:u₀ ≤ seats)(hk:h ≤ k)
    (out u b:ℕ)(roster:(n+2)*k ≤ out)(depth:out ≤ b)(bond:b ≤ seats)(look:u+b ≤ u₀)
    (slack:1 ≤ (b:ℝ)-(((n+2)*h:ℕ):ℝ)-((n+2:ℕ):ℝ)/4):
    ∃F:(i:(Fin ((n+1)+1)))→Alma (R.family.labels.level (d i))→ℝ,(∀i l,0 ≤ F i l) ∧ ∃C₁ C₂ price:(Fin ((n+1)+1))→Credit,∀η:ℝ,0 < η →
    ∀ᶠ idx:ℕ in atTop,∀i:Requests B.a,i.val=idx →
      let cir:=WilsonIndependentExactPlate.S V B.a B.positive j phase
      let levels:=WilsonIndependentExactPlate.M V B.a i
      let ε:=(V.step idx).spacing
      ∃(L:Levels G)(s:ℕ),L.clock.kernel=kernel ∧
        (∀f:RegulatorIR.Ledger.Flap (WilsonIndependentExactPlate.M V B.a),f.volW=i →
          ∀per:ℕ,(L.clock.op (s+(levels-(f.offset+1))) per).patch=cir.pactP f) ∧
        ∃(torch:Torch (hol G) T₀ p v C C C)(book:ChorusLine (hol G) T₀ p e C C C),
          torch.L=book.arch ∧ torch.L.V.draws=L ∧ torch.L.V.paid=chart ∧ torch.L.V.anchor=s ∧
          WilsonIndependentMovingRosterAllFineSeats.Elected F₀ torch.L.V height seats ∧
          WilsonIndependentCutJoinNativeFrames.Funded F₀ torch.L.V height seats ∧
          (∀z ≤ levels,torch.L.V.y (s+z)=B.price ⟨i.val%B.a,Nat.mod_lt _ B.positive⟩) ∧
          let N:=s+levels
          let m:=s+old V B.a idx
          L.S.a N/L.S.a m=ε ∧
          ∀(t:ℕ),s ≤ t → t ≤ m → ∀(c:(s:(Fin ((n+1)+1)))→Verse (R.family.labels.level (d s)))(reach:(Fin ((n+1)+1))→ℝ), (∀i,0 < reach i) →
            let r:=fun i:(Fin ((n+1)+1))=>L.S.a (homes t m i)/L.S.a m
            ∃seat:∀i:(Fin ((n+1)+1)),Seated R W (kind i) false (cap i) p (hol G) v C C C C (F i) (C₁ i) (C₂ i)
                torch (homes t m i) N (c i) (ε/r i) ((reach i/r i)^h),
              (∀i:(Fin ((n+1)+1)),WilsonIndependentMovingRosterLaneSeated.Certified R W (kind i) false (cap i) p (hol G) v
                C C C C (seat i) (price i)) ∧
              let X:=fun i:(Fin ((n+1)+1))=>(seat i).choose
              let a:=fun i:(Fin ((n+1)+1))=>((paceT torch.L.V.draws.S (homes t m i) N)^(h-d i))⁻¹
              let fee:=fun i:(Fin ((n+1)+1))=>(reach i/r i)^h*WilsonIndependentMatchedFiledIncome.charge e (c i) (F i)
              ∀(older:ℕ),s ≤ older → older ≤ m →
                ∀(col:(Fin ((n+1)+1))→Verse (R.family.labels.level h))(φ:(Fin ((n+1)+1))→Rarity D)(amp:(Fin ((n+1)+1))→ℝ)(y z gap:ℝ)(o:CellR),
                let zoom:=paceT torch.L.V.draws.S m t
                0 < gap → (∀i,Amplitude (φ i) (amp i)) → (∀i,radiusH (φ i) 1 (centers y zoom i) ≤ z) →
                (∀i l:Fin (n+1),i≠l → ClearDay (φ i.succ) (φ l.succ) gap) →
                (∀i:Fin (n+1),∀x∈tsupport (φ i.succ).ψ.val,∀w∈tsupport (φ 0).ψ.val,gap ≤ dist x (zoom • w)) →
                Hearing R W p v out u b torch.L.V X a fee t m older N col φ amp y z gap o ε η:=by
  classical
  obtain ⟨C₀,C',earns⟩:=WilsonIndependentMovingRosterNormalizedEscrow.original
    (H:=hol G) (T:=T₀) (p:=p) (v:=v) (n:=n) (E:=C) (W:=C) (K:=C) (U:=C) hk out u b C C
  obtain ⟨F,fnn,C₁,C₂,price,boards⟩:=WilsonIndependentMovingRosterNormalizedCourse.original
    (J:=Bits (n+1)) R W chart kernel V d kind cap (fun i=>(cap i).trans hk) p v B earned
    phase high dim ranks₀ test u b
  let order:=fun mask:Bits (n+1)=>(n+2)*h+counts (choose (n+1) mask)
  refine ⟨F,fnn,C₁,C₂,price,?_⟩
  intro η pos
  filter_upwards [boards C' C₀ (fun _=>priceWG G e out u b C C) order η pos] with idx appointed i hi cir levels ε
  obtain ⟨L,s,real,patch,torch,book,stamp,draw,clock,base,paid,frames,dates,ruler,seated⟩:=appointed i hi
  refine ⟨L,s,real,patch,torch,book,stamp,draw,clock,base,paid,frames,dates,?_⟩
  intro N m
  have till:m ≤ N:=by
    change s+old V B.a idx ≤ s+WilsonIndependentEvenPassport.count V B.a i.val
    rw [hi]
    unfold WilsonIndependentEvenPassport.count
    omega
  refine ⟨ruler,?_⟩
  intro t st tm c reach funds r
  have live (i:(Fin ((n+1)+1))):s ≤ homes t m i:= Fin.cases st (fun _=>st.trans tm) i
  have top (i:(Fin ((n+1)+1))):homes t m i ≤ N:= Fin.cases (tm.trans till) (fun _=>till) i
  obtain ⟨seat,cert,wage⟩:=seated (homes t m) live top c reach funds
  refine ⟨seat,cert,?_⟩
  intro X a fee older start prev col φ amp y z gap o zoom gpos costs radius separate far
  have authority (i:(Fin ((n+1)+1))):=WilsonIndependentMovingRosterNormalizedSeats.original R W (kind i) false (cap i) p
    (hol G) v C C C C draw ruler (top i) (seat i) (price i) (cert i)
  obtain ⟨spring,dorm,limit,bound⟩:=WilsonIndependentMovingRosterNormalizedAdmissions.original F₀ torch.L.V
    paid hk roster depth bond (Nat.le_trans (Nat.le_add_right u b) (look.trans test)) slack
  have sep:1 ≤ zoom:= (one_le_div (torch.L.V.draws.S.a_pos m)).2 (torch.L.V.draws.S.strictAnti.antitone tm)
  have mesh:paceT torch.L.V.draws.S m N=ε:=by
    change torch.L.V.draws.S.a N/torch.L.V.draws.S.a m=ε
    rw [draw,ruler]
  have deployed:paceT L.S m N=ε:=ruler
  let A:=fun i:(Fin ((n+1)+1))=>(price i).buy (X i).Age*fee i
  have atDay (mask:Bits (n+1))(j:ℕ)(mj:m ≤ j)(jN:j ≤ N):=
    wage col (choose (n+1) mask) mask older m j start prev mj jN
  have hearing:=earns torch.L.V X spring dorm older t m N tm prev till (base.le.trans start)
    col a A amp φ y z gap o η fee sep gpos limit look bound
    (fun i=>(authority i).1) (fun i=>(authority i).2.1) (fun i=>(authority i).2.2.1)
    (fun i=>(authority i).2.2.2.1) (fun i=>(authority i).2.2.2.2) costs radius separate far
    (fun mask j mj jN=>by
      have pay:=atDay mask j mj jN
      simpa only [WilsonIndependentMovingRosterNormalizedEarnings.edge,draw,deployed,
        WilsonIndependentMovingRosterNormalizedWallet.amount] using pay)
  intro q hq ω
  simpa only [mesh] using hearing q hq ω

end YM.Integration.WilsonIndependentMovingRosterNormalizedSchool

