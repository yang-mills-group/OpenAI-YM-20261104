import YM.Integration.WilsonMarkedIndependentFoldedBirth

/-! The original finite one-source folded Wilson integral and its covered
marked tensor on the very same registered page. The period, the ultraviolet top,
the source positions and the real tests are read only after funding. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentRegisteredFoldedSeam
open Function Filter Finset Lattice Wilson RG Precision Laurent Source Labels Marker WilsonCoeffUV
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.Realm
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Blue WilsonCoeffUV.Soil
open WilsonCoeffUV.Embroider WilsonCoeffUV.Winding
open AnalyticNext.QuarticMatch.Sheets IndependentSourcePathFamily FundedMarkedPathSelection
open Function Filter Lattice Wilson RG Laurent Next.Foundations Precision
open PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Winding
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Address
open WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Embroider ActualRunAdmissionScales
open Work.F08
open scoped Classical BigOperators
variable {G:Gauge}{ι:Type}[Fintype ι][DecidableEq ι]{D k:ι→ℕ}{I:ι→Type}[∀i,Fintype (I i)]
variable {m N e j r d c q t:ℕ}

def row (R:Run G)(Q:Realm G (e+1) Credit.leanC)(N m per:ℕ)(s:ι)(j r:ℕ)(k:ι→ℕ)
    (X:∀i,I i→Seed G (D i))(cells:(ι → Cover)→ι→Site (loose Q.draws m).L):=
  let A:=Q.draws
  let O:=Q.paid
  let L:=loose A m
  let n:=R.family.side m per
  let f:=n*L.L
  let input y:=independent X (chartIn L y (cells y))
  let vol:=emera (actionW A O N (m+1)) f
  RootedPeriodicMarkedWinding.row n {s} s (fun loc=>
    let x:=PeriodicMarkedWinding.roots n loc s
    let F:=((logO A O m N (input x) k {s}).2 j r)
    let P:=reed (stepAt L A.clock.kernel n) (xree L A.clock.kernel n) (freeForms A N (m+1))
      (roam A N m n) O vol (mass k {s}) (((input x) {s}).1 f)
    Carp.plume F n-(Blue.mix (ratioHigh A O N m) P) j r)

def Bill (R:Run G)(Q:Realm G (e+1) Credit.leanC)(hm:Q.anchor ≤ m)(N per:ℕ)(s:ι)(j r d c q t:ℕ)
    (k:ι→ℕ)(X:∀i,I i→Seed G (D i))(cells:(ι → Cover)→ι→Site (loose Q.draws m).L)
    (w σ:Gear G→ℝ):Prop:=
  let A:=OriginalIssuedMarkedRows.fee (k:=k) X Q hm w
  let g:=Pert.Asymptotics.regulatorRun R.family N per (m+1)
  let n:=R.family.side m per
  let width:=σ (Q.mint m hm).gear
  ∃B:ℝ,B*g^(-(c:ℝ))≤g^q*A ∧ B≤(admittedCost R.family.path.levels m)^t*
    (Real.exp (-(width/512)*(n.val:ℝ))*A) ∧
    PostMark {s} s r (row R Q N m per s j r k X cells) (width/32/2/2/2) B d

/-- The paid native Gazette step at a genuine nonbare appointment on this
authenticated R. Only the enrolled one-source angular tensor is inserted. -/
theorem receipt (R:Run G)(Q:Realm G (e+1) Credit.leanC)(hm:Q.anchor ≤ m)(s:ι)
    {w σ:Gear G→ℝ}(hw:∀U,0<w U)
    (income:FundedMarkedWindingWindow.ReceiptOn R {s} {s} s D k e j r d c q t w σ m Q hm)
    (per:ℕ)(live:m<N)(X:∀i,I i→Seed G (D i))(h:∀i b,(X i b).rank≤k i+(X i b).head)
    (cells:(ι → Cover)→ι→Site (loose Q.draws m).L):Bill R Q hm N per s j r d c q t k X cells w σ:=by
  let L:=loose Q.draws m
  let E:=OriginalIssuedMarkedRows.input X Q hm w hw {s} cells h
  have entry:=OriginalIssuedMarkedRows.enters (k:=k) X Q hm w hw {s} cells h
  have price:=income N per live E.familyAt cells _ entry.1 entry.2
  obtain ⟨B,pay,wind,post⟩:=price
  refine ⟨B,by simpa using pay,by simpa using wind,?_⟩
  let n:=R.family.side m per
  have seen (x:ι → Cover):coilH Q.draws Q.paid m N n (E.familyAt x) k
        (ratioHigh Q.draws Q.paid N m) {s}=Blue.mix (ratioHigh Q.draws Q.paid N m)
      (reed (stepAt L Q.draws.clock.kernel n) (xree L Q.draws.clock.kernel n) (freeForms Q.draws N (m+1))
        (roam Q.draws N m n) Q.paid (emera (actionW Q.draws Q.paid N (m+1)) (n*L.L))
        (mass k {s}) ((E.familyAt x {s}).1 (n*L.L))):=
    WilsonMarkedIndependentFoldedBirth.original Q.draws Q.paid m N n s X h
      (chartIn L x (cells x)) (ratioHigh Q.draws Q.paid N m)
  change PostMark {s} s r (RootedPeriodicMarkedWinding.row n {s} s (fun loc=>
    let x:=PeriodicMarkedWinding.roots n loc s
    Carp.plume ((logO Q.draws Q.paid m N (E.familyAt x) k {s}).2 j r) n-
      coilH Q.draws Q.paid m N n (E.familyAt x) k (ratioHigh Q.draws Q.paid N m) {s} j r)) _ B d at post
  dsimp only at post
  simp_rw [seen] at post
  exact post

/-- The derivative, source width and rooted bill are chosen on the original
course before every cutoff, period and fresh source. -/
theorem original (s:ι)(D k:ι→ℕ)(e j r d:ℕ)(hj:j ≤ e)(w:Gear G→ℝ)(hw:∀I,0<w I):
    ∃(v:ℕ→Gear G→ℝ)(σ:Gear G→ℝ)(t:ℕ),(∀I,0<σ I) ∧ (∀b I,(σ I)⁻¹≤v b I) ∧
      WilsonLimitConstruction.FundedPredictionSupply.AllPrices (@FundedMarkedCoverRows.prices G v) ∧
      ∀(R:Run G),G.Simple → RG05Preconstruction.ReadoutPurchase R.b → ∀c q:ℕ,
        ∀ᶠ m:ℕ in atTop,∀(Q:Realm G (e+1) Credit.leanC)(hm:Q.anchor ≤ m),
          Q.y=zz R.family.path.levels → v (R.family.path.levels.clock.J (m+1)) (Q.mint m hm).gear≤Q.cash Credit.leanC m →
          ∀N per,m<N → ∀(I:ι→Type)[∀i,Fintype (I i)](X:∀i,I i→Seed G (D i)),
            (∀i b,(X i b).rank≤k i+(X i b).head) → ∀cells,Bill R Q hm N per s j r d c q t k X cells w σ:=by
  obtain ⟨v,σ,t,hot,wide,tags,file⟩:=FundedMarkedWindingWindow.pricedOnWithRate
    (J:={s}) (Z:={s}) le_rfl s (Finset.mem_singleton_self s) D k e j r hj w hw d
  refine ⟨v,σ,t,hot,wide,tags,?_⟩
  intro R simple bought c q
  filter_upwards [file R simple bought c q] with m ready
  intro Q hm pace cash N per age I inst X lawful cells
  exact receipt R Q hm s hw (ready Q hm pace cash) per age X lawful cells

end YM.Integration.WilsonMarkedIndependentRegisteredFoldedSeam
end
