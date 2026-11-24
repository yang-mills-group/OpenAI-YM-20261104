import YM.Integration.WilsonMovingForkCapturedFee
import YM.Integration.WilsonOriginalTwoFlatIRMounted

/-! Name the lower ordinary word from the submitted independent compact
copies, at the actual parents of each trial pin. Preserve the issued
optical inverse and the engineering-restored original seed at its own date. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.Integration.WilsonMovingForkPrintedFile
open Function Filter Finset Lattice Wilson RG Source Labels Marker Multi QuadraticLocal QuadraticLocal.Earn
open Push Push.AbsoluteSums QuadraticLocal.Sunrise QuadraticLocal.Poetry QuadraticLocal.Affinity
open PhysicalNext PhysicalNext.Repeat.Legato RG16 RG16.Literal Trace.Physical.GermGraph
open WilsonRootedKioskOccupiedSlip WilsonOlderFreshGraphSlate WilsonRegisteredPairUnaryWallet
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonMovingForkMixedSeed (doses product)
open WilsonThermometerUnitFilingFourSquare (Arm)
open Trace.Pilot OPE WilsonOriginalMixedBlockRows Pert.Asymptotics
open scoped Classical BigOperators Topology
variable {G:Gauge}{R:Run G}{n K:ℕ}{d:Fin n → ℕ}

def allSlots (n:ℕ):(Stock.census (Fin n)).Mode:=⟨univ,mem_univ _⟩

structure Board {side:Side}(G:Gauge){n:ℕ}(pins:Fin n → Site side) where
  index:Type
  [count:Fintype index]
  load:Fin n → ℕ
  order:ℕ
  strip:ℝ
  binder:index → Earn.Binder (Passport.point pins) (Stock.census (Fin n))
  copies:∀a,Copy G (∑i∈(binder a).mode.val,load i) order strip
  wallet:Wallet (room (Fin n))

attribute [instance] Board.count

def parent (R:Run G){i K:ℕ}(ik:i ≤ K)(per:ℕ)(ξ:Fin n → Site (R.family.side K per)):
    Fin n → Site (R.family.side i per):=fun a=>(R.family.S.toDepth ik per).parent (ξ a)

abbrev Program (R:Run G)(d:Fin n → ℕ)(K:ℕ):=
  ∀(_N per:ℕ),((a:Fin n) → R.family.label (d a)) → (ξ:Fin n → Site (R.family.side K per)) →
    (i:ℕ) → (ik:i<K) → Board G (parent R ik.le per ξ)

def row (programme:Program R d K)(N per:ℕ)(w:∀a,R.family.label (d a))
    (ξ:Fin n → Site (R.family.side K per))(i:ℕ)(U:Config G (R.family.side i per)):ℂ:=
  if ik:i<K then
    let b:=programme N per w ξ i ik
    (WilsonOriginalTwoFlatIRMounted.value b.binder b.load b.copies (regulatorRun R.family N per i) b.wallet U).part (allSlots n)
  else if equal:i=K then product R d (N:=N) ξ w (equal ▸ U) else 0

def registered (old:Filed R d K)(programme:Program R d K):Filed R d K:=
  {old with
    row := row programme
    seed := by
      intro N per live w ξ
      funext U
      simp [row]}

theorem matrix (old:Filed R d K)(programme:Program R d K):
    (registered old programme).A=old.A:=rfl

variable {S:Table R.family.book}{l:Ultrafilter (ℕ×ℕ)}{x:∀i,S.Field (d i)}
  (old:Filed R d K)(programme:Program R d K)(arms:∀a,Arm R.family S (l:Filter _) (d a) (x a))

theorem upper {j u v c:ℕ}(jk:j ≤ K)(uv:u ≤ v)(vc:v ≤ c)(ck:c ≤ K)
    (o:Fin n → Cover)(z:ℕ×ℕ)(live:K<z.1)(w:ℝ):
    WilsonMovingForkFiniteCell.Upper (registered old programme) arms jk uv vc ck o z live w ↔
    WilsonMovingForkFiniteCell.Upper old arms jk uv vc ck o z live w:=Iff.rfl

theorem original {j i:ℕ}(jk:j ≤ K)(ik:i<K)(o:Fin n → Cover)(z:ℕ×ℕ):
    let a:=fun h=>(arms h).source z
    let w:=doses R d old.station (N:=z.1) (per:=z.2) (old.A z.1 z.2) a
    let ξ:=WilsonMovingForkSeededPoint.seats (R:=R) jk z.2 o
    let b:=programme z.1 z.2 w ξ i ik
    ∀U,WilsonMovingForkCapturedFee.word (registered old programme) arms jk o z i U=
      (WilsonOriginalTwoFlatIRMounted.value b.binder b.load b.copies (regulatorRun R.family z.1 z.2 i) b.wallet U).part (allSlots n):=by
  intro a w ξ b U
  change row programme z.1 z.2 w ξ i U=_
  simp only [row,dif_pos ik]
  rfl

end YM.Integration.WilsonMovingForkPrintedFile
