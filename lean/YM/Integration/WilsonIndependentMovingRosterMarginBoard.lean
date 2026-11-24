import YM.Integration.WilsonIndependentMovingRosterMarginOptics
import YM.Integration.WilsonIndependentCutJoinNativeFrames

/-! The anchor certificate needed by the optical margin at every report
on the selected board, including its compensated Wick theatre. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMovingRosterMarginBoard
open Filter Function Finset Lattice RG RG.Supply Wilson PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open XSpace XSpace.Rose XSpace.Cirrus Source Source.Drops Labels Precision Next.Foundations
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Bank.PathCost
open WilsonCoeffUV.Embroider WilsonCoeffUV.Shard WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.AuxPlates
open RegulatorIR RegulatorIR.Ledger
open WilsonIndependentExactPlate (Requests)
open WilsonIndependentEvenPassport (old)
open WilsonIndependentMovingRosterMarginOptics (Billed)
open scoped BigOperators Classical Topology
local notation "C" => Credit.leanC
variable {G:Gauge}{H:Hol G}{e height seats j extra:ℕ}{I J:Type}[Fintype I][Fintype J]

theorem original (M:Master H)(chart:ChartRatio G)(kernel:KernelChoices)(V:XSpace.Run)
    (B:WilsonIndependentEvenPassport.Menu M chart kernel V e height seats j extra)
    (grant:WilsonIndependentCutJoinPlate.Approved M chart kernel V e height seats j extra B)(phase:4 ≤ j)
    (report carry:J→Credit)(cost:J→ℕ)(rate:I→Credit)(η:ℝ)(small:0 < η):
    ∀ᶠ idx:ℕ in atTop,∀i:Requests B.a,i.val=idx →
      let cir:=WilsonIndependentExactPlate.S V B.a B.positive j phase
      let n:=WilsonIndependentExactPlate.M V B.a i
      let r:Fin B.a:=⟨i.val%B.a,Nat.mod_lt _ B.positive⟩
      ∃(A:Levels G)(s:ℕ),A.clock.kernel=kernel ∧
        (∀f:Flap (WilsonIndependentExactPlate.M V B.a),f.volW=i → ∀per:ℕ,
          (A.clock.op (s+(n-(f.offset+1))) per).patch=cir.pactP f) ∧
        A.S.scale (s+n)-A.S.scale (s+old V B.a idx)= -Real.log (V.step idx).spacing ∧
        ∀(h D:ℕ)(p:h<D),h ≤ height → D ≤ seats →
          ∃W:ChorusLine H (M.T h) p e C C C,W.arch.V.draws=A ∧ W.arch.V.paid=chart ∧
            W.arch.V.y=extendedY (B.price r) A.S (s+n) ∧ W.arch.V.anchor=s ∧
            (∀z ≤ n,W.arch.V.y (s+z)=B.price r) ∧ Weston W.arch C ∧
            (∀(k u:ℕ)(v:Rails h k u e),k ≤ seats → u ≤ seats → ∃L:Torch H (M.T h) p v C C C,L.L=W.arch) ∧
            WilsonIndependentMovingRosterAllFineSeats.Elected M W.arch.V height seats ∧
            WilsonIndependentCutJoinNativeFrames.Funded M W.arch.V height seats ∧
            ∀q:J,Billed W.arch.V (report q) (carry q) (cost q) rate s (s+n) ((V.step idx).spacing^(-η)):=by
  filter_upwards [WilsonIndependentMovingRosterMarginOptics.family (G:=G) (e:=e) (E:=C)
    V B.a j B.positive phase report carry cost rate B.cap η small] with idx billed i eq cir n r
  subst idx
  obtain ⟨A,s,ker,_,patch,clock,step,all⟩:=WilsonIndependentCutJoinPlate.optics M chart kernel V e height seats j extra B grant phase i
  refine ⟨A,s,ker,patch,clock,?_⟩
  intro h D p hh dim
  obtain ⟨W,draw,quiet,money,anchor,west,_,torches,rests⟩:=all h D p hh dim
  have row:∀z ≤ n,W.arch.V.y (s+z)=B.price r:=by
    intro z hz
    rw [money]
    exact step z hz
  have bank:W.arch.V.y s ≤ B.cap:=by
    have first:=row 0 (Nat.zero_le _)
    change W.arch.V.y s=B.price r at first
    exact first.le.trans (B.limits r).2
  exact ⟨W,draw,quiet,money,anchor,row,west,torches,
    WilsonIndependentMovingRosterAllFineSeats.original M A chart _ s all W.arch.V draw quiet money anchor rests,
    WilsonIndependentCutJoinNativeFrames.original M A chart _ s all W.arch.V draw quiet money anchor,
    billed i rfl A s (fun f hf=>patch f hf 0) W.arch.V draw anchor bank⟩

end YM.Integration.WilsonIndependentMovingRosterMarginBoard

