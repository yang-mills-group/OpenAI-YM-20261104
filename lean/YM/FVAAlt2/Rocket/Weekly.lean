import YM.FVAAlt2.Rocket.Splice
import YM.FVAAlt2.Rocket.Fan
/-! # Request paths through the history overlap. In particular different dimensions or
 trade/budget witnesses through different requests don't affect terms shared in overlap! -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Lodge.Contract
open Function Set Filter MeasureTheory Topology Real Finset Lattice RG Precision Gauge
open Oracle Epoch Calibration Rocket Uniform Binding Diagram Ledger Taping Atlas Epoch.League
open PhysicalNext.Repeat.Legato Family Run
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius
variable {X W:Type} {G:Gauge}{K:KernelChoices} (Y:Oracle.Program K)(Z:∀ Q:Patch,Q.Branches K G)(C:Run G)(T:Contract C Y Z)
variable (stamp:X→ℕ)(H:∀ x,T.floor Y Z C ≤ stamp x)(earn:W→ℕ)(h:∀ x,T.floor Y Z C ≤ earn x)
local notation "B"=> T.profile Y Z C stamp H
local notation "Ψ"=> T.profile Y Z C earn h
variable (u:X→ W)(he:∀ x,stamp x= earn (u x))
include he
lemma same_sizes(x:X): (B).entire x=(Ψ).entire (u x):=by rw [T.thick,T.thick, he]
def passages: Section (B).desk (Ψ).desk where
   cast_r:=u
   connects i := ⟨u i.bindW,i.downW,(i.good.trans_eq (T.same_sizes Y Z C stamp H earn h u he i.bindW))⟩
   from_w _:= rfl
   fly i:= ⟨u i.volW,i.offset,i.ok.trans_eq (T.same_sizes Y Z C stamp H earn h u he i.volW) ⟩
   previous _:= rfl
   next _:=rfl
   pact i:=by
      change (Ψ).desk.pactP _=( B ).desk.pactP _
      unfold Circuit.pactP; congr 1
      · exact congr_arg C.family.path.levels.clock.factor ( he i.volW |>.symm )
      exact (he i.volW).symm
local notation "L"=> T.passages Y Z C stamp H earn h u he
lemma restores : ∀ i, (L).connects ((native (B).entire).choose i)=(native (Ψ).entire).choose ((L).cast_r i):= fun _=>rfl
lemma clips : ∀ i, (L).connects ((B).stop.choose i)=(Ψ).stop.choose ((L).cast_r i):=by
    intro i; let k:=(B).stop.choose i; let z:=(Ψ).stop.choose ((L).cast_r i)
    have hp:(B).long i=(Ψ).long ((L).cast_r i):=mul_left_cancel₀ (a:=2) (by norm_num) ( T.same_sizes Y Z C stamp H earn h u he i )
    dsimp only [ Choice.choose, passages ]; congr 1
lemma actualLe (i): T.atLevel Y Z C stamp H i=T.atLevel Y Z C earn h ((L).connects i):=by
    unfold atLevel
    congr 1
    · unfold Contract.ceiling; congr 1 <;> apply he
end YM.RegulatorIR.FVAAlt2.Lodge.Contract
