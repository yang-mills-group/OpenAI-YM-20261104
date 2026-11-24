import YM.Integration.FundedMarkedPathSelection
import YM.WilsonCoeffUV.Marked.Paths.Determinism

/-! Numerical Laurent and true compact-root receipts for a named connected log. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshConnectedRobe
open Function Filter Finset MeasureTheory Lattice RG Precision Wilson Tree Exterior
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Embroider
open WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Soil WilsonCoeffUV.Wheel.Flooring
open Work.F08
open scoped BigOperators Classical


open FundedMarkedPathSelection
variable {G:Gauge}{I:Type}[DecidableEq I][Fintype I]
variable {e m N l b kmax:ℕ}{A:ℝ}{k D:I → ℕ}{S J:Finset I}{c:I}
variable (Q:Realm G (e+1) Credit.leanC)(hm:Q.anchor ≤ m)(X:Input Q hm S k D A)

theorem pole (j l:ℕ)(r:Fin (l+j+1)){g:ℝ}(pos:0<g)(small:g ≤ 1):
    g^((j:ℤ)-r.val) ≤ g^(-(l:ℤ)):=by
  apply zpow_le_zpow_right_of_le_one₀ pos small
  have bound:=r.isLt
  omega

private theorem dressed {ι:Type}{fee:ι → ℝ}{M:ℝ}(raw:SumBudget fee M)
    (j l:ℕ)(r:Fin (l+j+1)){g:ℝ}(pos:0<g)(small:g ≤ 1):
    SumBudget (fun u=>g^((j:ℤ)-r.val)*fee u) (g^(-(l:ℤ))*M):=by
  have h:0 ≤ g^((j:ℤ)-r.val):=zpow_nonneg pos.le _
  have hm:0 ≤ M:=(tsum_nonneg raw.1).trans raw.2.2
  refine ⟨fun u=>mul_nonneg h (raw.1 u),raw.2.1.mul_left _,?_⟩
  rw [tsum_mul_left]
  exact (mul_le_mul_of_nonneg_left raw.2.2 h).trans (mul_le_mul_of_nonneg_right (pole j l r pos small) hm)

def Rendered (J:Finset I)(c:I)(l N:ℕ)(y:I → Cover):Prop:=
  let P:=sphere (output X J N y) l (e+1) c y
  let T:=shifted (baton P (e+1)) (y c)
  ∀j ≤ e,Auth l T ∧ T.2 j=(output X J N y).2 j ∧
    ∀n r,T.1 n j r=Carp.plume ((output X J N y).2 j r) n

def Rooted (J:Finset I)(c:I)(l N:ℕ)(width mass:ℝ)(o:Cover)(j:ℕ)(r:Fin (l+j+1)):Prop:=
  let Z:=fun x:Frill J c × RadP G r.val=>packetH J (output X J N) l (e+1) c o x.1 j r x.2
  ∃ μ:(x:Frill J c × RadP G r.val) → Stationary.Ink G r.val → Measure (Sky D),
    (∀x,Barn (Z x) (μ x)) ∧
    (∀x (t:Case D) {n:Side} (U:Config G n)(root:Site n),
      (Rolls.dip (Z x) (touch t J)).unmasked U root =
         ∑a,(∫y:Sky D,Express.mica t J y ∂μ x a)*(sprigB (Z x) a).unmasked U root) ∧
    let fee:=fun x:Frill J c × RadP G r.val=>
      Real.exp (width*feeH (toe J c o x.1) c J)*lease (Z x) (μ x) width
    SumBudget fee mass ∧ ∀g:ℝ,0<g → g ≤ 1 → 
      SumBudget (fun x=>g^((j:ℤ)-r.val)*fee x) (g^(-(l:ℤ))*mass)

theorem issued (sub:J ⊆ S)(root:c ∈ J)(pos:0 ≤ A)(live:m<N)(closed:Cloze D k Q Credit.leanC)
    (rank:∀y n,WilsonCoeffUV.Blue.shellK l ((output X J N y).1 n))
    (tickets:Insure b kmax Q Credit.leanC)(count:J.card ≤ b)(seat:l ≤ kmax):
    (∀y,Rendered Q hm X J c l N y) ∧ ∀o j,j ≤ e → ∀r:Fin (l+j+1),
      Rooted Q hm X J c l N (VestS b kmax Q m hm)
        (Rolls.glacier G l (e+1)*VestZ b kmax Q m hm*price Q k D A J m*sprigs J c (Vσ Q m hm)) o j r:=by
  have readyAt:=fun y=>ready X sub pos live closed y
  have auth (y:I → Cover):Auth l (output X J N y):=
    ⟨(readyAt y).1.wing,rank y,(readyAt y).1.pale,(readyAt y).1.token⟩
  have base:0 ≤ price Q k D A J m:=mul_nonneg (zero_le_one.trans (Credit.purchase _ (Q.depth m hm))) (pow_nonneg pos _)
  have post:=fun y=>Rolls.posting (tickets.proof m hm) y (output X J N y) root seat count _ base
    (auth y) (readyAt y).2 (le_refl (e+1))
  refine ⟨fun y j hj=>(post y).2.2 j (by omega),?_⟩
  intro o j hj r
  obtain ⟨μ,born,raw⟩:=rolled_sum (tickets.proof m hm) (output X J N) root seat count
    (le_refl (e+1)) base auth (fun y=>(readyAt y).2) o j (by omega) r
  refine ⟨μ,born,?_,raw,fun _ hg h1=>dressed raw j l r hg h1⟩
  intro x t n U y
  apply Rolls.packet _ t _ _ (born x) U y
  exact (((post (toe J c o x.1)).1.2 j (by omega)).2 r).1 x.2

theorem original (sub:J ⊆ S)(root:c ∈ J)(pos:0 ≤ A)(live:m<N)(closed:Cloze D k Q Credit.leanC)
    (tickets:Insure b kmax Q Credit.leanC)(count:J.card ≤ b)(seat:mass k J ≤ kmax):
    (∀y,Rendered Q hm X J c (mass k J) N y) ∧ ∀o j,j ≤ e → ∀r:Fin (mass k J+j+1),
      Rooted Q hm X J c (mass k J) N (VestS b kmax Q m hm)
        (Rolls.glacier G (mass k J) (e+1)*VestZ b kmax Q m hm*price Q k D A J m*sprigs J c (Vσ Q m hm)) o j r:=
  issued Q hm X sub root pos live closed (fun y=>(ready X sub pos live closed y).1.span) tickets count seat

end YM.Integration.WilsonOlderFreshConnectedRobe
end
