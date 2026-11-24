import YM.RGLocalTaylor.Post.Law
/-!
# Restoring actual evaluation

E Taylor errors here are supported regular arrays, not a statement of
pointwise log-relative error on the measure. Still worthwhile to give
the exact reading rule (ALL fields incl all nonempty flag sets; no excisions
on a topology of supports). Uses the same exact K, conserving masks even in
components with seed compulsory partners. Never declare that replacing exact
inputs by the Taylor model is by itself a valid computation of the successor
K. `stamp` functions should be called on the actual Rep always.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor.Post
open Function Filter Set Lattice Wilson RG RG.Shoot Ovens
open AnalyticBridge VerifiedReset Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open PhysicalNext PhysicalNext.Repeat Collection Extra.Iteration Song Refrain Geo Quotes
open Residual WilsonStartup Averaging Progress.DirectedRecipe Extra.Iteration Push.BetaTransport
open UVNext.CouplingReset Input
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {n : Side}
abbrev glyph (G:Gauge)(n:Side):= ℕ → Config G n→ℝ

def imprint (A : Activities G n) (E : glyph G n) : Activities G n := { A with E:= E }
/-- Model counterpart for the estimate. Used on actual K, with beta changed
explicitly for testing error on the kinetic channels. Does not change any
other history data and is not claiming that producing a new history from this
model will have small error. Actual conditional normalization must still be
read from the construction on the true density. -/
def template (V:Rep G n)(m:glyph G n) (b t:ℝ) := {V with activities:= imprint V.activities m,beta:=b,v:=t}

def descending (V:Rep G n)(e:glyph G n) (b t:ℝ) (U:Config G n) :=(V.v-t)*Fintype.card (Site n)-(V.beta-b)*Push.BetaTransport.kinetic V.path V.clip V.p U - (imprint V.activities e).additive V.p U
namespace template
variable {m e:glyph G n} {b x y z δ w t:ℝ} {V:Rep G n} {A:Activities G n} {P:BudgetPoint}
lemma inheritance (E:glyph G n) (hv:A.Valid P x w) (hm:(imprint A E).RegularFamily P) (he:(imprint A E).EBound P z)
    (hM:∀ s b,Nonempty ((imprint A E).Moves s b)): (imprint A E).Valid P z w:=
  ⟨hm,⟨hv.forced.sym,hv.forced.symtest,hv.forced.meas,hv.forced.meas_test,hv.forced.reads,hv.forced.reads_test,hv.forced.permit⟩,hM,he, by obtain ⟨w,hk,h⟩:=hv.boundK; exact ⟨w,hk,h⟩⟩

lemma part (h : A.E=m+e) (he:(imprint A e).RegularFamily P) (ha : A.RegularFamily P) (hh:(imprint A e).EBound P w) (hA:A.EBound P x) : (imprint A m).EBound P (x+w):= by
  obtain ⟨t,ht,hW⟩:=hh; obtain ⟨p,hp,hL⟩:=hA
  have hg i:(imprint A m).E i=A.E i-(imprint A e).E i:= by rw [h]; exact (add_sub_cancel_right ..).symm
  refine ⟨fun i=> p i+t i,fun i=> ?_,fun i=>?_⟩
  · rw [hg]; exact CouplingShape.sup_sub (ha.smooth i) (he.smooth i) (hp i) (ht i)
  convert budget_plus (hL i) (hW i) using 2 with j; dsimp only [imprint,BudgetPoint.mass]; split_ifs <;> ring

lemma recovers (b t:ℝ) (hv: V.activities.E=m+e) (hm : (imprint V.activities m).Valid V.p x w)
    (he:(imprint V.activities e).Valid V.p δ y) (U: Config G n):
    V.eval U=Real.exp (descending V e b t U) * (template V m b t).eval U:= by
  let S i T U:= (imprint V.activities T).regularOccurrence V.p i U
  have hi : V.activities.additive V.p U= (imprint V.activities e).additive V.p U+(imprint V.activities m).additive V.p U:= by
    simp only [Activities.additive]; rw [← Summable.tsum_add ((Activities.ESeries he).summable U) ((Activities.ESeries hm).summable U)]
    apply tsum_congr; intro i
    let T := V.p.threshold; let S:= (V.activities.reg i).support
    change masked T S (V.activities.E i) U= masked T S (e i) U + masked T S (m i) U
    rw [hv]; by_cases hp:Healthy T S U <;> simp [masked_eq,masked_ne,hp,add_comm]
  have hJ : V.exponent U= descending V e b t U + (template V m b t).exponent U:= by
    unfold Rep.exponent descending template; simp only [hi]; rw [channels_split,channels_split (b:=b)]; ring
  rw [Rep.eval,hJ,Real.exp_add,mul_assoc]; rfl
end template
end YM.RGLocalTaylor.Post
