import YM.Integration.WilsonCoherentLampTicket
import YM.Integration.WilsonMatrixTicketLanesRetainedPrincipal
import YM.Integration.WilsonMatrixTicketLanesReflectedInner

/-! The actual positive conditional and its first registered cup polynomial on an arbitrary held field. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesRetainedRoster
open PertExtension.Series.Tested RGComparison.Core16.Lumen.Stage
open Function Filter MeasureTheory Finset Lattice RG Tree Gauge Wilson Precision PowerSeries
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Radial PertExtension.GaussianScore
open FormalOPE.RG10 FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Splice FormalOPE.RG10.MultiGauge.Stack
open FormalOPE.RG10.MarkovChain.Router FormalOPE.RG10.OpenSlots RGComparison.Core16 RGComparison.Core16.Lumen
open RGComparison.Core16.Lumen.Planet RGComparison.Core16.Forge RGComparison.Core16.Parcel RGComparison.Core16.Spool
open FVA2 FVA2.CityHistory WilsonCoherentLampTicket WilsonMatrixTicketLanesReflectedInner
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {I : Type} [Fintype I] (J : I→Lamp G) {c f : Side} (S : StepData c f)
  (T : Tree.Forest S.ratio) (o : I→Site f) (part : Bool)

def placed (x : Future G S T) : Slice J→G.Color := Fk.scene (earns S T J o) (0,x)

omit [Fintype I] in
theorem origin : placed J S T o 0=0 := by
  funext i;unfold placed Fk.scene;cases (earns S T J o) i <;> simp [Fk.spread]

theorem analytic : ContDiffAt ℝ ω (placed J S T o) 0 := by
  apply contDiffAt_pi.mpr;intro i;unfold placed Fk.scene
  cases (earns S T J o) i with
  | inl e => exact (turn_hot (G:=G)).contDiffAt.comp (f:=fun x:Future G S T=>x e) _ (contDiff_apply ℝ _ _).contDiffAt
  | inr e => change ContDiffAt ℝ ω (fun _ : Future G S T=>(0:ℝ)•e) 0;exact contDiffAt_const

/-- An arbitrary family of honest insertions keeps the total recorded grade after the actual
nonlinear angular chart, including the original locations and all unoccupied/trunk links. -/
theorem graded : RadialOrder (power J) (source J S T o part) := by
  intro z
  let a (t : ℝ) := sight J (placed J S T o (t•z.1))
  let g (i : I) (t : ℝ) := (J i).action (heavens J i (placed J S T o (t•z.1)))
  have prod : a=∏ i,g i := by ext t;simp_rw [Finset.prod_apply];rfl
  have billed (i : I) : Bill (J i).order (g i) := by
    obtain ⟨m,B,L,h,hL⟩:=(J i).basis
    let Y : Future G S T → CoverConfig G := heavens J i ∘ placed J S T o
    have smooth (e) : ContDiffAt ℝ ω (fun x=>G.mat (Y x e)) 0 := by
      have outer:=pastor J i e
      rw [←origin J S T o] at outer
      exact outer.comp _ (analytic J S T o)
    have at0 : Y 0=1 := by simp only [Y,comp_apply,origin,past_zero]
    unfold g;rw [h];exact shadow smooth at0 B _ L hL z.1
  obtain ⟨C,hC,fee⟩:=(show Bill (power J) a from (prod ▸ bill_product _ _ _ (fun i _=>billed i)))
  refine ⟨‖look part‖*C,by positivity,fee.mono (fun t ht=> ((look part).le_opNorm (a t)).trans ((mul_le_mul_of_nonneg_left ht (norm_nonneg _)).trans_eq (mul_assoc ..).symm))⟩

theorem prepare : Stack.rise (source J S T o part) = X^(power J)*Stack.drop (power J) (Stack.rise (source J S T o part)) := by
  symm;apply Stack.recover;intro k hk
  rw [Stack.rise,coeff_mk];apply Subtype.ext
  exact jets_vanish ((admitted J S T o part).of_le le_top) (graded J S T o part) hk

/-- The actual normalized positive one-block principal at arbitrary retained pin, on precisely
this registered finite roster. Its conditional shift is computed from the true initial Hessian. -/
theorem original {P : Oven S.patch} (X : P.Form G) (offer : P.Offers X S.kernel) (Z : ChartRatio G) (hz : LocalRatio Z)
    (large : Bid.Larger (G:=G) S) (tag : S.Choices) (nil : (Descent.nil (top:=f)).Tags) (u : Directions G c) (pin : ∀ i,‖u i‖≤X.Q) :
    Spool.rankℝ J S T X Z u o part 0 = (law S T large tag nil).average (tangent G T.Free)
      (fun x=>Radial.jet (source J S T o part) (power J) (x+(precision S T tag nil).skew (sound S T large tag nil) u,u)) := by
  have h:=WilsonCoherentLampTicket.booked J S T o part X Z hz large u offer pin tag nil
  have zero:=congrArg (coeff (R:=ℝ) 0) h
  simp only [coeff_mk,Stack.drop,Nat.add_zero] at zero
  rw [zero,solenoid,prepare]
  have paid:=CityHistory.primeZ (S:=S) (T:=T) (d:=Descent.nil) (t:=nil) (b:=tag) (Z:=Z)
    (z:=1) (hz:=hz) (h:=large) (H:=trivial)
  rw [WilsonMatrixTicketLanesRetainedPrincipal.initial _ _ _ _ _ paid]
  rw [←coeff_zero_eq_constantCoeff_apply,Stack.drop,coeff_mk,Nat.add_zero,Stack.rise,coeff_mk];rfl

end YM.Integration.WilsonMatrixTicketLanesRetainedRoster
