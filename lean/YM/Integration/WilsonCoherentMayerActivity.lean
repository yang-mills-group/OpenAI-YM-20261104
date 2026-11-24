import YM.Integration.WilsonCoherentMayerSurvivor

/-! The actual signed compact activity with its original omitted column and every retained order. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonCoherentMayerActivity
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open Blaze.March PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt RGLocalTaylor RGLocalTaylor.Insert
open RG01.Survive PhysicalNext.Repeat.Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open AnalyticBridge.LocalGaussianLaws PhysicalNext.Repeat.Legato WilsonCoherentMayerGate WilsonCoherentMayerSubmission
open WilsonCoherentMayerSignedCharge (polynomial residual)
open LocalLTE.Fan
variable {G:Gauge} {c f L:Side}{S:StepData c f}{T:Tube G S}{R:Rep G f}
    {P:Teller G}{Q:ConnectedActivityE6.Target G P}{W s μ C:ℝ}{o:Target.Order G W}
    (run:Run G) {I:Type} [Fintype I] (d:I→ℕ) (H:Cash W s μ L Q o C T R)
    (M taylor:ℕ) (share:ℝ)


variable {j k:ℕ} {c' d' v Y A a r B q θ:ℝ} {N:Captain H j c' d' v Y A a r B q k Chi.canonical}
    (paid:WilsonCoherentMayerSurvivor.Returned run d H M taylor share N.conduit.fare θ)
    (entry:Submitted run R I) (same:d=entry.grade) (contract:∀i z,|entry.phase i z|≤‖z‖)
    (old:Team R) (fresh:∀m∈old.own,∀i,m.turn≠(row entry i).turn)
    (loc:H.ThinP) {veil:Finset (Veil c f)} {height:ℕ} (stage:MeasuredSupport.Component H loc veil height)
variable (coverage:Team.signs (together entry old fresh) S⊆loc.val)

def budget:ℝ:=(old.weight*(∏i∈loc.val\Team.signs (together entry old fresh) S,N.conduit.fare i)*
    Mayer.spreadRate M θ 1^loc.val.card)*(WilsonCoherentReportingPivot.mass run entry.grade R.p.threshold entry.label*share)

private theorem charge (M : ℕ) (L : Fin (M+2) → ℝ) (P : Fin (M+1) → ℝ)
    (K : ℝ) (fee : ∀ e, |L e.castSucc-P e| ≤ K) :
    |(∑ j, L j) - (L (Fin.last (M+1)) + ∑ e,P e)| ≤ (M+1:ℝ)*K := by
  rw [Fin.sum_univ_castSucc]
  have regroup : (∑ e:Fin (M+1),L e.castSucc) + L (Fin.last (M+1)) -
      (L (Fin.last (M+1)) + ∑ e, P e) = ∑ e, (L e.castSucc-P e) := by
    rw [Finset.sum_sub_distrib]
    ring
  exact (congrArg abs regroup).le.trans ((Finset.abs_sum_le_sum_abs _ _).trans
    ((Finset.sum_le_sum (fun e _ ↦ fee e)).trans (by simp [nsmul_eq_mul])))

include paid same contract stage coverage in
theorem measured:
    |((together entry old fresh)).lotus T s Chi.canonical o.K W o.a Q.table Q.halo (1:Config G c) loc.val-
       (Laminate.column (together entry old fresh) loc.val H (χ:=Chi.canonical) M (Fin.last (M+1)) 1+
        ∑e:Fin (M+1),WilsonCoherentMayerColumn.model (χ:=Chi.canonical) (M:=M)
           run entry old fresh taylor loc e.val)|≤
      (M+1:ℝ)*budget run H M share (N:=N) (θ:=θ) entry old fresh loc:=by
  have empty:(roster loc.val).flags=∅:=by rw [stage.lift,LocalLTE.Fan.Field.rosterD]
  have flags:RG.flags (Pressure.temp s) (1:Config G c)=∅:=by
    let i:Greenbelt.Reserve S:=Classical.arbitrary _
    exact ((prism T s Chi.canonical o.K (1:Config G c) (Greenbelt.allot i)).bowed (SectorMeasure.temp_nonneg _)).symm
  have healthy:Healthy (Pressure.temp s) (H.unionP loc.val) (1:Config G c):=by
    change Disjoint _ (RG.flags (Pressure.temp s) (1:Config G c))
    rw [flags];exact Finset.disjoint_empty_right _
  have truth:=Laminate.teamLecturer (M:=(together entry old fresh)) (S:=S) (T:=T) (R:=R) (H:=H) (P:=P) (Q:=Q) (o:=o) (χ:=Chi.canonical)
    (p:=loc.val) (j:=j) (C':=c') (d:=d') (v:=v) (Y:=Y) (A:=A) (b:=a) (r:=r) (B:=B) (q:=q) (n:=k) coverage (1:Config G c) N empty
  rw [masked_eq _ _ _ _ healthy] at truth
  have whole:(∑j:Orders M,Laminate.column (together entry old fresh) loc.val H (χ:=Chi.canonical) M j 1)=
      ((together entry old fresh)).lotus T s Chi.canonical o.K W o.a Q.table Q.halo (1:Config G c) loc.val:=by
    rw [←Finset.sum_apply,Laminate.passport (together entry old fresh) loc.val H M coverage,←truth]
  let K:=budget run H M share (N:=N) (θ:=θ) entry old fresh loc
  let L₀ : Orders M→ℝ:=fun j=>Laminate.column (together entry old fresh) loc.val H (χ:=Chi.canonical) M j 1
  let P₀ : Fin (M+1)→ℝ:=fun e=>WilsonCoherentMayerColumn.model (χ:=Chi.canonical) (M:=M)
    run entry old fresh taylor loc e.val
  have fee (e:Fin (M+1)): |L₀ e.castSucc-P₀ e|≤K:=by
    have fitting : e.castSucc.val≤M:=Nat.le_of_lt_succ e.isLt
    exact paid entry same contract old fresh loc veil height stage coverage e.castSucc fitting
  have priced:=charge M L₀ P₀ K fee
  have equal:=congrArg (fun v:ℝ=>|v-(L₀ (Fin.last (M+1))+∑e,P₀ e)|) whole.symm
  exact equal.le.trans priced

end YM.Integration.WilsonCoherentMayerActivity
