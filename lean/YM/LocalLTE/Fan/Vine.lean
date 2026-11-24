import YM.LocalLTE.Fan.Wake
/-! All real Bochner numerator formulas. Measurability of transformed marg kernels even outside posture. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Fan
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Blaze.March Captain Mask Raw Matter Frond Coat Vine
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Brush Foramen Pastel
variable {v z r W w s t y η γ B a μ: ℝ} {j n m : ℕ} {Q: YM.ConnectedActivityE6.Target G P}{o: Target.Order G W}{R:Rep G f}
variable (X:Coat T F)
lemma vow_b (H: Cash W t μ L Q o a T R)(hp:X.x=t)(hX:X.width=o.K)(i:Veil c f)(p:Disk G c): Measurable fun z:Air f G=> vows X R Q o.a p z i:= by
  let Z:=timeΛ X p; let F' (z:Air f G):= vows X R Q o.a p z i
  have hh := H.laws.data; have hk := Shield.bornB Z (Y:=fun _:Air f G=> Z.Y) (V:=fun _:Air f G=> Z.V)
     (show ShellAccess S G Z.x W Z.width o.γ from by change ShellAccess _ _ X.x W X.width _; rw [hp,hX]; exact hh.access)
     (show Intake P T Z.x R from hp.symm ▸ H.laws.intake) Q.table_exists measurable_const measurable_const (u:=id) measurable_id o.a 0 ∅ (elastic (S:=S) i)
  have he : Measurable fun z=> Real.exp (F' z)-1:=hk
  have h': Measurable fun z=> Real.log (Real.exp (F' z)-1+1):= Real.measurable_log.comp (he.add measurable_const)
  simpa only [sub_add_cancel,Real.log_exp] using! h'
lemma vines_b (H: Cash W t μ L Q o a T R)(hp:X.x=t)(hX:X.width=o.K)(p:Disk G c) (i: Veil c f): Measurable fun z=> coming Q.table R X p z i:=by
  let Z:=timeΛ X p; let u z :=switchΛ X z p
  have he : Measurable u:= measurable_const.add (Measurable.smul (measurable_const (a:=p.1)) (measurable_pi_lambda _ fun i=> (X.tale i).measurable))
  have h:Measurable fun z:Air f G=> inputΛ X z p:= by
    simp_rw [openingΛ]; apply Z.summon (Y:=fun _:Air f G=> Z.Y) measurable_const he
  let A:=-R.beta*orientation
  have ht {d:ℕ}(P:ℕ→Atom G d)(i:Trans f)(b:ℝ) : Measurable fun z=> atomΛ X P i b z p:= measurable_const.mul (((Atom.unmasked_cont ..).measurable).comp ((continuous_pull ..).measurable.comp h))
  have hM:=H.laws.data
  rcases i with i|i|i|i|i
  · exact (((H.laws.intake.cap.labels.regular.smooth i).borel).comp h).neg
  · exact ht _ _ _
  · exact ht _ _ _
  · exact ht _ _ _
  rcases i with i|i|i
  · change Measurable fun z=> A*sourceΛ X i z p; apply Measurable.mul measurable_const
    have hh z: sourceΛ X i z p=Polar.rootface Z (u z) (Z.input (u z)) true i.1 i.2+ Vine.costs Z (voltage Z) i.1 i.2:= congr_arg (fun x=> x+Vine.costs Z (voltage Z) i.1 i.2) ((Vine.patch_rep X (Vine.pass p) (u z) i).symm)
    simp_rw [hh]; apply Measurable.add _ measurable_const; unfold Polar.rootface
    apply Measurable.sub; apply Shield.liftB hM.funds.funds measurable_const
    apply (continuous_pull ..).measurable.comp
    exact Z.summon (Y:=fun _:Air f G=> Z.Y) measurable_const he
    refine Finset.measurable_fun_sum _ fun i' _=> ?_; unfold Vine.pot; split; next=> exact ((((Shield.strains hM.funds.funds (V:=fun _:Air f G=>Z.V) measurable_const Z (Y:=fun _:Air f G=> Z.Y) measurable_const (show ShellAccess S G Z.x W Z.width o.γ from by change ShellAccess _ _ X.x W X.width _; rw [hp,hX]; exact hM.access) he _ i').norm).pow_const (2:ℕ)).div_const 2)
    exact measurable_const
  · exact measurable_const (a:=Z.undercurrent i)
  change Measurable fun z=> solar X z Q.table p i; unfold solar; split
  next h=> exact Real.measurable_log.comp (Q.table_exists.borel.comp ((measurable_pi_apply i).comp he)) -- edit
  exact measurable_const
end YM.LocalLTE.Fan
