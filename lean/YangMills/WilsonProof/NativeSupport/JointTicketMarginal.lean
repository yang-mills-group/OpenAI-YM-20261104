import YangMills.WilsonProof.NativeSupport.JointTicket
import YangMills.WilsonProof.NativeSupport.JointCoatLocality

/-! Conditional local equality for an actual planted ticket carrying transition
energies. The two Gaussian laws can be different outside the paid support. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.JointTicket
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset
open MeasureTheory Push Push.BetaTransport Push.AbsoluteSums Precision Exterior ConnectedActivityE6
open Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Mask Contract Work.F03
open Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse Coat Matter
open ProbabilityTheory Poll Pond PhysicalNext.Repeat PhysicalNext.Repeat.Lotus JointCoat
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P : Teller G} {T : Tube G S}
    {F : Forest S.ratio} {R : Rep G f} {W μ C : ℝ}
    {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W}
    {X Y : Coat T F} {Z : Support c} {k l : Finset ℕ} {p : Molecule S}
variable (K : Team R) (H : Cash W X.x μ L Q o C T R)
variable (J : Finset (Bond c)) (h : Bond c→ℝ→ℝ)

include H
theorem measurable_raw (width : X.width=o.K) (hm : ∀ b∈J,Measurable (h b)) :
    Measurable (raw (W:=W) K X k p o.a Q.table Q.halo J h) := by
  exact (Finset.measurable_fun_prod J fun b bJ =>
    (hm b bJ).comp (measurable_lifted X H width b)).mul
    (K.crystall X k H.laws.intake (width.symm ▸ H.laws.data.access) Q.table_exists ..)

theorem concur {u v : Air f G} {s t : F.Slice G}
    (A : Borough (X.wrapY s) (Y.wrapY t) Z u v k l R)
    (old : H.unionP p⊆Z) (fresh : ∀ b∈J,zone S X.B b⊆Z) :
    raw (W:=W) K X k p o.a Q.table Q.halo J h (s,u)=
      raw (W:=W) K Y l p o.a Q.table Q.halo J h (t,v) := by
  apply congrArg₂ (·*·)
  · exact Finset.prod_congr rfl fun b bJ =>
      congrArg (h b) (energy_concur A H.laws.data.room b (fresh b bJ))
  exact K.concur (X.wrapY s) k (Y.wrapY t) A H.laws.data.room Q.buys old H.laws.intake

theorem marginal (width : X.width=o.K) (hx : X.manifest) (hy : Y.manifest)
    (hm : ∀ b∈J,Measurable (h b))
    (unit : ∀ b∈J,∀ t∈Set.Icc 0 (linkCap S),‖h b t‖≤1)
    (hv : Village X Y (H.unionP p)) (fresh : ∀ b∈J,zone S X.B b⊆H.unionP p)
    (flags : ∀ i : Site f,S.ratio.parent i∈H.unionP p →
      (i∈Contract.covered R k ↔ i∈Contract.covered R l)) :
    (∫ v,raw (W:=W) K X k p o.a Q.table Q.halo J h v ∂((F.order G).prod X.dice)) =
      ∫ v,raw (W:=W) K Y l p o.a Q.table Q.halo J h v ∂((F.order G).prod Y.dice) := by
  have hyx : Y.x=X.x := hv.weather.symm
  let HY : Cash W Y.x μ L Q o C T R := hyx.symm ▸ H
  rw [integral_prod _ (raw_price K X H width hx k p J h hm unit).1,
    integral_prod _ (raw_price K Y HY (hv.width ▸ width) hy l p J h hm unit).1]
  apply integral_congr_ae
  filter_upwards with a
  let I := podium S G (H.unionP p) X.B
  have hpX := (H.laws.data.localP F X rfl width hx).sails.fullC
  have hpY := (H.laws.data.localP F Y hyx (hv.width ▸ width) hy).sails.fullC
  have same_cov : circuit I X.relating=circuit I Y.relating := by
    ext i j
    exact hv.same_cov H.laws.data.room j.val j.2 i.val
  have target : MeasurePreserving (swim I) Y.dice (arch I X.relating) := by
    rw [arch,same_cov]
    exact orbit hpY.posSemidef I
  let left (u : Air f G) := raw (W:=W) K X k p o.a Q.table Q.halo J h (a,u)
  let right (u : Air f G) := raw (W:=W) K Y l p o.a Q.table Q.halo J h (a,u)
  have ml : Measurable left := (measurable_raw K H J h width hm).comp
    (measurable_const.prodMk measurable_id)
  have mr : Measurable right := (measurable_raw K HY J h (hv.width ▸ width) hm).comp
    (measurable_const.prodMk measurable_id)
  have same (u v) (e : swim I u=swim I v) : left u=right v :=
    concur K H J h ⟨hv.wrap a a (fun _ _ => rfl),(observe I).mp e,flags⟩
      (Finset.Subset.refl _) fresh
  rw [Pond.gathered (spill I) (spill_m I)
    (show MeasurePreserving (swim I) X.dice (arch I X.relating) from orbit hpX.posSemidef I)
    (settled I) (f:=left) (fun u v e => (same u v e).trans (same v v rfl).symm) ml,
    Pond.gathered (spill I) (spill_m I) target (settled I) (f:=right)
      (fun u v e => (same u u rfl).symm.trans (same u v e)) mr]
  exact integral_congr_ae (Eventually.of_forall fun _ => same _ _ rfl)

end YM.Integration.InletSusceptibility.JointTicket
