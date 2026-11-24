import YangMills.WilsonProof.NativeSupport.JointHeld
import YM.MergeProof.TeamWorld

/-! Gauge covariance and the localized held-field law of the original measured ticket. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 25000
noncomputable section
namespace YM.Integration.InletSusceptibility.JointTicket
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.BetaTransport Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations
open SectorMeasure Oriented Work.E03 Mask Contract Work.F03 Presented LabelSum Sector Footprint
open Packets SliceRows Control Window Pulse Coat Matter Itinerary Census Horticulture ProbabilityTheory Poll Pond
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus JointCoat
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P : Teller G} {T : Tube G S}
    {F : Forest S.ratio} {R : Rep G f} {W μ C : ℝ}
    {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W}
variable (M : Team R) (X : Coat T F) (J : Finset (Bond c)) (probe : Bond c→ℝ→ℝ)
open Census Itinerary Art Rotation
variable (H : Cash W X.x μ L Q o C T R) (he : X.width=o.K)
variable (mh : ∀ b∈J,Measurable (probe b)) (unit : ∀ b∈J,∀ t∈Set.Icc 0 (linkCap S),‖probe b t‖≤1)
open Hues
include H he mh in
private theorem rotated (z : Site c→G.El) (good : X.manifest) (k : Finset ℕ) (i : Molecule S) :
    tithe M (X.rinse z) J probe k W o.a Q.table Q.halo i=tithe M X J probe k W o.a Q.table Q.halo i := by
  let Y:=sluice X z
  let g (Z : Coat T F):=raw (W:=W) M Z k i o.a Q.table Q.halo J probe
  have hv : Measurable (g Y):=measurable_raw (X:=Y) (k:=k) (p:=i) M H J probe he mh
  have hA : MeasurePreserving (fun v : F.Slice G × Air f G => (pairs X z v.1,weep X z v.2))
      ((F.order G).prod X.dice) ((F.order G).prod Y.dice) :=
    (drinking X z).prod (speeds X z H.laws.intake.ready (H.laws.data.localP F X rfl he good).sails.fullC
      (H.laws.data.localP F Y rfl he (Cash.wind X z good)).sails.fullC)
  change (∫ v,g Y v ∂((F.order G).prod Y.dice))=_
  rw [← Pond.reception hA _ hv]
  apply integral_congr_ae
  filter_upwards with v
  refine congrArg₂ (·*·) ?_ (M.sparkling (X.wrapY v.1) k H he z v.2 good i)
  apply prod_congr rfl
  intro b _
  apply congrArg (probe b)
  let Z:=X.wrapY v.1
  change energy (sluice Z z) ((sluice Z z).liftA R.beta (weep Z z v.2)) b=energy Z (Z.liftA R.beta v.2) b
  rw [Hues.fullA Z z H.laws.intake.ready (he.symm ▸ H.laws.data.access)]
  exact JointCoat.gauge_eq Z z b _ (funds_branch H.laws.intake.ready)

include H he mh in
theorem held_gauge (s : Molecule S) (v : Site c→G.El) :
    bloom M (X.rinse v) J probe W o.a Q.table Q.halo s=bloom M X J probe W o.a Q.table Q.halo s := by
  unfold bloom
  let U:=planted X s
  simp_rw [show standsIn (X.rinse v) R Q.halo s↔standsIn X R Q.halo s from
    by unfold standsIn claimed rinse; simp only [Coat.B,gauge_flags]]
  split
  next =>
    have hv : (planted (X.rinse v) s)=U.rinse v := by unfold planted preps U rinse; simp only [gauge_flags]; rfl
    rw [hv]
    exact congrArg likely (funext fun j=>rotated M (U.taggedL j) J probe H he mh v (planted_valid X s) _ s)
  rfl

open Greenbelt Merge Merge.Palette
variable {x : ℝ} {ι : Type} (N : ι→Leaf R) (Y : Cash W x μ L Q o C T R) (χ : Chi)
include mh unit in
theorem held_outputs (p : Molecule S) (i : Tickets (Palette.sign N S)) (fresh : ∀ b∈J,zone S (radiusB x) b⊆Y.unionP p) :
    let f:=fun U=>JointTicket.act N Y χ U p i J probe
    UsesFinal (Pressure.temp x) (Y.unionP p) f ∧ GaugeInvariant f ∧ Measurable f := by
  intro f
  let X (u : Greenbelt.Reserve S):=prism T x χ o.K 1 (allot u)
  let g u (V : Config G c):=bloom (team N i) (vary (X u) V) J probe W o.a Q.table Q.halo p
  refine ⟨fun U V hu hp=>congrArg likely (funext fun u=>held_uses (team N i) (X u) J probe Y rfl mh unit p fresh U V hu hp),
    fun z U=>congrArg likely (funext fun u=>held_gauge (team N i) (vary (X u) U) J probe Y rfl mh p z),?_⟩
  exact measurable_const.mul (Finset.measurable_fun_sum _ fun u _=>
    (show Measurable (g u) from held_measurable (team N i) (X u) J probe Y rfl mh unit p))

end YM.Integration.InletSusceptibility.JointTicket
