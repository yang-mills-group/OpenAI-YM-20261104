import YM.Integration.WilsonPositionProgramTrialPublicJointPivotMeshStock
import YM.Integration.WilsonOriginalObservedRoseBornGalopNodes
import YM.Integration.WilsonMaxwellThermometerPublicPlacedIncome

/-! The timed connected coefficient at the actual reported site on the original volume schedule. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicJointPivotMeshAddress
open Function Set Filter Finset Metric Lattice RG Wilson Source Extraction MeasureTheory PowerSeries
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1 XSpace.Rose XSpace.Cirrus XSpace.Photo
open PhysicalNext.Repeat.Legato RG17 Spec Table OPE OPE.Orbits Climb PhysMS Trace.Pilot
open MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open WilsonMaxwellThermometerShiftedPanel (translated shift accepted location)
open WilsonMaxwellThermometerPublicStation (aperture granted)
open WilsonMaxwellThermometerPublicPlacedIncome (atParent)
open WilsonSeparatedOriginalThermometerDetectorMesh (chart)
open WilsonPositionProgramTrialPublicJointPivotSeries (signed)
open WilsonPositionProgramTrialPublicJointPivotMesh (measured)
open scoped Classical Topology BigOperators
variable {G : Gauge} (Z : WilsonPrescription G) {hG : G.Simple} (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ : Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match Z hG M σ dial) (ν : ℝ)

theorem neighborhood (A : Sample 3 → ℂ) (B : Points 3 → ℂ) (h : Senses (conf 3) A B)
    (K : Set (Points 3)) (compact : IsCompact K) (separated : K ⊆ conf 3) {ε : ℝ} (positive : 0<ε) :
    ∀ᶠ m in Front, ∀ x∈K, ∀ v : pack 3, dist (Extraction.tag m.spacing v) x ≤ 24*m.spacing →
      dist (A (translated m v)) (B x) ≤ ε := by
  choose radius pos fee using fun x : K => sensesU h x.val (separated x.property) (ε/2) (half_pos positive)
  let balls (x : K) := ball x.val (radius x/2)
  obtain ⟨u,cover⟩ := compact.elim_finite_subcover balls (fun _=>isOpen_ball)
    (fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,mem_ball_self (half_pos (pos _))⟩)
  have shrink (k : K) : ∀ᶠ m in Front,(24:ℝ)*m.spacing<radius k/2 := by
    have t := frontier.endpt.const_mul (24:ℝ)
    rw [mul_zero] at t
    exact t.eventually (gt_mem_nhds (half_pos (pos k)))
  filter_upwards [accepted,(eventually_all_finset u).mpr (fun k _=>(fee k).and (shrink k))] with m admit pay x hx v hv
  obtain ⟨k,hxk⟩ := mem_iUnion.mp (cover hx)
  obtain ⟨within,inside⟩ := mem_iUnion.mp hxk
  have hk := pay k within
  have close : dist x k.val < radius k/2 := inside
  refine (dist_triangle _ (B k.val) _).trans ?_
  apply le_trans (add_le_add ?_ ?_) ((add_halves ε).le)
  · apply le_of_lt (hk.1 _ _ admit ?_)
    change dist (familiar (translated m v)) k.val < radius k
    rw [location]
    exact (dist_triangle _ x _).trans_lt (by linarith [hv,close,hk.2])
  · rw [dist_comm]
    exact senses_price h k.val (radius k) (pos k) _ (fee k) x (separated hx) (close.trans (half_lt_self (pos k)))

theorem periodic (d : ℕ) (m : Mesh) (v w : pack 3)
    (eq : wrap m.p.side ∘ v = wrap m.p.side ∘ w) :
    Rose.measureₓ Z.scheme Z.criterion d (translated m v) = Rose.measureₓ Z.scheme Z.criterion d (translated m w) := by
  have address : chartV (translated m v) = chartV (translated m w) := by
    funext i
    have h := congrFun eq i
    change wrap m.p.side (v i+shift m)=wrap m.p.side (w i+shift m)
    simpa only [map_add,Function.comp_apply] using congrArg (· +wrap m.p.side (shift m)) h
  change Rose.turn Z.scheme Z.criterion m (Rose.cooked Z.scheme Z.store d (translated m v)) =
    Rose.turn Z.scheme Z.criterion m (Rose.cooked Z.scheme Z.store d (translated m w))
  apply congrArg
  funext k
  unfold Rose.cooked XSpace.Cirrus.live
  simp only [address]
  rfl

include H ν in
theorem original (R : Run G) (o : Extraction.Order) (U : Filter (ℕ×ℕ)) (prior : U≤o.fuse)
    (s : ℝ→ℕ) (small : Tendsto (aperture R s) trail (𝓝 0)) (d k : ℕ) (p : Fin 3→Sec G d)
    (K : Set (Points 3)) (hc : IsCompact K) (hs : K ⊆ conf 3) {ε : ℝ} (ep : 0<ε) :
    ∀ᶠ w : ℝ×(ℕ×ℕ) in trail.curry U, ∀ (N : ℕ) (live : s w.1≤N), ∀ x∈K,
      ‖coeff k (signed (Rose.measureₓ Z.scheme Z.criterion d (atParent R s w.1 N w.2.2 live x)) p) -
        coeff k (signed (Jury.fxt (Measure.start Z.scheme Z.criterion d) x) p)‖ ≤ ε := by
  have geo := WilsonSeparatedOriginalThermometerDetectorMesh.reporting R trail o U prior s _ (granted R s) small
  have radii : Tendsto (Prod.fst : ℝ×(ℕ×ℕ) → ℝ) (trail.curry U) trail := tendsto_fst.mono_left curry_le_prod
  have menu := neighborhood _ _ (measured Z M H ν d k p) K hc hs ep
  filter_upwards [geo.eventually menu,radii.eventually (self_mem_nhdsWithin (s:=Ioi (0:ℝ)))] with w paid rp
  obtain ⟨r,χ,per⟩ := w
  intro N live x hx
  obtain ⟨v,sites,near⟩ := WilsonMaxwellThermometerParentLift.parents R.family.S live per rp x
  let m := chart R (s r) per (aperture R s r) (granted R s r)
  rw [atParent,periodic Z d m _ v (by refine Eq.trans ?_ sites.symm; funext i; exact wrap_lift _)]
  simpa only [dist_eq_norm] using paid x hx v (by simpa only [m,chart,aperture,if_pos (show 0<r from rp)] using near)

end YM.Integration.WilsonPositionProgramTrialPublicJointPivotMeshAddress
