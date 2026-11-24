import YM.Integration.WilsonInvariantActionSpectatorPrices
import YM.Integration.WilsonInvariantActionCoarseTrace
import YM.Integration.WilsonMatrixTicketLanesReportedAdmission

/-! The enrolled, moving exterior is evaluated as its genuine upper registered field
in the signed two-point covariance of the original run. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionAdmittedPair
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Climb Table Spec PhysMS
open Lattice Wilson RG RG17 Extraction Extraction.Order Next.UVStress Next.Rank.Price
open PhysicalNext.Repeat.Legato Pier.Lair SharpGram.Lenses FVA2 FVA2.Register
open Trace.Pilot Trace.Over TraceExtension Spin OPE OPE.Orbits
open WilsonInvariantActionIntegratedPair WilsonInvariantActionPairMarginals
open WilsonPositionHomogeneousFrame WilsonInvariantActionSpectatorPrices
open private tags recorded use from YM.Integration.WilsonInvariantActionIntegratedPair
open scoped Classical Topology BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (L : Layout F) {U : Filter (ℕ×ℕ)} [U.NeBot] (chosen : U≤L.lens)

private def pair (a b : R.family.label 4) : R.family.book.Vector (fun _:Fin 2=>4) :=
  Fin.cons (α:=fun _:Fin 2=>R.family.label 4) a (fun _=>b)

include F chosen in
private theorem smear {r : ℝ} (live : R.family.ref 4≤L.level r) (a w : R.family.label 4) (φ : Test 2) :
    let b:=S.representative 4 (master L 4 r w)
    Tendsto (fun z:ℕ×ℕ=>smears R.family z.1 z.2 (tags R a (atRef L 4 r z w)) φ-
      smears R.family z.1 z.2 (tags R a b) φ) U (𝓝 0) := by
  intro b
  let v:=locatedRef L 4 r w
  have moving:=tendsRef (L:=L) (D:=4) (r:=r) (v:=fun _=>w) chosen tendsto_const_nhds live
  have every (i : Fin 2) : Tendsto (fun z:ℕ×ℕ=>pair a (atRef L 4 r z w) i) U (𝓝 (pair a v i)) := by
    fin_cases i
    · exact tendsto_const_nhds
    · exact moving
  have m:=calibrated_smear (v:=fun z=>pair a (atRef L 4 r z w)) (x:=pair a v)
    F.room.ordered U (chosen.trans L.certified) φ every
  have s:=calibrated_smear (v:=fun _=>pair a b) (x:=pair a b)
    F.room.ordered U (chosen.trans L.certified) φ (fun _=>tendsto_const_nhds)
  have proj : S.project 4 v=S.project 4 b := (payRef L w).trans (S.rep 4 _).symm
  have eq : S.integralOn (fun _:Fin 2=>4) (pair a v) φ=S.integralOn (fun _:Fin 2=>4) (pair a b) φ := by
    apply φ.apply_eq
    intro x hx
    change S.read x (tags R a v)=S.read x (tags R a b)
    rw [use F _ _ hx,use F _ _ hx,proj]
  simpa only [eq,sub_self] using! m.sub s

include F chosen in
private theorem moving {r : ℝ} (live : R.family.ref 4≤L.level r) (y : S.Field 4)
    (w : R.family.label 4) (φ : Test 2) (cut : (N p:ℕ)→Fin (N+1)) :
    let a:=S.representative 4 y
    let b:=S.representative 4 (master L 4 r w)
    Tendsto (fun z:ℕ×ℕ=>profile R cut a (atRef L 4 r z w) φ z.1 z.2-
      profile R cut a b φ z.1 z.2) U (𝓝 0) := by
  intro a b
  have covered:=chosen.trans L.certified
  have prior:=(along (converge F y)).mono_left covered
  have drift:=(smear F L chosen live a w φ).sub (prior.mul (smear F L chosen live (R.family.refUnit 4) w φ))
  have zero:=drift.congr' (f₂:=fun z:ℕ×ℕ=>profile R cut a (atRef L 4 r z w) φ z.1 z.2-
    profile R cut a b φ z.1 z.2) (by
    filter_upwards [((Cards.largeMesh f).eventually_ge_atTop (R.family.ref 4)).filter_mono covered] with z hz
    rw [recorded R cut a _ φ hz,recorded R cut a b φ hz]
    ring)
  simpa only [mul_zero,sub_zero] using! zero

variable (J : ℝ→tower S) (Z : WilsonPrescription G) {H : (Bel R.family.book).Hierarchy}
    (lead : Leading F J) (paid : ∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (J r) d)
    (simple : G.Simple) {P : ℝ→Spin.change S 4} {δ g : ℝ→ℝ} (same : ∀ᶠr in trail,J r 4=P r)
    (cal : TendC F P δ) (coupling : Coupling G g)
    {u : Filter (ℕ×ℕ)} (B : Mantle F u) (E : Services R.family f S) (pegs : Pegs B L)
    (near : ∀ᶠr in trail,R.family.S.a (L.level r)≤r ∧
      r≤R.family.S.a (L.level r)*R.family.path.levels.clock.hatBeta (L.level r)^2)

include F chosen lead paid simple same cal coupling E pegs near in
theorem original (q : ℕ) {ε : ℝ} (he : 0<ε) :
    ∃e:ℕ,∀ᶠr in trail,∀hr:0<r,∀v:RG17.Free R.family 4,∃w:R.family.label 4,
      master L 4 r w=homogeneous F J Z r 4 v ∧
      (∀N p,L.level r≤N→quota R.family 4 (L.level r) N p (atRef L 4 r (N,p) w)≤
        R.family.S.a (L.level r)^4 * (R.family.path.levels.clock.hatBeta (L.level r)^e *
          ‖freeInput F J Z 4 r v‖)) ∧
      ∀ (φ : Test 2) (cut : (N p:ℕ)→Fin (N+1)),
        let t:=dilate hr φ
        let original:=profile R cut (S.representative 4 (J r 4 (stepField R.family)))
          (S.representative 4 (homogeneous F J Z r 4 v)) t
        ∀ᶠz in U,‖original z.1 z.2-((r^4/(4*δ r):ℝ):ℂ)*
          profile R cut (S.representative 4 (center F)) (atRef L 4 r z w) t z.1 z.2‖≤ε*(g r)^q := by
  obtain ⟨e,market⟩:=WilsonReportingMeasuredTender.entry B E
    (WilsonReportingMeasuredAdmission.present F J lead paid) pegs near 4
  refine ⟨e,?_⟩
  filter_upwards [market,pegs.level.growing.eventually_ge_atTop (R.family.ref 4),
    WilsonInvariantActionPairCovariance.charged F J simple same cal coupling,coupling.positive]
    with r bought live ward gr
  intro hr v
  obtain ⟨w,cost,name⟩:=bought (freeInput F J Z 4 r v)
  refine ⟨w,name,fun N p hN=>?_,?_⟩
  · rw [WilsonMatrixTicketLanesReportedAdmission.quota R F L 4 r w live N p hN]
    exact mul_le_mul_of_nonneg_left cost (pow_nonneg (R.family.S.a_pos _).le _)
  intro φ cut t original
  let b:=homogeneous F J Z r 4 v
  let a:=S.representative 4 (center F)
  let C:ℂ:=((r^4/(4*δ r):ℝ):ℂ)
  have base:=(along (WilsonInvariantActionIntegratedPair.ordered F cut φ hr (center F) b)).mono_left (chosen.trans L.certified)
  have prev:=moving F L chosen live (center F) w t cut
  rw [show master L 4 r w=b from name] at prev
  have top:=(along (WilsonInvariantActionIntegratedPair.ordered F cut φ hr (J r 4 (stepField R.family)) b)).mono_left (chosen.trans L.certified)
  have cv : Tendsto (fun z:ℕ×ℕ=>profile R cut a (atRef L 4 r z w) t z.1 z.2) U
      (𝓝 (WilsonInvariantActionPairCovariance.tested (center F) b r φ)) := by
    simpa only [t,sub_add_cancel,zero_add] using! prev.add base
  have scalar : Tendsto (fun _:ℕ×ℕ=>C) U (𝓝 C):=tendsto_const_nhds
  have diff:=top.sub (scalar.mul cv)
  have zero : Tendsto (fun z:ℕ×ℕ=>original z.1 z.2-C*profile R cut a (atRef L 4 r z w) t z.1 z.2) U (𝓝 0) := by
    simpa only [C,ward b φ,sub_self] using! diff
  filter_upwards [Metric.tendsto_nhds.mp zero (ε*(g r)^q) (mul_pos he (pow_pos gr _))] with z hz
  simpa only [dist_zero_right] using hz.le

end YM.Integration.WilsonInvariantActionAdmittedPair
