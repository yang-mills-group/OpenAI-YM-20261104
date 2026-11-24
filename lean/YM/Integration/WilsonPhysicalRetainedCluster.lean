import YM.Integration.WilsonPhysicalRetainedReport
import YM.Integration.WilsonVariablePhysicalCluster
import YM.Integration.IntrinsicPhysicalCell

/-! The measured continuum cluster is read by the same genuinely
retained, summed cutoff label from which the signed finite comparison
starts. The spatial price is chosen before its original regulator tail. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalRetainedCluster
open Function Filter Real MeasureTheory Lattice Wilson RG Cells OPE OPE.Orbits OPE.Cards
open Source Labels Trace.Pilot Trace.Physical Trace.Physical.GermGraph Work.G08 RG16.Literal
open StressFlux.Matching Frontier6.Road EngineeringWeightedReadout WilsonWholeLimit
open MultilinearCellCapture FilteredIntrinsicGramReadout FilteredWilsonProduct SharedIntrinsicWilsonGrid
open PhysicalNext.Repeat.Legato IntrinsicPhysicalCell ContinuumIntrinsicWilsonProduct
open scoped Classical Topology BigOperators
variable {G : Gauge} (R : Run G) {S : Table R.family.book} {f : Extraction.Order}
variable {I : Type} [Fintype I] {d : I → ℕ} {D : ℕ}

abbrev Retained (D : ℕ) := (g : Grades d) → ℝ → (I → Cover) → Indices R.family (levels g) →
  (ℕ×ℕ) → R.family.label D

def basket (Z : Retained (d:=d) R D) (F : Spec.Final R.family f S)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (v : (k : I) → (Climb.Bel R.family.book).Field (d k))
    (t : ℝ) (x : I → Cover) (w : ℕ×ℕ) : R.family.label D :=
  ∑ g : Grades d, ∑ a, weight (component F Q J v g t) a • Z g t x a w

theorem all_inputs (hG : G.Simple) (F : Spec.Final R.family f S) (fac : Facilities R.family f S)
    (anchor : I) (P : Plan R.family D (Fintype.card I) (∑ i,d i)) :
    ∃ Z : Retained (d:=d) R D, ∀ (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
      (J : ℝ → PhysMS.tower S), PhysMS.Leading F J → ∀ A : ℝ, ∀ᶠ t in trail,
      ∀ x : I → Cover, Plot R.family (P.b t) (P.middle t) (P.j t) x →
      (∀ᶠ w in f.fuse, ∀ v : (k : I) → (Climb.Bel R.family.book).Field (d k),
        ‖IntrinsicProductCompactness.value (D:=D) F.room.cutoff (P.b t) w (field F Q J v t (P.j t) x w) -
          basket R Z F Q J v t x w‖ ≤ exp (-A*LogV t)*(∏ k,‖v k‖)) ∧
      ∀ v : (k : I) → (Climb.Bel R.family.book).Field (d k),
        let actual := fun w => IntrinsicProductCompactness.value (D:=D) F.room.cutoff (P.b t) w (field F Q J v t (P.j t) x w)
        let kept := basket R Z F Q J v t x
        (∃ z : R.family.label D, Cluster F Q J v t (P.b t) (P.j t) x z) ∧
        ∀ z : R.family.label D, Cluster F Q J v t (P.b t) (P.j t) x z →
          ∃ l : Filter (ℕ×ℕ), l.NeBot ∧ l≤f.fuse ∧ Tendsto actual l (𝓝 z) ∧
            ∀ ε>0, ∀ᶠ w in l, ‖kept w-z‖ ≤ exp (-A*LogV t)*(∏ k,‖v k‖)+ε := by
  obtain ⟨Z,rows⟩ := WilsonPhysicalRetainedReport.all_inputs (d:=d) R hG F fac anchor P
  refine ⟨Z,?_⟩
  intro Q J H A
  let mult := (D:ℝ)*P.h+1
  have floor := (chart_rate (C:=R.family) PhysMS.to_log_zoom D P.coarse).pays PhysMS.to_log_zoom
  have finance := (RateIs.exp mult PhysMS.to_log_zoom).outweigh floor (by dsimp [mult]; linarith) PhysMS.to_log_zoom
  filter_upwards [rows Q J H (A+mult),finance,WilsonVariablePhysicalCluster.all_inputs F fac anchor Q J P,
    P.coarse.earlier (P.before.trans (P.low.trans P.high)) PhysMS.to_log_zoom P.fine]
    with t retained cashier clusters order
  intro x plot
  let actual := fun (v : (i : I) → (Climb.Bel R.family.book).Field (d i)) (w : ℕ×ℕ) =>
    IntrinsicProductCompactness.value (D:=D) F.room.cutoff (P.b t) w (field F Q J v t (P.j t) x w)
  let kept := fun v => basket R Z F Q J v t x
  have cash : chart R.family D (P.b t) ≤ exp (mult*LogV t) := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (chart_nonneg (C:=R.family) D (P.b t))] using cashier
  have closeness : ∀ᶠ w in f.fuse, ∀ v, ‖actual v w-kept v w‖ ≤ exp (-A*LogV t)*(∏ k,‖v k‖) := by
    filter_upwards [retained x plot] with w paid
    intro v
    obtain ⟨ho,live,_,cost⟩ := paid v
    let Y := field F Q J v t (P.j t) x w
    let key := topReport R.family w.1 w.2 D R.makes (P.b t) ho live Y
    let out := (R.family.factory D w.1 w.2).terminal
    have physical : actual v w = out key := IntrinsicProductCompactness.value_eq F.room.cutoff ho live Y
    have vn : 0 ≤ ∏ k,‖v k‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
    calc
      _ = ‖out (key-out.symm (kept v w))‖ := by rw [physical,map_sub,out.apply_symm_apply]
      _ ≤ chart R.family D (P.b t)*mCost R.family D w.1 w.2 (P.b t) (key-out.symm (kept v w)) :=
        terminal_cost fac R.makes D w.1 w.2 _ ho live _
      _ ≤ chart R.family D (P.b t)*(exp (-(A+mult)*LogV t)*(∏ k,‖v k‖)) :=
        mul_le_mul_of_nonneg_left (cost (P.b t) le_rfl order.le live) (chart_nonneg ..)
      _ ≤ exp (mult*LogV t)*(exp (-(A+mult)*LogV t)*(∏ k,‖v k‖)) :=
        mul_le_mul_of_nonneg_right cash (mul_nonneg (exp_pos _).le vn)
      _ = exp (-A*LogV t)*(∏ k,‖v k‖) := by rw [←mul_assoc,←exp_add]; exact congrArg (fun a : ℝ => exp a*(∏ k,‖v k‖)) (by ring)
  refine ⟨closeness,?_⟩
  intro v
  refine ⟨clusters v x plot,?_⟩
  intro z chosen
  obtain ⟨l,nb,sub,conv⟩ := chosen
  refine ⟨l,nb,sub,conv,?_⟩
  intro ε pos
  filter_upwards [closeness.filter_mono sub,(Metric.tendsto_nhds.1 conv) ε pos] with w nearby tends
  have triangle : ‖kept v w-z‖ ≤ ‖kept v w-actual v w‖+‖actual v w-z‖ := by
    simpa only [dist_eq_norm] using dist_triangle (kept v w) (actual v w) z
  exact triangle.trans (add_le_add ((norm_sub_rev _ _).le.trans (nearby v)) (by simpa only [dist_eq_norm] using tends.le))

theorem original (hG : G.Simple) (F : Spec.Final R.family f S) (fac : Facilities R.family f S)
    (anchor : I) (P : Plan R.family D (Fintype.card I) (∑ i,d i)) :
    ∃ Z : Retained (d:=d) R D, ∀ (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
      (J : ℝ → PhysMS.tower S), PhysMS.Leading F J → ∀ (v : (k : I) → (Climb.Bel R.family.book).Field (d k)) (A : ℝ),
    ∀ᶠ t in trail, ∀ x : I → Cover, Plot R.family (P.b t) (P.middle t) (P.j t) x →
      let actual := fun w => IntrinsicProductCompactness.value (D:=D) F.room.cutoff (P.b t) w (field F Q J v t (P.j t) x w)
      let kept := basket R Z F Q J v t x
      (∀ᶠ w in f.fuse, ‖actual w-kept w‖ ≤ exp (-A*LogV t)) ∧
      (∃ z : R.family.label D, Cluster F Q J v t (P.b t) (P.j t) x z) ∧
      ∀ z : R.family.label D, Cluster F Q J v t (P.b t) (P.j t) x z →
        ∃ l : Filter (ℕ×ℕ), l.NeBot ∧ l≤f.fuse ∧ Tendsto actual l (𝓝 z) ∧
          ∀ ε>0, ∀ᶠ w in l, ‖kept w-z‖ ≤ exp (-A*LogV t)+ε := by
  obtain ⟨Z,bank⟩ := all_inputs (d:=d) R hG F fac anchor P
  refine ⟨Z,?_⟩
  intro Q J H v A
  have charge := (Real.tendsto_exp_atTop.comp PhysMS.to_log_zoom).eventually_ge_atTop (∏ k,‖v k‖)
  filter_upwards [bank Q J H (A+1),charge] with t booked rate
  intro x plot
  have absorbs : exp (-(A+1)*LogV t)*(∏ k,‖v k‖) ≤ exp (-A*LogV t) := calc
    _ ≤ exp (-(A+1)*LogV t)*exp (LogV t) := mul_le_mul_of_nonneg_left rate (exp_pos _).le
    _ = exp (-A*LogV t) := by rw [←exp_add]; exact congrArg exp (by ring)
  obtain ⟨finite,clusters⟩ := booked x plot
  obtain ⟨born,limit⟩ := clusters v
  refine ⟨finite.mono fun w done => (done v).trans absorbs,born,?_⟩
  intro z original
  obtain ⟨l,nb,sub,conv,near⟩ := limit z original
  exact ⟨l,nb,sub,conv,fun ε pos => (near ε pos).mono fun w bill => bill.trans (add_le_add absorbs le_rfl)⟩

end YM.Integration.WilsonPhysicalRetainedCluster
