import YM.Integration.SharedIntrinsicWilsonGrid
import YM.Integration.WilsonExteriorReplicaCapture

/-! The full prescribed moving-frame product and its single intrinsic
Wilson counterterm occupy one reflection cell.  Each macroscopic exterior
is charged on its own tiling.  The alternating copies are taken *after*
the finite grade sum, in the same Wilson measure. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedPhysicalCopies
open Function Filter Lattice Wilson RG Cells Extraction OPE OPE.Orbits OPE.Cards OPE.Log
open Frontier6.Road Trace.Pilot Trace.Physical.GermGraph RG16.Literal
open FilteredIntrinsicGramReadout FilteredWilsonProduct IntrinsicPhysicalCell
open SharedIntrinsicWilsonGrid WilsonExteriorReplicaCapture
open scoped Classical BigOperators Topology
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
variable {I : Type} [Fintype I] {d : I → ℕ} {D : ℕ}

def gap (F : Spec.Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (v : (i : I) → (Climb.Bel C.book).Field (d i))
    (r : ℝ) (b j : ℕ) (x : I → Cover) (w : ℕ × ℕ) : Config G (C.side w.1 w.2) → ℂ :=
  let Y := field F Q J v r j x w
  Y-C.O w.1 w.2 (IntrinsicProductCompactness.value (D:=D) F.room.cutoff b w Y) 0

private theorem assembled (F : Spec.Final C f S)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (v : (i : I) → (Climb.Bel C.book).Field (d i))
    (r : ℝ) (b j : ℕ) (x : I → Cover) (w : ℕ × ℕ) (a : Grades d → ℝ)
    (pay : ∀ g : Grades d, Observed F.room.cutoff b j D x (component F Q J v g r) w (a g)) :
    PaidAt C.S w.1 w.2 b (C.beta w.1 w.2) (∑ g, a g) (gap (D:=D) F Q J v r b j x w) := by
  obtain ⟨ho,hn,_⟩ := pay (fun _ => 0)
  let W := center C.S w.2 hn 0
  let Y g := leaves C j (levels g) x (component F Q J v g r) w.1 w.2
  let Z g := IntrinsicProductCompactness.value (D:=D) F.room.cutoff b w (Y g)
  let err g := Y g-C.O w.1 w.2 (Z g) 0
  have pieces (g : Grades d) :
      Booked C w.1 w.2 D (Y g) b hn ∧ Interior (W.chamber 0) (err g) ∧
        W.rootTest (C.beta w.1 w.2) (err g) ≤ a g := by
    obtain ⟨_,_,book,_,_⟩ := pay g
    exact ⟨book,(discrepancy_paid (pay g)).ticket,(discrepancy_paid (pay g)).mark⟩
  have cont (g : Grades d) : Continuous (Y g) := by
    have showFn : Y g = fun U => ∏ i,C.O w.1 w.2 (component F Q J v g r i)
        (location C.S j w.1 w.2 (x i)) U := funext fun U => Finset.prod_apply ..
    rw [showFn]
    exact continuous_finsetProd _ (fun _ _ => C.continuousO ..)
  have captured := IntrinsicProductLinearity.booked_sum C w.1 w.2 D b F.room.cutoff ho hn
    (fun _ : Grades d => (1:ℂ)) Y cont (fun g => (pieces g).1)
  simp only [one_smul] at captured
  have sumfield : field F Q J v r j x w=∑ g,Y g := field_expansion F Q J v r j x w
  have sumlabel : IntrinsicProductCompactness.value (D:=D) F.room.cutoff b w (field F Q J v r j x w) =
      ∑ g, Z g := by
    simp only [Z,IntrinsicProductCompactness.value_eq F.room.cutoff ho hn, label, sumfield,captured.2,map_sum]
  have total : gap (D:=D) F Q J v r b j x w = ∑ g, err g := by
    dsimp only [gap]
    rw [sumlabel,sumfield]
    have mapped : C.O w.1 w.2 (∑ g,Z g) 0 = ∑ g,C.O w.1 w.2 (Z g) 0 :=
      map_sum ((C.linearO w.1 w.2 D 0).mk' _) _ _
    rw [mapped,← Finset.sum_sub_distrib]
  have bound := Next.UVStress.root_sum W (C.beta w.1 w.2) Finset.univ err
    (fun _ => (1:ℂ)) (fun g _ => (pieces g).2.1) (seamless F.room.cutoff w.1 w.2)
  simp only [one_smul,norm_one,one_mul] at bound
  rw [total]
  exact ⟨hn,bound.1,bound.2.trans (Finset.sum_le_sum fun g _ => (pieces g).2.2)⟩

/-- One previously selected physical grid and one actual counterterm of
the full product, at every allowed cutoff of the fused regulator tail. -/
theorem purchased (F : Spec.Final C f S) (facility : Facilities C f S) (anchor : I)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (P : Plan C D (Fintype.card I) (∑ i,d i))
    (J : ℝ → PhysMS.tower S) (H : PhysMS.Leading F J)
    (v : (i : I) → (Climb.Bel C.book).Field (d i)) :
    ∃ fee : ℝ → ℝ, RateLE trail LogV fee (-(D:ℝ)-1/32) ∧
      (∀ k : ℕ, Tendsto (fun r => C.path.levels.clock.hatBeta (P.j r)^k *
        (Real.exp ((D:ℝ)*LogV r) * fee r)) trail (𝓝 0)) ∧
      ∀ᶠ r in trail, ∀ x : I → Cover, Plot C (P.b r) (P.middle r) (P.j r) x →
        ∀ᶠ w in f.fuse, PaidAt C.S w.1 w.2 (P.b r) (C.beta w.1 w.2) (fee r)
          (gap (D:=D) F Q J v r (P.b r) (P.j r) x w) := by
  have margin (g : Grades d) : Margin D (Fintype.card I) (∑ i,levels g i) P.h P.a P.c := by
    have count : ∑ i,levels g i ≤ ∑ i,d i := Finset.sum_le_sum (fun i _ => Nat.le_of_lt_succ (g i).isLt)
    have weighted := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr count : ((∑ i,levels g i : ℕ):ℝ) ≤ _)
      (sub_nonneg.mpr P.high.le)
    have full := P.margin
    dsimp only [Margin] at full ⊢
    linarith only [full,weighted]
  choose a rates pays using fun g : Grades d =>
    FilteredIntrinsicGramReadout.on_grid F facility anchor D P.coarse P.mid P.fine P.pos P.before P.low P.high
      (margin g) (component F Q J v g) (component_rate F Q J H v g)
  let fee r := ∑ g : Grades d, ‖a g r‖
  have rate : RateLE trail LogV fee (-(D:ℝ)-1/32) := RateLE.sum PhysMS.to_log_zoom (fun g _ => (rates g).norm)
  refine ⟨fee,rate,MultilinearCellCapture.all_loop_orders PhysMS.to_log_zoom D fee rate P.fine,?_⟩
  filter_upwards [eventually_all.mpr pays] with r now
  intro x plot
  filter_upwards [eventually_all.mpr (fun g => now g x plot)] with w bought
  exact assembled F Q J v r (P.b r) (P.j r) x w (fun g => ‖a g r‖)
    (fun g => (bought g).weaken (Real.le_norm_self _))

/-- Preselect the scalar allowance before the exterior, its bounded
physical labels, the replica count and the regulator.  The left side
contains alternating copies of the full sum, including every mixed term. -/
theorem exterior (F : Spec.Final C f S) (facility : Facilities C f S) (anchor : I)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (P : Plan C D (Fintype.card I) (∑ i,d i)) (J : ℝ → PhysMS.tower S)
    (H : PhysMS.Leading F J) (v : (i : I) → (Climb.Bel C.book).Field (d i)) :
    ∃ fee : ℝ → ℝ, RateLE trail LogV fee (-(D:ℝ)-1/32) ∧
      (∀ k : ℕ, Tendsto (fun r => C.path.levels.clock.hatBeta (P.j r)^k *
        (Real.exp ((D:ℝ)*LogV r) * fee r)) trail (𝓝 0)) ∧
      ∀ (E : Type) [Fintype E] (y : E → E4), Injective (Sum.elim (fun _ : Unit => (0:E4)) y) →
      ∀ (de : E → ℕ) (R : E → ℝ), (∀ i, 0<R i) → ∀ δ : ℝ, 0<δ →
      ∃ o n : ℕ, ∃ A : E → ℝ, (∀ i,0≤A i) ∧ ∀ᶠ r in trail, ∀ x : I → Cover,
        Plot C (P.b r) (P.middle r) (P.j r) x → ∀ copies : ℕ, ∀ᶠ t : ℕ in atTop,
        ∀ᶠ w in f.fuse, ∀ e : (i:E) → C.label (de i), (∀ i,‖e i‖≤R i) →
        ‖reading C w o t copies y (gap (D:=D) F Q J v r (P.b r) (P.j r) x w) de e‖ ≤
          (fee r * ∏ i, (A i*C.S.a n^(-(de i:ℝ)-δ)+1))^(2*copies) := by
  obtain ⟨fee,rate,orders,price⟩ := purchased F facility anchor Q P J H v
  refine ⟨fee,rate,orders,?_⟩
  intro E _ y sep de R hR δ hδ
  obtain ⟨n₀,A,hA,ext⟩ := ActualFoundryDetectorSource.exterior_bounds F de R hR δ hδ
  obtain ⟨o,_,q,_,n,hn,_,_,space⟩ :=
    WilsonMixedPlacement.placements (C:=C) f (fun _ : Unit => (0:E4)) y sep 0 0 n₀
  refine ⟨o,n,A,hA,?_⟩
  filter_upwards [price,P.coarse.grows.eventually_ge_atTop q] with r center later
  intro x plot copies
  filter_upwards [space (2*copies)] with t train
  filter_upwards [train,center x plot,ext n ((le_max_right q n₀).trans hn) 1 one_pos] with w fits paid bank
  obtain ⟨positions⟩ := fits
  intro e he
  exact placed F.room.cutoff positions later _ paid de e (bank e he)

end YM.Integration.WilsonSeparatedPhysicalCopies
