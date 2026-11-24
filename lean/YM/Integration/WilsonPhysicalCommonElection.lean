import YM.Integration.WilsonOriginalAllOrderAcceptance
import YM.Integration.WilsonViewerElectedHierarchy
import YM.Integration.WilsonViewerGridPins

/-! One original archive and funded hierarchy, with a linear assembly of heterogeneous
cutoff columns whose quota and reflected bills hold before the ordered limits. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
universe u
namespace YM.Integration.WilsonPhysicalCommonElection
open Filter Table Spec Extraction Climb Lattice PhysMS Trace.Pilot OPE OPE.Orbits
open PhysicalNext.Repeat.Legato WilsonLimitConstruction
open GapsContact.Ascent GapsContact.Seams WilsonViewerElectedHierarchy WilsonViewerGridPins
open WilsonOriginalAllOrderCourse
open scoped Classical Topology
variable {G : Gauge} {R : Run G} {T : Campaign R} {W : Campaign.Pillars R T}
variable {f : Extraction.Order} {S : Table R.family.book} {F : Final R.family f S}
  {Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}
  {L : EveryPhase.Almanac F} {J : ℝ → tower S} {Y : (Bel R.family.book).Hierarchy}
  {arch : Trace.Terrace.Arch R.family} {ℓ : Ultrafilter (ℕ × ℕ)} {simple : G.Simple}
  {cohort : Ultrafilter (ℕ × ℕ) → Prop}

/-- The genuine cutoff fields form one linear map per grade. On each complete finite
roster the fields share the same period-then-cutoff opening, including all proper faces. -/
def Ordered (F : Final R.family f S) (ℓ : Ultrafilter (ℕ × ℕ))
    (r : ℝ) (j m D : ℕ) (b : ℝ) : Prop :=
  ∃ A : Maps R.family S D,
    (∀ (d : Fin (D+1)) (v : S.Field d),
      S.project d (A.limit d v) = v ∧
      Tendsto (fun z => A.field d z v) (ℓ : Filter (ℕ × ℕ)) (𝓝 (A.limit d v)) ∧
      ∀ N per, j < N → Next.UVStress.quota R.family d j N per (A.field d (N,per) v) ≤
        R.family.S.a j^d.val * b * cost F d r v) ∧
    ∀ (n : ℕ) (d : Fin n → Fin (D+1)) (v : (i : Fin n) → S.Field (d i)),
      f.late fun N per => ∀ (i : Fin n),
        Next.UVStress.quota R.family (d i) j N per (A.field (d i) (N,per) (v i)) ≤
          R.family.S.a j^(d i).val * b * cost F (d i) r (v i) ∧
        Cards.PaidAt R.family.S N per m (R.family.beta N per) (b * cost F (d i) r (v i))
          (R.family.O N per (A.field (d i) (N,per) (v i)) 0)

theorem before_limits (run : Selected.{u} F L Q J Y arch ℓ simple cohort) (D : ℕ) :
    ∃ t : ℕ, ∀ᶠ r in trail, ∃ j m, m ≤ j ∧ r < dock r^t * R.family.S.a j ∧
      R.family.S.a m < r*dock r^t ∧ Ordered F ℓ r j m D (dock r^t) := by
  classical
  obtain ⟨t,date⟩ := WilsonThermometerUnitFilingFourPool.original F simple run.bliss D
  refine ⟨t,?_⟩
  filter_upwards [date] with r receipt
  obtain ⟨j,m,h⟩ := receipt
  choose b w represents converges money using fun d : Fin (D+1) =>
    WilsonViewerReportingGrid.labels F (h.budget d (Nat.le_of_lt_succ d.isLt))
  let A : Maps R.family S D := ⟨b,w⟩
  refine ⟨j,m,h.fore,h.breadth,h.front,A,?_,?_⟩
  · exact fun d v => ⟨represents d v,converges d v,(money d v).1⟩
  · intro n d v
    have mesh : ∀ᶠ z : ℕ × ℕ in f.fuse, j < z.1 := by
      rw [Extraction.Order.fused,Extraction.Order.late]
      exact Eventually.of_forall fun _ => f.mesh.cofinal.eventually (eventually_gt_atTop j)
    let atCut (z : ℕ × ℕ) : Prop := ∀ (i : Fin n),
        Next.UVStress.quota R.family (d i) j z.1 z.2 (A.field (d i) z (v i)) ≤
          R.family.S.a j^(d i).val * (dock r^t) * cost F (d i) r (v i) ∧
        Cards.PaidAt R.family.S z.1 z.2 m (R.family.beta z.1 z.2) ((dock r^t) * cost F (d i) r (v i))
          (R.family.O z.1 z.2 (A.field (d i) z (v i)) 0)
    have joint : ∀ᶠ z in f.fuse, atCut z := by
      filter_upwards [mesh,eventually_all.mpr fun i => (money (d i) (v i)).2] with z hz bound i
      exact ⟨(money (d i) (v i)).1 z.1 z.2 hz,bound i⟩
    exact (Extraction.Order.fused f atCut).mp joint

/-- Recover the campaign financing without electing a second Run, hierarchy or extraction. -/
theorem finances {a : Axis} {ε : ℝ} {s : WilsonOriginalAllOrderCourse.Schedule G} (cash : Paid.{u} a simple ε s R T W) :
    FundedOriginalProperties.{u} simple ε W ∧ WilsonWindowReportingPace.Slow R.kit ∧
    NativeFVAPlateau.Correlations R := by
  obtain ⟨_,_,_,_,_,_,_,slow,_,_,physical,finance,_⟩ := cash.originalSchool
  exact ⟨finance,slow,physical⟩

/-- Choose the physical construction first. Horizon, all finite physical rosters, perturbative
tests and target coefficients can subsequently be specified on this same Final. -/
theorem original (a : Axis) (hG : G.Simple) {ε : ℝ} (hp : 0 < ε) (s : WilsonOriginalAllOrderCourse.Schedule G)
    (cohort : Ultrafilter (ℕ × ℕ) → Prop)
    (admit : ∀ (f : Extraction.Order) (l : Ultrafilter (ℕ × ℕ)), (l : Filter _) ≤ f.fuse → cohort l)
    (v : Extraction.Order) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T), Paid.{u} a hG ε s R T W ∧
    ∃ (w : Extraction.Order) (S : Table R.family.book) (F : Final R.family (v.refine w) S)
      (L : EveryPhase.Almanac F) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
      (J : ℝ → tower S) (Y : (Bel R.family.book).Hierarchy) (arch : Trace.Terrace.Arch R.family)
      (ℓ : Ultrafilter (ℕ × ℕ)), Selected.{u} F L Q J Y arch ℓ hG cohort ∧
      ∀ D, ∃ t : ℕ, ∀ᶠ r in trail, ∃ j m, m ≤ j ∧ r < dock r^t * R.family.S.a j ∧
        R.family.S.a m < r*dock r^t ∧ Ordered F ℓ r j m D (dock r^t) := by
  obtain ⟨R,T,W,cash⟩ := WilsonOriginalAllOrderCourse.original.{u} a hG hp s
  obtain ⟨w,S,F,L,Q,Y,arch,ℓ,bliss,T₀,T₁,J,φ,c,d,e,complete,trace,exclusion,fac,foundation,
    sharp,grade,scheme,comparison,leading,obedient,under,approved,ticket,_⟩ := cash.physical cohort admit v
  have selected : Selected.{u} F L Q J Y arch ℓ hG cohort :=
    ⟨complete,trace,exclusion,fac,foundation,sharp,bliss,under,approved,ticket,leading,obedient,
      T₀,T₁,φ,c,d,e,grade,scheme,comparison⟩
  exact ⟨R,T,W,cash,w,S,F,L,Q,J,Y,arch,ℓ,selected,before_limits selected⟩

end YM.Integration.WilsonPhysicalCommonElection

