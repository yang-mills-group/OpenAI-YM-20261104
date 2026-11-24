import YM.Integration.WilsonMatrixOriginalDeckExterior
import YM.TraceExtension.Atlas.Group

/-! The genuine reflected complex two-site observation at an arbitrary outer point on the same hierarchy. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalDeckObserver
open Filter Set Finset MeasureTheory Pert Pert.Position MS MS.Menus MS.Local.Physical MS.Land MS.Theater
open Extraction Extraction.Order Spec Climb FVA2 FVA2.ColorCode OPE OPE.Orbits OPE.Levy RG11.Fields
open Trace.Pilot Table PhysMS RG17 SharpGram SharpGram.Lenses
open WilsonMatrixOriginalDeckColumns WilsonMatrixOriginalDeckMixed WilsonMatrixOriginalDeckExterior
open scoped Classical Topology BigOperators Matrix
variable {G:Gauge} {C:Family G} {S:Table C.book} {f:Extraction.Order}
variable (B:Deck G) (F:Spec.Final C f S) (J:ℝ→PhysMS.tower S) (h:ℕ)

/-- Actual signed exterior functional. The submitted field is first and the reflected field is second. -/
def read (t:ℝ) (x:Points 2) (e:(Bel C.book).Field h) : S.Field h→ₗ[ℂ]ℂ :=
  (OPE.Levy.linear₂ (S.classMoment S (fun _:Fin 2=>h) (t•x))).flip (S.adj F.room.kernel.spin h timeAxis (J t h e))

theorem measured (t:ℝ) (x:Points 2) (e:(Bel C.book).Field h) (y:S.Field h) :
    read F J h t x e y=S.classMoment S (fun _:Fin 2=>h) (t•x) ![y,S.adj F.room.kernel.spin h timeAxis (J t h e)] := rfl

/-- The physical signed rotation and real structure fix the same reflected input before taking the limit. -/
theorem reflection (simple:G.Simple) {K:(Bel C.book).Hierarchy} {t:ℝ}
    (aligned:AlignO F.sector F.room.kernel.spin K h (J t h)) (e:(Bel C.book).Field h) :
    J t h ((Bel C.book).adj K.spin h timeAxis e)=S.adj F.room.kernel.spin h timeAxis (J t h e) := by
  let g:=Signed.mirror timeAxis
  change J t h ((Bel C.book).mirror K.spin h g ((Bel C.book).conj K.spin h e)) =
    S.mirror F.room.kernel.spin h g (S.conj F.room.kernel.spin h (J t h e))
  rw [←(compass (C:=C) (H:=K) simple).signed h g _,aligned.axis,aligned.real,(compassF F).signed]

/-- The finite full-field fee of the actual outer functional stays bounded uniformly on any fixed separated compact. -/
theorem price (simple:G.Simple) (lead:PhysMS.Leading F J) {H:(Bel C.book).Hierarchy}
    (paid:∀d:ℕ,∀ᶠr in trail,AlignO F.sector F.room.kernel.spin H d (J r d))
    (e:(Bel C.book).Field h) {K:Set (Points 2)} (compact:IsCompact K) (sep:K⊆conf 2) :
    ∃A:ℝ,0≤A ∧ ∀ᶠt in trail,∀x∈K,fare B J h t (read F J h t x e)≤A := by
  classical
  let b:=WilsonMatrixOriginalDeckColumns.basis C B h
  let far:=(Bel C.book).adj H.spin h timeAxis e
  have one (j:Glyph B h) : ∃D:ℝ,∀ᶠt in trail,∀x∈K,‖read F J h t x e (J t h (b j))‖≤D := by
    let v:MaxwellSlots C (fun _:Fin 2=>h):=![b j,far]
    obtain ⟨D,bd⟩:=compact.exists_bound_of_continuousOn (f:=WickGoal v) (fun x hx=>
      (WickGoal_tied v (sep hx)).continuousAt.continuousWithinAt)
    refine ⟨D+1,?_⟩
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp (lead.lead 2 (fun _=>h) v 0 K compact sep) 1 zero_lt_one,paid h] with t accurate aligned x hx
    have close:=accurate x hx
    rw [dist_comm,dist_eq_norm] at close
    have jets : iteratedFDeriv ℝ 0 (PhysMS.measured F none (J t) v t) x-iteratedFDeriv ℝ 0 (WickGoal v) x=
        iteratedFDeriv ℝ 0 (PhysMS.measured F none (J t) v t-WickGoal v) x := by ext; simp
    rw [jets,norm_iteratedFDeriv_zero] at close
    change ‖PhysMS.measured F none (J t) v t x-WickGoal v x‖<1 at close
    have actual : read F J h t x e (J t h (b j))=PhysMS.measured F none (J t) v t x := by
      rw [measured,←reflection F J h simple aligned]
      unfold PhysMS.measured
      apply congrArg _
      ext i
      fin_cases i <;> rfl
    rw [actual]
    have tri:=norm_le_norm_sub_add (PhysMS.measured F none (J t) v t x) (WickGoal v x)
    exact tri.trans (by linarith [bd x hx])
  choose D bound using one
  refine ⟨max 0 (∑j,D j),le_max_left ..,?_⟩
  filter_upwards [Filter.eventually_all.mpr bound] with t ht x hx
  exact (Finset.sum_le_sum fun j _=>ht j x hx).trans (le_max_right _ _)

end YM.Integration.WilsonMatrixOriginalDeckObserver
