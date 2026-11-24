import YM.Integration.WilsonSeparatedPhysicalCopies
import YM.OPE.Screens.Entry
import YM.OPE.Levy.Measured

/-! Passage of the entire finite signed moving-input report to the same
ground algebra.  The terminal label varies along its actual regulator
sublimit.  Every reflected word keeps the full exterior. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedPhysicalView
open Function Filter Lattice Wilson RG Cells Extraction OPE OPE.Orbits OPE.Cards
open OPE.Log.Trunk.Shuttle Trace.Pilot Frontier6.Road
open FilteredWilsonProduct FilteredProductLimit FilteredIntrinsicGramReadout
open scoped Classical BigOperators Topology
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
variable {I E : Type} [Fintype I] [Fintype E] {d : I → ℕ} {de : E → ℕ} {D : ℕ}

private theorem viewingGrades (F : Spec.Final C f S)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (J : ℝ → PhysMS.tower S)
    (v : (i : I) → (Climb.Bel C.book).Field (d i)) (r : ℝ)
    (x : I → E4) (y : E → E4) (w : Labels S de) (s : Viewers F) (sep : Injective (beside x y)) :
    whole (spectator F s) x (PhysMS.Frame.born J r v) y w =
      ∑ g : Grades d, whole (spectator F s) x (sector F Q J v r g) y w := by
  let A := F.sector.derivatives
  let p (i:I) (k:Fin (d i+1)) := Q.cutTest k.val (d i) (J r (d i) (v i))
  let lift (i:I) (k:Fin (d i+1)) := A.rise (Nat.le_of_lt_succ k.isLt) (p i k)
  have sum : PhysMS.Frame.born J r v = fun i => ∑ k,lift i k := by
    funext i
    change J r (d i) (v i) = ∑ k,A.rise _ (Q.cutTest _ _ _)
    rw [Q.reconstruct _ _ le_rfl,A.arrival Q.continuum.laws.toSymmetric Q.lifts]
  let M : MultilinearMap ℂ (fun i=>S.Field (d i)) ℂ :=
    sectionLabels (d:=Sum.elim d de) w (Orbits.moment (spectator F s) (beside x y))
  have placed (u:Labels S d) : M u = whole (spectator F s) x u y w := sectionLabels_apply ..
  rw [←placed,sum,M.map_sum lift]
  apply Finset.sum_congr rfl
  intro g _
  rw [placed]
  let dim := Sum.elim (levels g) de
  have up : dim ≤ Sum.elim d de := by
    rintro (i|i)
    · exact Nat.le_of_lt_succ (g i).isLt
    · exact le_rfl
  let low := stages (sector F Q J v r g) w
  have rearr : (fun i => A.rise (up i) (low i)) = stages (fun i => lift i (g i)) w := by
    funext i
    cases i with
    | inl i => rfl
    | inr i => exact A.arrival Q.continuum.laws.toSymmetric Q.lifts _
  exact ((Levy.inclusionMoment F _ _ up low _ s sep).trans (congrArg (Orbits.moment (spectator F s) _) rearr)).symm

private def lamp (F : Spec.Final C f S)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (v : (i : I) → (Climb.Bel C.book).Field (d i))
    (r : ℝ) (j : ℕ) (x : I → Cover) (g : Grades d) (l : Filter (ℕ×ℕ))
    (h : Screen (C.S.gridPoint j ∘ x)) : Spark C l j where
  Index := I
  x := x
  v := names (sector F Q J v r g)
  q := frozen C _
  limit _ := tendsto_const_nhds
  frames := h

/-- Every selection, including the unselected state, sees the same
terminal cluster point and the summed original field. The right hand
side charges only the center and the presold exterior cells. -/
theorem measured (F : Spec.Final C f S) (fac : Facilities C f S)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (v : (i : I) → (Climb.Bel C.book).Field (d i))
    (r : ℝ) (b j : ℕ) (bj : b ≤ j) (x : I → Cover) (hx : Screen (C.S.gridPoint j ∘ x))
    (y : E → E4) (w : Labels S de) {a c A : ℝ}
    (buy : Probe.Viewer C f (names w) b c A) (free : ClearOf 0 y c)
    (separated : Injective (beside (C.S.gridPoint j ∘ x) y))
    (outside : Injective (beside (sole (0:E4)) y))
    (paid : ∀ᶠ u in f.fuse, PaidAt C.S u.1 u.2 b (C.beta u.1 u.2) a
      (WilsonSeparatedPhysicalCopies.gap (D:=D) F Q J v r b j x u))
    (z : C.label D) (cluster : ContinuumIntrinsicWilsonProduct.Cluster F Q J v r b j x z)
    (s : Viewers F) :
    ‖whole (spectator F s) (C.S.gridPoint j ∘ x) (PhysMS.Frame.born J r v) y w -
      upon (spectator F s) D 0 y w (S.project D z)‖ ≤ a*A := by
  classical
  obtain ⟨l,live,sub,hz⟩ := cluster
  letI := live
  let output := host hz j
  let K := Option (Grades d)
  let L : K → Spark C l j := fun k => k.elim output (fun g=>lamp F Q J v r j x g l hx)
  let scalar : K → ℂ := fun k => k.elim (-1) (fun _=>1)
  let ix := (Fintype.equivFin K).symm
  have inner (g:Grades d) (u:ℕ×ℕ) : (lamp F Q J v r j x g l hx).cuts u.1 u.2 =
      leaves C j (levels g) x (component F Q J v g r) u.1 u.2 := by
    funext U
    change register C j x (germ (frozen C (names (sector F Q J v r g)))) u.1 u.2 U = _
    rw [germ_here]
    simp only [leaves,Finset.prod_apply, frozen]
    rfl
  have summands (u:ℕ×ℕ) : (fun U:Config G (C.side u.1 u.2) =>
      ∑ i:Fin (Fintype.card K), scalar (ix i)*(L (ix i)).cuts u.1 u.2 U) =
        WilsonSeparatedPhysicalCopies.gap (D:=D) F Q J v r b j x u := by
    funext U
    rw [ix.sum_comp (fun k:K=>scalar k*(L k).cuts u.1 u.2 U),Fintype.sum_option]
    simp only [scalar,L,Option.elim_none,Option.elim_some,neg_one_mul,one_mul,inner]
    have out : output.cuts u.1 u.2 U = _ := congrFun (congrFun (congrFun (hostcut hz j) u.1) u.2) U
    have expand := congrFun (field_expansion F Q J v r j x u) U
    rw [Finset.sum_apply] at expand
    rw [out,←expand]
    dsimp only [WilsonSeparatedPhysicalCopies.gap,Pi.sub_apply,stampEntry]
    rw [sub_eq_add_neg,add_comm]
  have points (i:Fin (Fintype.card K)) : Injective (beside (Probe.point (L (ix i))) y) := by
    cases h:ix i with
    | none =>
      change Injective (beside (C.S.gridPoint j ∘ fun _:Unit=>(0:Cover)) y)
      rw [show (C.S.gridPoint j ∘ fun _:Unit=>(0:Cover))=sole (0:E4) from hostPoint hz]
      exact outside
    | some g => exact separated
  have price := Probe.sold (X':=fun N p=>WilsonSeparatedPhysicalCopies.gap (D:=D) F Q J v r b j x (N,p))
    F sub buy fac.toServices.schedule (scalar ∘ ix) bj (paid.filter_mono sub)
    (Eventually.of_forall summands) points free
  have joint := (glance_bound F s _).trans price
  rw [map_sum] at joint
  simp only [map_smul,Function.comp_apply] at joint
  rw [ix.sum_comp (fun k:K=>scalar k • (glance F s) (Probe.view F (L k) (names w) y)),Fintype.sum_option] at joint
  have fieldRead (g:Grades d) : (glance F s) (Probe.view F (lamp F Q J v r j x g l hx) (names w) y) =
      whole (spectator F s) (C.S.gridPoint j ∘ x) (sector F Q J v r g) y w :=
    read_algebra F s separated
  have outRead : (glance F s) (Probe.view F output (names w) y) =
      upon (spectator F s) D 0 y w (S.project D z) := by
    change (glance F s) (viewing F (beside (C.S.gridPoint j ∘ fun _:Unit=>(0:Cover)) y)
      (beside (sole (⟨D,z⟩:C.book.Token)) (names w)))=_
    rw [show (C.S.gridPoint j ∘ fun _:Unit=>(0:Cover))=sole (0:E4) from hostPoint hz,glance_sees F s _ _ outside,
      upon_observe _ w (spectate F s) (spectate_respects F s) outside]
    exact (projectedOne (spectator F s) _ D z (spectate F s).laws.toSymmetric (spectate_respects F s) outside).symm
  simp only [scalar,L,Option.elim_none,Option.elim_some,neg_smul,one_smul,fieldRead,outRead] at joint
  rw [viewingGrades F Q J v r _ y w s separated,sub_eq_add_neg,add_comm]
  exact joint

end YM.Integration.WilsonSeparatedPhysicalView
