import YM.Integration.WilsonReportWindowSource

/-! Exact gauge invariance and finite torus support of the opened source
itself, including its complete retained signed series. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportFittedSupport
open Function Finset Set MeasureTheory Lattice Wilson RG Source Marker Next Next.Rank Next.Rank.Spindle OPE OPE.Strobe OPE.Vitrines
open Cells Push.GridApprox Extra.Histories Extra.Multi MergeProof MergeProof.Ribbons.ManyCopies.Patrol
open WilsonPhysicalMarkedDefect WilsonPhysicalMarkedDefect.StoredInterior WilsonReportWindowSource
open scoped BigOperators Classical Topology
variable {G : Gauge} (C : Family G) {d k N p : ℕ}

private theorem extent (b : ℕ) :
    (↑(halo 8 ((C.localSection d).footprint (0 : Site (C.side k p)))) : Set (Site (C.side k p))) ⊆
      window 0 (omen C d k b) := by
  rw [island]
  let K := BasisCost.extent (C.localSection d)
  intro x hx
  obtain ⟨y,hy,hY⟩ := halo_spec.mp hx
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hy
  apply halo_spec.mpr
  refine ⟨0,Finset.mem_singleton_self _,(separation_triangle _ (wrap (C.side k p) z+0) x).trans
    ((Nat.add_le_add (show separation (0 : Site (C.side k p)) _ ≤ K from ?_) hY).trans
      (Nat.add_le_add_left ?_ K))⟩
  · rw [separation_comm,separation,add_zero,sub_zero]
    apply Finset.sup_le
    intro i _
    exact (Corona.lap z _).trans ((Finset.le_sup_of_le hz
      (Finset.le_sup (f:=fun i=>(z i).natAbs) (Finset.mem_univ i))) : (z i).natAbs≤K)
  unfold Therm.Stove.eroom
  omega

/-- The original primary and its failed complement use the actual local
polynomial and the original threshold. Both fit in the same purchased window. -/
private theorem loss (law : C.Makes) (cut : k≤N) (Q : Coefficient (C.labels.level d) (C.side k p))
    (b : ℕ) : Interior (window 0 (omen C d k b)) (failed C N p d k Q) := by
  let A := C.path.rep N p k
  let S := C.localSection d
  let X := S.footprint (0 : Site (C.side k p))
  let v := (C.labels.level d).scaled A.p.threshold⁻¹ ((C.labels.level d).core Q.x)
  let f := S.places v (0 : Site (C.side k p))
  let K := window (0 : Site (C.side k p)) (omen C d k b)
  have land := extent (d:=d) (k:=k) (p:=p) C b
  have small : ((X : Support (C.side k p)):Set _) ⊆ K := fun _ j=>land (halo_subset 8 X j)
  have localF := S.placed_local (0 : Site (C.side k p)) v
  have groupF := S.placed_invariant (law.sections d) (0 : Site (C.side k p)) v
  have smoothF := S.continuous_places v (0 : Site (C.side k p))
  obtain ⟨M,me⟩ := (isCompact_range smoothF.norm).bddAbove
  have bound (U : Config G (C.side k p)) : ‖f U‖≤M := me ⟨U,rfl⟩
  have Mn : 0≤M := (norm_nonneg _).trans (bound 1)
  have full : Interior K f := ⟨groupF,smoothF.measurable,
    fun U V e=>localF U V (agrees_mono e small),M,bound⟩
  have kept : Interior K (masked A.p.threshold X f) := by
    refine ⟨Alarm.sails _ X f groupF,masked_measurable _ _ _ smoothF.measurable,
      fun U V e=>Alarm.sail _ X f localF U V (agrees_mono e land),M,?_⟩
    intro U
    by_cases live : Healthy A.p.threshold X U
    · rw [masked_eq _ _ _ _ live]
      exact bound _
    rw [masked_ne _ _ _ _ live,norm_zero]
    exact Mn
  have replace : (fun U=>masked A.p.threshold X f U+(-1:ℂ)*f U)=failed C N p d k Q := by
    funext U
    have same : f U=fitted C N p d k Q U := StoredInterior.primary C N p d k law cut Q U
    by_cases live : Healthy A.p.threshold X U
    · rw [masked_eq _ _ _ _ live]
      change f U+(-1:ℂ)*f U=(if Healthy A.p.threshold X U then 0 else -fitted C N p d k Q U)
      simp [live]
    rw [masked_ne _ _ _ _ live]
    change 0+(-1:ℂ)*f U=(if Healthy A.p.threshold X U then 0 else -fitted C N p d k Q U)
    simp [live,same]
  exact replace ▸ kept.plus (full.scale (-1))

/-- The fitted source and the actual failed primary, at every deposited
coefficient and site, both remain gauge-invariant, bounded and measurable
and depend only on the exact same finite torus window as the native bead. -/
theorem original (law : C.Makes) (v : C.label d) (grade : C.ref d≤k) (cut : k≤N)
    (x : Site (C.side k p)) :
    let B := (C.path.levels.budget k).B
    let K := window x (omen C d k B)
    Interior K (opened C (N:=N) v x) ∧ Interior K (alarm C (N:=N) v x) := by
  let B := (C.path.levels.budget k).B
  let Q := parcel C d k N p v
  let A := C.path.rep N p k
  let K := window x (omen C d k B)
  let base := window (0 : Site (C.side k p)) (omen C d k B)
  obtain ⟨format,paid,_,split⟩ := WilsonReportWindowSource.actual (N:=N) (p:=p) C law grade cut v
  have f := enamel_local (C.localSection d) format paid (law.sections d) B
  rw [show A.p=C.path.levels.budget k from (law.wilson.represents N p k cut).vac] at f
  have e : Interior base (enamel (C.localSection d) A Q B) := by
    change Interior (window 0 (omen C d k B)) _
    rw [island]
    exact f
  have origin := loss C law cut Q B
  have native := e.unchanged _ _ (window_affine _ x 1)
  have lossHere := origin.unchanged _ _ (window_affine _ x 1)
  rw [show affine 1 x 0=x from by simp [affine]] at native lossHere
  have beaded : Interior K (bead C d k N p B v x) := native.scale _
  have alarmed : Interior K (alarm C (N:=N) v x) := lossHere.scale _
  have equal : (fun U=>bead C d k N p B v x U+(-1:ℂ)*alarm C (N:=N) v x U)=opened C (N:=N) v x := by
    funext U
    rw [split x U]
    ring
  exact ⟨equal ▸ beaded.plus (alarmed.scale (-1)),alarmed⟩

end YM.Integration.WilsonReportFittedSupport
end

