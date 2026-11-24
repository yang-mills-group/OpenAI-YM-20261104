import YM.Integration.WilsonPhysicalAnchoredGauge
import YM.Push.STATIONARY_UNIFORM.Support

/-! Concrete seam-correct gauge transport on the physical finite lattice.
Paths are charged in the genuine torus separation, rather than a choice
of an unwrapped fundamental region. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalAnchoredPaths
open Function Set Finset Lattice RG Wilson
open WilsonPhysicalAnchoredGauge
open scoped Classical BigOperators
variable {n:Side} {G:Gauge}

def roads (o : Site n) : Roads n where
  root:=o
  arm x:=route (lift x) (lift x+lift (o-x)) 1
  closed x:=by
    let w:=route (lift x) (lift x+lift (o-x)) 1
    calc stop x w=stop (wrap n (lift x)) w := by rw [wrap_lift]
      _=wrap n (stop (lift x) w) := (wrap_stop_cover ..).symm
      _=o := by unfold w; rw [route_end,map_add,wrap_lift,wrap_lift];abel

theorem length (o x : Site n) : ((roads o).arm x).length≤4*separation o x := by
  have row (l:List Axis): (axisRoute (lift x) (lift x+lift (o-x)) l).length≤l.length*separation o x := by
    induction l with
    | nil=>simp [axisRoute]
    | cons i l ih=>
      change (straight i ((lift x+lift (o-x)) i-lift x i) ++ axisRoute (lift x) (lift x+lift (o-x)) l).length≤_
      rw [List.length_append,List.length_cons,Nat.succ_mul]
      have co:((lift x+lift (o-x)) i-lift x i)=(lift (o-x)) i := by change lift x i+lift (o-x) i-lift x i=lift (o-x) i;abel
      rw [co,straight,List.length_replicate]
      exact (Nat.add_le_add (component_le (o-x) i) ih).trans_eq (Nat.add_comm ..)
  have bill:=row (allAxes 1)
  simpa only [roads,route,allAxes,List.length_map,List.length_finRange] using bill

theorem visited (x y:Site n) (w:Walk) (h:y∈visits x w) : separation x y≤w.length := by
  induction w generalizing x with
  | nil=>have he:y=x:=by simpa [visits] using h
         subst y;simp
  | cons d w ih=>
    change y∈x::visits (x+d.vec) w at h
    rcases List.mem_cons.mp h with h|h
    · subst y;simp
    · exact (separation_triangle x (x+d.vec) y).trans (by
        have a:=Push.Uniform.letter_step x d
        have b:=ih _ h
        simp only [List.length_cons];omega)

/-- All read edges and both endpoints are inside the authenticated short
support's existing halo, including when the support crosses a torus seam. -/
theorem charged (o : Site n) (X : Support n) (D:ℕ) (rad:∀ x∈X,separation o x≤D) :
    collar (roads o) (X:Set (Site n))⊆(halo (4*D) X:Set (Site n)) := by
  intro y hy
  rcases hy with h|⟨x,hx,hxy⟩
  · exact halo_subset _ _ h
  exact halo_spec.mpr ⟨x,hx,(visited x y _ hxy).trans ((length o x).trans (Nat.mul_le_mul_left 4 (rad x hx)))⟩

theorem localized {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (o : Site n) (X:Support n)
    (D:ℕ) (rad:∀x∈X,separation o x≤D) {B:Config G n→E} (h:LocalOn (X:Set (Site n)) B) :
    GaugeInvariant (representative (roads o) B) ∧ LocalOn (halo (4*D) X:Set (Site n)) (representative (roads o) B) := by
  refine ⟨invariant (roads o) B,fun U V agree=>support _ h U V ?_⟩
  intro e he hb;exact agree e (charged o X D rad he) (charged o X D rad hb)

end YM.Integration.WilsonPhysicalAnchoredPaths

