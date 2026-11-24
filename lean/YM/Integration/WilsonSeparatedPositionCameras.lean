import YM.OPE.Coverage.Temporal
import YM.Boundary.Contour

/-! A finite set of Euclidean time charts covers any compact set of mutually distinct
positions in finite arity. The same compact ordered set receives their whole neighborhoods. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedPositionCameras
open Function Set Metric Boundary
open scoped Classical Topology BigOperators
variable {n : ℕ}

def view (g : Ortho) (σ : Equiv.Perm (Fin n)) (x : Points n) : Points n :=
  Points.rearrange σ (Points.move g x)

theorem line (g : Ortho) (σ : Equiv.Perm (Fin n)) (x u : Points n) (t : ℝ) :
    view g σ (x+t • u) = view g σ x + t • view g σ u := by
  apply PiLp.ext
  intro i
  change Ortho.motion g (x (σ i)+t • u (σ i)) = Ortho.motion g (x (σ i))+t • Ortho.motion g (u (σ i))
  rw [map_add,map_smul]

theorem size (g : Ortho) (σ : Equiv.Perm (Fin n)) (x : Points n) : ‖view g σ x‖ = ‖x‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]
  change ∑ i : Fin n, ‖Ortho.move g (x (σ i))‖^2 = ∑ i : Fin n, ‖x i‖^2
  simp only [Ortho.move_norm]
  exact Equiv.sum_comp σ (fun i=>‖x i‖^2)

theorem isometry (g : Ortho) (σ : Equiv.Perm (Fin n)) : Isometry (view g σ) := by
  apply Isometry.of_dist_eq
  intro x y
  have sub : view g σ (x-y) = view g σ x-view g σ y := by
    apply PiLp.ext
    intro i
    exact (Ortho.motion g).map_sub (x (σ i)) (y (σ i))
  rw [dist_eq_norm,dist_eq_norm,← sub,size]

def ordered (n : ℕ) : Set (Points n) := {x | (fun i=>YM.time (x i)) ∈ east n}

theorem opened : IsOpen (ordered n) :=
  (open_east n).preimage (continuous_pi fun i=>Mink.clock_cont.comp (PiLp.continuous_apply 2 _ i))

theorem camera (x : Points n) (hx : x∈conf n) :
    ∃ (g : Ortho) (σ : Equiv.Perm (Fin n)), view g σ x∈ordered n := by
  obtain ⟨a,ha,h⟩ := OPE.Coverage.directions (Fin n × Fin n)
  obtain ⟨g,hg⟩ := h (fun k=>x k.1-x k.2)
  let clock (i : Fin n) := YM.time (Ortho.move g (x i))
  have inj : Injective clock := by
    intro i j he
    by_contra hij
    have pos := mul_pos ha (norm_pos_iff.mpr (sub_ne_zero.mpr (fun h=>hij (hx h))))
    have bound := hg (i,j)
    change a*‖x i-x j‖ ≤ |Ortho.move g (x i-x j) timeAxis| at bound
    rw [show Ortho.move g (x i-x j) = Ortho.move g (x i)-Ortho.move g (x j) from (Ortho.motion g).map_sub ..] at bound
    change a*‖x i-x j‖ ≤ |clock i-clock j| at bound
    rw [he,sub_self,abs_zero] at bound
    exact (not_le_of_gt pos) bound
  let σ := Tuple.sort clock
  exact ⟨g,σ,(Tuple.monotone_sort _).strictMono_of_injective (inj.comp σ.injective)⟩

/-- Every point is viewed inside one common compact subset of the open ordered domain. -/
theorem compact_cover (K : Set (Points n)) (hK : IsCompact K) (clear : K ⊆ conf n) :
    ∃ P : Set (Points n), IsCompact P ∧ P ⊆ ordered n ∧ ∀ x∈K,
      ∃ (g : Ortho) (σ : Equiv.Perm (Fin n)), view g σ x∈P := by
  choose g σ good using fun q : K => camera q.val (clear q.property)
  let c (q : K) := view (g q) (σ q)
  have local_open (q : K) : IsOpen (c q ⁻¹' ordered n) := opened.preimage (isometry (g q) (σ q)).continuous
  choose e he sub using fun q : K => Metric.isOpen_iff.mp (local_open q) q.val (good q)
  let U (q : K) := ball q.val (e q/2)
  have all : K ⊆ ⋃ q : K,U q := fun x hx=>mem_iUnion.mpr ⟨⟨x,hx⟩,mem_ball_self (half_pos (he _))⟩
  obtain ⟨I,cover⟩ := hK.elim_finite_subcover U (fun _=>isOpen_ball) all
  let piece (q : K) := c q '' (K ∩ closedBall q.val (e q/2))
  have compact (q : K) : IsCompact (piece q) := (hK.inter_right isClosed_closedBall).image (isometry (g q) (σ q)).continuous
  refine ⟨⋃ q∈I,piece q,I.finite_toSet.isCompact_biUnion (fun q _=>compact q),?_,?_⟩
  · intro y hy
    obtain ⟨q,-,x,⟨-,hx⟩,rfl⟩ := mem_iUnion₂.mp hy
    exact sub q (mem_ball.mpr ((mem_closedBall.mp hx).trans_lt (half_lt_self (he q))))
  · intro x hx
    obtain ⟨q,hq,inside⟩ := mem_iUnion₂.mp (cover hx)
    exact ⟨g q,σ q,mem_iUnion₂.mpr ⟨q,hq,⟨x,⟨hx,ball_subset_closedBall inside⟩,rfl⟩⟩⟩

end YM.Integration.WilsonSeparatedPositionCameras
