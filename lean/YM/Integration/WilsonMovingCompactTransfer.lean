import YM.Integration.WilsonMeasuredSpatialModulus
import YM.Dash.Regular
import YM.Spec.Closed

/-! Regulator-dependent fine positions on the originally selected extraction.
The auxiliary finite Wilson Lipschitz constant is spent at fixed compact
set.  There is no restriction on ties in individual coordinate projections.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingCompactTransfer
open Function Filter Set Metric MeasureTheory Lattice Wilson RG Source Extraction
open PhysicalNext.Repeat.Legato Extra.WeakScaling FullVolume
open scoped Classical BigOperators Topology ContDiff
variable {G : Gauge} (R : Run G) (hG : G.Simple) {n : ℕ}
    {f : Extraction.Order} {S : Table R.family.book} (F : Spec.Final R.family f S)

include hG F in
theorem measured (v : Fin n → R.family.book.Token)
    (K : Set (Points n)) (hk : IsCompact K) (sep : K ⊆ conf n) (ε : ℝ) (he : 0<ε) :
    ∀ᶠ i : ℕ×ℕ in f.fuse, ∀ z : Positions n, tag (R.family.S.a i.1) z ∈ K →
      dist (lifted R.family i.1 i.2 v z) (S.read (tag (R.family.S.a i.1) z) v) < ε := by
  let C := R.family
  obtain ⟨a,B,ha,hB,all⟩ := WilsonMeasuredSpatialModulus.purchased R hG f v K hk sep
  have near (x : K) : ∃ η : ℝ, 0<η ∧ ∀ᶠ i : ℕ×ℕ in f.fuse, ∀ z : Positions n,
      tag (C.S.a i.1) z ∈ K → dist (tag (C.S.a i.1) z) x.val < η →
      dist (lifted C i.1 i.2 v z) (S.read (tag (C.S.a i.1) z) v) < ε := by
    have c : ContinuousAt (fun u => S.read u v) x.val :=
      ((S.smooth_read F.room.kernel.smooth v).continuousOn x.val (sep x.property)).continuousAt
        ((conf_open _).mem_nhds (sep x.property))
    obtain ⟨δ,hδ,hD⟩ := Metric.continuousAt_iff.mp c (ε/4) (by positivity)
    let η := min (a/4) (min (δ/2) ((ε/16)/(1+B)))
    have hden : 0<1+B := by linarith
    have hη : 0<η := lt_min (by positivity) (lt_min (by positivity) (div_pos (by positivity) hden))
    have aa : η ≤ a/4 := min_le_left _ _
    have dd : η ≤ δ/2 := (min_le_right _ _).trans (min_le_left _ _)
    have small : η*(1+B) ≤ ε/16 :=
      (le_div_iff₀ hden).mp ((min_le_right _ _).trans (min_le_right _ _))
    have density : Dense (generic n) := Dash.full n
    obtain ⟨xg,hg,close⟩ := Metric.mem_closure_iff.mp (density x.val) η hη
    have distg : dist xg x.val < η := by simpa only [dist_comm] using close
    let y (N : ℕ) := address (C.S.a N) xg
    have round : Tendsto (fun N => tag (C.S.a N) (y N)) atTop (𝓝 xg) := chosen xg
    have here := points_approach F.room.generic hg round v
    have fit := ((round.comp (cofin_fst f)).eventually (Metric.ball_mem_nhds xg hη))
    have moment := here.eventually (Metric.ball_mem_nhds (S.read xg v) (show 0<ε/4 by positivity))
    refine ⟨η,hη,?_⟩
    filter_upwards [all,fit,moment] with i bill landed tested z hz hx
    let t := C.S.a i.1
    have hy : dist (tag t (y i.1)) xg < η := landed
    have hv : dist (lifted C i.1 i.2 v (y i.1)) (S.read xg v) < ε/4 := tested
    have walk : dist (tag t (y i.1)) (tag t z) ≤ 3*η := by
      have via := dist_triangle (tag t (y i.1)) xg x.val
      have back := dist_triangle (tag t (y i.1)) x.val (tag t z)
      rw [dist_comm x.val (tag t z)] at back
      linarith
    have quote := bill z (y i.1) hz (walk.trans (by linarith))
    rw [dist_comm] at quote
    have fee : dist (lifted C i.1 i.2 v z) (lifted C i.1 i.2 v (y i.1)) ≤ B*(3*η) :=
      quote.trans (mul_le_mul_of_nonneg_left walk hB)
    have cx : dist (S.read xg v) (S.read x.val v) < ε/4 := hD (by linarith : dist xg x.val < δ)
    have cz : dist (S.read (tag t z) v) (S.read x.val v) < ε/4 := hD (by linarith : dist (tag t z) x.val < δ)
    have h₁ := dist_triangle (lifted C i.1 i.2 v z) (lifted C i.1 i.2 v (y i.1)) (S.read xg v)
    have h₂ := dist_triangle (lifted C i.1 i.2 v z) (S.read xg v) (S.read x.val v)
    have h₃ := dist_triangle (lifted C i.1 i.2 v z) (S.read x.val v) (S.read (tag t z) v)
    rw [dist_comm (S.read x.val v) (S.read (tag t z) v)] at h₃
    change dist (lifted C i.1 i.2 v z) (S.read (tag t z) v) < ε
    nlinarith only [fee,hv,cx,cz,h₁,h₂,h₃,small,hη,he]
  choose η hη purchased using near
  have covers : K ⊆ ⋃ x : K, ball x.val (η x) := by
    intro z hz; exact mem_iUnion.mpr ⟨⟨z,hz⟩,mem_ball_self (hη _)⟩
  obtain ⟨s,hs⟩ := hk.elim_finite_subcover (fun x : K => ball x.val (η x)) (fun _ => isOpen_ball) covers
  filter_upwards [(eventually_all_finset s).mpr (fun x _ => purchased x)] with i hi z hz
  obtain ⟨x,hxs,he⟩ := mem_iUnion₂.mp (hs hz)
  exact hi x hxs z hz he

end YM.Integration.WilsonMovingCompactTransfer

