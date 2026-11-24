import YM.Nonperturbative.HeadlineSpec
import YangMills.WilsonProof.Hierarchy
import YangMills.WilsonProof.NativeSupport.HierarchyBridge
import YangMills.FiniteVolume
import YM.FullVolume.Profiles
import YM.FullVolume.Connect
import YM.Extraction.Held
import YM.Extra.WEAK_SCALING_ACTLAW.Comparisons
import YM.Dash.Regular
import YM.Spec.Closed

/-! The full-mesh position limits on fixed physical periods and their
compact convergence to each selected infinite-volume table. -/

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096


noncomputable section
namespace YM.Integration.LeanPointBounds.SpatialModulus
open Function Filter Set Metric MeasureTheory Lattice Wilson RG Source Extraction Extraction.Gaps
open FullVolume PhysicalNext.Repeat.Legato
open scoped Classical BigOperators Topology ContDiff
variable {G : Gauge} (R : Run G) (hG : G.Simple) {n : ℕ}

include hG in
theorem purchased (f : Extraction.Order) (v : Fin n → R.family.book.Token)
    (K : Set (Points n)) (hk : IsCompact K) (sep : K ⊆ conf n) :
    ∃ a B : ℝ, 0<a ∧ 0≤B ∧ ∀ᶠ i : ℕ×ℕ in f.fuse,
      ∀ x y : Positions n, tag (R.family.S.a i.1) x ∈ K →
        dist (tag (R.family.S.a i.1) y) (tag (R.family.S.a i.1) x) ≤ a →
        dist (lifted R.family i.1 i.2 v y) (lifted R.family i.1 i.2 v x) ≤
          B*dist (tag (R.family.S.a i.1) y) (tag (R.family.S.a i.1) x) := by
  let C := R.family
  obtain ⟨a,ha,hA⟩ := hk.exists_cthickening_subset_open (conf_open n) sep
  let V := cthickening a K
  have hV : IsCompact V := hk.cthickening
  obtain ⟨r,hr,outer⟩ := someGrows C.S hV hA
  choose M hM cost using fun j : MotionIndex n =>
    (FullVolume.genuine R hG).bounds n v [j] r hr
  let B : ℝ := ∑ j,M j
  have pos : 0≤B := Finset.sum_nonneg fun j _ => hM j
  have le (j : MotionIndex n) : M j ≤ B :=
    Finset.single_le_sum (fun j _ => hM j) (Finset.mem_univ j)
  refine ⟨a,B*Fintype.card (MotionIndex n),ha,mul_nonneg pos (Nat.cast_nonneg _),?_⟩
  filter_upwards [(Extra.WeakScaling.cofin_snd f).eventually outer,
    (Extra.WeakScaling.cofin_fst f).eventually (eventually_all.mpr cost)] with i P N x y hx hy
  refine stroll (C.S.a_pos _) (lifted C i.1 i.2 v) x y a B pos hy ?_
  intro u j hu
  have inside : tag (C.S.a i.1) u ∈ V := mem_cthickening_of_dist_le _ _ _ K hx hu
  have gap : spaceout C r i (wrap _ ∘ u) :=
    fun b c neq => gridSeparation C.S _ rfl (P _ inside) _ _ neq.symm
  have charge := (N j i.2 u gap).trans (le j)
  rw [dist_eq_norm,unique_units _ (C.S.a_pos _) j u,norm_smul,Real.norm_of_nonneg (C.S.a_pos _).le]
  exact mul_le_mul_of_nonneg_left charge (C.S.a_pos _).le

end YM.Integration.LeanPointBounds.SpatialModulus
end

noncomputable section
namespace YM.Integration.LeanPointBounds.CompactTransfer
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
  obtain ⟨a,B,ha,hB,all⟩ := SpatialModulus.purchased R hG f v K hk sep
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

end YM.Integration.LeanPointBounds.CompactTransfer
end

noncomputable section
namespace LeanPointReturns.Nodes
open YangMills YangMills.Wilson
open YM.Extraction YM.FullVolume
open Filter Function Set MeasureTheory
open scoped Topology ContDiff
variable {g : GaugeGroup} (C : YM.Family g.core)

def representatives {N m n : ℕ}
    (x : Fin n → Site ((wilsonFamily C).period m * (wilsonFamily C).denominator N)) : Positions n :=
  fun i a => ZMod.valMinAbs (x i a)

theorem placed {N m n : ℕ}
    (x : Fin n → Site ((wilsonFamily C).period m * (wilsonFamily C).denominator N)) :
    tag (C.S.a N) (representatives C x) = nodePosition (wilsonFamily C) N m x := rfl

theorem moment {N m n : ℕ} (v : Fin n → C.book.Token)
    (x : Fin n → Site ((wilsonFamily C).period m * (wilsonFamily C).denominator N)) :
    lifted C N m v (representatives C x) = (wilsonFamily C).finiteMoment N m v x := by
  rw [moment_eq]
  unfold lifted
  congr 1
  funext i a
  exact ZMod.coe_valMinAbs _

theorem safe {n m : ℕ} {z : YM.Points n}
    (hz : z ∈ periodPatch (wilsonFamily C) m n) : z ∈ NoHit C.S m n :=
  (no_wrap_hit C.S (show z ∈ Inside C.S m n from hz.2)).2 hz.1

def appoint (row : (m n : ℕ) → (Fin n → C.book.Token) → YM.Points n → ℂ) :
    PeriodPointTable (wilsonFamily C) :=
  fun m {n} v z => row m n v z.val

theorem appointment (row : (m n : ℕ) → (Fin n → C.book.Token) → YM.Points n → ℂ)
    (m n : ℕ) (v : Fin n → C.book.Token) {z : YM.Points n} (hz : z ∈ periodPatch (wilsonFamily C) m n) :
    periodValue (appoint C row) m v z = row m n v z := by
  simp [periodValue, hz, appoint]

theorem test (row : (m n : ℕ) → (Fin n → C.book.Token) → YM.Points n → ℂ)
    (m n : ℕ) (v : Fin n → C.book.Token) (t : SeparatedTest n) (s : (wilsonFamily C).suitable m t) :
    YM.Test.applyTo t (row m n v) = ∫ z, t z * periodValue (appoint C row) m v z := by
  apply integral_congr_ae
  filter_upwards with z
  change t z * row m n v z = t z * periodValue (appoint C row) m v z
  by_cases hz : z ∈ tsupport t
  · exact congrArg (fun a : ℂ => t z * a) (appointment C row m n v ⟨t.tsupport_subset hz,s hz⟩).symm
  · have zero : t z = 0 := notMem_support.mp (fun h => hz (subset_closure h))
    simp [zero]

end LeanPointReturns.Nodes
end

noncomputable section
namespace LeanPointReturns.Uniform
open YangMills YangMills.Wilson
open YM.Extraction YM.FullVolume
open Filter Function Set MeasureTheory
open scoped Topology
open LeanPointReturns.Nodes
variable {g : GaugeGroup} (C : YM.Family g.core)

theorem compact (row : (m n : ℕ) → (Fin n → C.book.Token) → YM.Points n → ℂ)
    (m n : ℕ) (v : Fin n → C.book.Token)
    (cluster : Cluster C .full m n (fun N => lifted C N m v) (row m n v))
    (K : Set (YM.Points n)) (comp : IsCompact K) (inside : K ⊆ periodPatch (wilsonFamily C) m n)
    (ε : ℝ) (pos : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N : ℕ in atTop, ∀ z ∈ K,
      ∀ x : Fin n → Site ((wilsonFamily C).period m * (wilsonFamily C).denominator N),
      dist (nodePosition (wilsonFamily C) N m x) z < δ →
      dist ((wilsonFamily C).finiteMoment N m v x) (periodValue (appoint C row) m v z) < ε := by
  classical
  simp only [Filter.eventually_atTop]
  by_contra! failed
  choose stage later target owner site close wrong using
    fun k : ℕ => failed (1 / ((k : ℝ) + 1)) (by positivity) k
  obtain ⟨point, member, sub, strict, converges⟩ := comp.isSeqCompact owner
  have cofinal : Tendsto stage atTop atTop := tendsto_atTop_mono later tendsto_id
  have toZero : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have tags : Tendsto (fun j => nodePosition (wilsonFamily C) (stage (sub j)) m (site (sub j))) atTop (𝓝 point) := by
    apply Metric.tendsto_nhds.mpr
    intro δ hδ
    have small := (toZero.comp strict.tendsto_atTop).eventually_lt_const (half_pos hδ)
    have picked := (Metric.tendsto_nhds.mp converges) (δ / 2) (half_pos hδ)
    filter_upwards [small,picked] with j near here
    have one : dist (nodePosition (wilsonFamily C) (stage (sub j)) m (site (sub j))) (target (sub j)) < δ / 2 :=
      lt_trans (close (sub j)) near
    calc
      _ ≤ _ := dist_triangle _ (target (sub j)) point
      _ < δ / 2 + δ / 2 := add_lt_add one here
      _ = δ := add_halves δ
  have live := safe C (inside member)
  have raw : Tendsto (fun j => (wilsonFamily C).finiteMoment (stage (sub j)) m v (site (sub j)))
      atTop (𝓝 (row m n v point)) := by
    simp_rw [← moment C]
    exact cluster.2 point live (fun j => representatives C (site (sub j))) (stage ∘ sub)
      (cofinal.comp strict.tendsto_atTop) tags
  have smooth := (cluster.1.continuousAt ((nohitOpen C.S m n).mem_nhds live)).tendsto.comp converges
  have gap : Tendsto (fun j => dist ((wilsonFamily C).finiteMoment (stage (sub j)) m v (site (sub j)))
      (row m n v (target (sub j)))) atTop (𝓝 0) := by
    simpa only [Function.comp_apply,dist_self] using raw.dist smooth
  obtain ⟨j,good⟩ := (gap.eventually_lt_const pos).exists
  apply (not_lt_of_ge (wrong (sub j)))
  rwa [appointment C row m n v (inside (owner (sub j)))]

end LeanPointReturns.Uniform
end

noncomputable section
namespace YM.Integration.LeanPointBounds.Outer
open Filter Set Spec Table Extraction
open PhysicalNext.Repeat.Legato
open scoped Classical Topology BigOperators
variable {G : Gauge} {R : Run G}
    {order : Extraction.Order} {S : Table R.family.book}

open MeasureTheory FullVolume Function Lattice RG Wilson Extraction.Lease Difference Gaps Cells Asymptotics
open scoped ContDiff

open Metric Extra.WeakScaling
theorem comparison (simple:G.Simple)(F:Spec.Final R.family order S){n:ℕ}(v:Fin n→R.family.book.Token)
    (row:ℕ→Points n→ℂ)(earned:∀p,Cluster R.family .full p n
      (fun N=>lifted R.family N p v) (row p))
    {K:Set (Points n)}(compact:IsCompact K)(sep:K⊆conf n){δ:ℝ}(positive:0<δ):
    ∀ᶠi:ℕ in atTop,∀x∈K,dist (row (order.per i) x) (S.read x v)≤δ:=by
  obtain ⟨a,ha,haK⟩:=compact.exists_cthickening_subset_open (conf_open n) sep
  let V:=cthickening a K
  have thick:IsCompact V:=compact.cthickening
  have bought:=CompactTransfer.measured R simple F v V thick haK δ positive
  rw [Extraction.Order.fused,Extraction.Order.late] at bought
  filter_upwards [bought,order.per.cofinal.eventually (room R.family.S compact)] with i paid interior
  intro x hx
  let z:=fun j:ℕ=>address (R.family.S.a (order.mesh j)) x
  have reaches:Tendsto (fun j=>tag (R.family.S.a (order.mesh j)) (z j)) atTop (𝓝 x):=
    (chosen (S:=R.family.S) x).comp order.mesh.cofinal
  have active:∀ᶠj:ℕ in atTop,tag (R.family.S.a (order.mesh j)) (z j)∈V:=by
    filter_upwards [(Metric.tendsto_nhds.mp reaches) a ha] with j hj
    exact mem_cthickening_of_dist_le _ _ _ K hx hj.le
  have just:x∈NoHit R.family.S (order.per i) n:=(no_wrap_hit R.family.S (interior hx)).2 (sep hx)
  have raw:= (earned (order.per i)).2 x just z order.mesh.choose order.mesh.cofinal reaches
  have cont:ContinuousAt (fun x=>S.read x v) x:=
    ((S.smooth_read F.room.kernel.smooth v).continuousOn x (sep hx)).continuousAt ((conf_open _).mem_nhds (sep hx))
  have limit:=raw.dist (cont.tendsto.comp reaches)
  apply le_of_tendsto limit
  filter_upwards [paid,active] with j funded inV
  exact (funded (z j) inV).le

end YM.Integration.LeanPointBounds.Outer
end

noncomputable section
namespace LeanPointReturns
open YangMills YangMills.Wilson YM.Integration
open YM.Extraction YM.FullVolume YM.PhysicalNext.Repeat.Legato
open Filter Function Set MeasureTheory
open scoped Topology
open LeanPointReturns.Nodes
variable {g : GaugeGroup} {R : Run g.core}

theorem rows (uv : PositionsUV R.family .full) :
    ∃ row : (m n : ℕ) → (Fin n → R.family.book.Token) → YM.Points n → ℂ,
      FixedPointReturns (wilsonFamily R.family) (appoint R.family row) ∧
      ∀ (m n : ℕ) (v : Fin n → R.family.book.Token),
        Cluster R.family .full m n (fun N => lifted R.family N m v) (row m n v) := by
  choose row read using uv
  have cluster (m n : ℕ) (v : Fin n → R.family.book.Token) :
      Cluster R.family .full m n (fun N => lifted R.family N m v) (row m n v) :=
    ((read m n v).2.2 []).1
  refine ⟨row, ⟨?_, ?_, ?_⟩, cluster⟩
  · intro m n v
    exact continuousOn_iff_continuous_restrict.mp ((read m n v).1.continuousOn.mono (fun _ hz => safe R.family hz))
  · intro m n v t st
    rw [← test R.family row m n v t st]
    simp_rw [smear_eq]
    exact (read m n v).2.1 t st
  · intro m n v K compact inside ε pos
    exact Uniform.compact R.family row m n v (cluster m n v) K compact inside ε pos

theorem outer (simple : g.core.Simple) {order : YM.Extraction.Order} {S : YM.Table R.family.book}
    (F : YM.Spec.Final R.family order S) (Q : YM.OPE.Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (row : (m n : ℕ) → (Fin n → R.family.book.Token) → YM.Points n → ℂ)
    (cluster : ∀ (m n : ℕ) (v : Fin n → R.family.book.Token),
      Cluster R.family .full m n (fun N => lifted R.family N m v) (row m n v))
    (n : ℕ) (v : Fin n → R.family.book.Token) (K : Set (YM.Points n))
    (compact : IsCompact K) (sep : K ⊆ WilsonFamily.separated n) (ε : ℝ) (positive : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ z ∈ K,
      dist (periodValue (appoint R.family row) (order.per.choose k) v z)
        ((hierarchy F Q).correlation none ((hierarchy F Q).project ∘ v) z) < ε := by
  have measured := LeanPointBounds.Outer.comparison
    simple F v (fun m => row m n v) (fun m => cluster m n v) compact sep (half_pos positive)
  filter_upwards [measured,order.per.cofinal.eventually (room R.family.S compact)] with k seen interior
  intro z hz
  have inPatch : z ∈ periodPatch (wilsonFamily R.family) (order.per.choose k) n :=
    ⟨sep hz,interior hz⟩
  rw [appointment R.family row (order.per.choose k) n v inPatch]
  have identify : (hierarchy F Q).correlation none ((hierarchy F Q).project ∘ v) z = S.read z v := by
    change S.useAt S z (S.classTokens ∘ v) = S.read z v
    rw [S.at_project S F.room.kernel.laws.toSymmetric (fun _ => le_rfl) (sep hz)]
  rw [identify]
  exact (seen z hz).trans_lt (half_lt_self positive)

/-- Fixed-period rows chosen from the same run work for every native final hierarchy. -/
theorem nativeReturns (R : Run g.core) (simple : g.core.Simple) (uv : PositionsUV R.family .full) :
    ∃ points : PeriodPointTable (wilsonFamily R.family), FixedPointReturns (wilsonFamily R.family) points ∧
      ∀ {order : YM.Extraction.Order} {S : YM.Table R.family.book} (F : YM.Spec.Final R.family order S)
        (Q : YM.OPE.Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
        (n : ℕ) (v : Fin n → R.family.book.Token) (K : Set (YM.Points n)),
        IsCompact K → K ⊆ WilsonFamily.separated n → ∀ ε : ℝ, 0 < ε →
        ∀ᶠ k : ℕ in atTop, ∀ z ∈ K,
          dist (periodValue points (order.per.choose k) v z)
            ((hierarchy F Q).correlation none ((hierarchy F Q).project ∘ v) z) < ε := by
  obtain ⟨row, fixed, cluster⟩ := rows (R := R) uv
  exact ⟨appoint R.family row, fixed, fun F Q => outer simple F Q row cluster⟩

end LeanPointReturns
end
