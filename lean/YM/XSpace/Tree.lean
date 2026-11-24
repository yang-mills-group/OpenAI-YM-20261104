import YM.XSpace.Geometry
import YM.Tree.Cut

/-!
# Tree gauge on the inversion quotient

The formal gauge prescription used here is tree gauge with unfixed global color. We show it
has the *literal product Haar* rule on our regulator (no often dangerous implicit determinant is
needed for the gauge fixing). A direct elimination works even with singular sites. Analogous
to `YM.Tree.Forest.pack` (different trees and spaces).
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace
open Lattice Function MeasureTheory Wilson
open scoped BigOperators Topology ENNReal
variable {R : Period} {G : Gauge}

namespace Period
variable (R)
abbrev Array (G : Gauge) := R.Link → G.El

/-- Restore a bounded-period variable: inversion reflects oriented edges but reverses
*positive* edge orientation. -/
def restore (U : R.Array G) : Config G R.side := fun e =>
  if R.Chosen e then U (R.rep e) else (U (R.rep e))⁻¹

@[simp] theorem restore_at (U : R.Array G) (e : R.Link) : R.restore U e = U e := by simp [restore,e.property]
@[simp] theorem restore_reflect (U : R.Array G) (e : R.Bonds) : R.restore U (R.reflect e)=(R.restore U e)⁻¹ := by
  by_cases he:R.Chosen e <;> simp [restore,he]

lemma restore_range (U : Config G R.side) : U∈Set.range R.restore ↔ ∀ e : R.Bonds, U (R.reflect e)=(U e)⁻¹ := by
  refine ⟨by rintro ⟨v,rfl⟩; exact R.restore_reflect v, fun h=>⟨fun e=> U e,?_⟩⟩
  funext e; by_cases he:R.Chosen e
  · simp [restore,he,R.rep_chosen]
  simp [restore,he,R.rep_other,h]

theorem restore_injective : Function.Injective (R.restore (G:=G)) := fun a b h =>
  funext fun i => (R.restore_at a i).symm.trans ((congr_fun h i).trans (R.restore_at b i))

@[fun_prop] theorem continuous_restore : Continuous (R.restore (G:=G)) := by
  apply continuous_pi; intro i; unfold restore; split_ifs <;> fun_prop

def act (a : R.Vertex → G.El) (U : R.Array G) : R.Array G := fun e=> a (R.src e) * U e * (a (R.dst e))⁻¹

/-- It is the genuine site gauge action restricted to inversion symmetry. -/
theorem act_restores (a : R.Vertex → G.El) (U : R.Array G) : R.restore (R.act a U)=Lattice.gauge (a ∘ R.vertex) (R.restore U) := by
  funext e
  by_cases h : R.Chosen e
  · simp only [restore,h,if_true,act,(R.rep_sites e h).1,(R.rep_sites e h).2]; unfold Lattice.gauge; simp [restore,h]
  obtain ⟨hs,hd⟩:=R.rep_sites' e h
  simp [restore,h,act,Lattice.gauge,hs,hd,mul_assoc]

/-- Select a spanning tree, specified by a parent for each non-root vertex together
with a strictly decreasing rank (no condition on the rank of arbitrary edges). -/
structure Tree where
  root : R.Vertex
  parent (x : R.Vertex) : R.Vertex
  edge (x : R.Vertex) (h : x≠root) : R.Link
  rank (x : R.Vertex) : ℕ
  joins (x : R.Vertex) (h : x≠root) : R.Joins x (parent x) (edge x h)
  closer (x : R.Vertex) (h : x≠root) : rank (parent x) < rank x

theorem exists_tree (r : R.Vertex) : ∃ T : R.Tree, T.root=r := by
  classical
  let d x:=Nat.find (R.connected x r)
  have h (x : R.Vertex) (hx : x≠ r) : ∃ (y : R.Vertex) (e : R.Link), R.Joins x y e ∧ d y < d x := by
    generalize hg : d x=m
    have hi : R.Path x r m:=hg ▸ Nat.find_spec (R.connected x r)
    cases hi with
    | nil => exact False.elim (hx rfl)
    | cons _ H p => exact ⟨_,_,H,Nat.lt_succ_of_le (Nat.find_min' _ p)⟩
  let p x := if h' : x=r then r else (h x h').choose
  refine ⟨⟨r,p,(fun x hx=>(h x hx).choose_spec.choose),d,(fun x hx=> by
    dsimp only [p]; rw [dif_neg hx]; exact (h x hx).choose_spec.choose_spec.1),fun x hx=>?_⟩,rfl⟩
  dsimp only [p]; rw [dif_neg hx]; exact (h x hx).choose_spec.choose_spec.2

def standardTree : R.Tree := (R.exists_tree (R.vertex 0)).choose

@[simp] theorem standardTree_root : R.standardTree.root=R.vertex 0 := (R.exists_tree _).choose_spec

/-- Independent Haar variables, one per orbit (not the conditional distribution
of periodic Wilson given symmetry). -/
def measure (G : Gauge) : Measure (R.Array G) := Measure.pi fun _=> G.probHaar
instance (G : Gauge) : IsProbabilityMeasure (R.measure G) := by unfold measure; infer_instance
end Period

namespace Period.Tree
variable (T : R.Tree)
abbrev Nonroot := {x // x≠T.root}

lemma edge_unique : Function.Injective (fun x : T.Nonroot=> T.edge x.val x.property) := by
  rintro ⟨x,hx⟩ ⟨y,hy⟩ h
  change T.edge x hx = T.edge y hy at h
  suffices x=y by subst x; rfl
  have hp:= T.joins x hx; rw [h] at hp
  have ha:= T.joins y hy
  rcases hp with ⟨a,b⟩|⟨a,b⟩ <;> rcases ha with ⟨i,j⟩|⟨i,j⟩
  · exact a.symm.trans i
  · exact False.elim ((T.closer x hx).not_gt (by
      rw [show T.parent x=y from b.symm.trans j]; nth_rw 1 [a.symm.trans i]; exact T.closer y hy))
  · have p:=T.closer x hx
    have hx' : T.parent x=y:=a.symm.trans i
    have hy': x=T.parent y:=b.symm.trans j
    rw [hx',hy'] at p; exact False.elim (p.not_gt (T.closer y hy))
  exact b.symm.trans j

-- Eliminate without a gauge-direction Jacobian.
def edges : Finset R.Link := Finset.univ.image fun x : T.Nonroot => T.edge x.val x.property
lemma mem_edges (e : R.Link) : e∈ T.edges ↔ ∃ (x : R.Vertex) (h : x≠T.root), T.edge x h=e := by simp [edges]

/-- Vertex gauge that pins the tree and leaves the root unfixed (takes value one there). -/
def fold (T : R.Tree) (U : R.Array G) (x : R.Vertex) : G.El := if hx : x=T.root then 1 else
    let e := T.edge x hx
    T.fold U (T.parent x) * if R.dst e=x then U e else (U e)⁻¹
termination_by T.rank x
decreasing_by exact T.closer x hx
@[simp] lemma fold_root (U : R.Array G) : T.fold U T.root=1 := by rw [fold,dif_pos rfl]

lemma pins (U : R.Array G) (e : R.Link) (h : e∈ T.edges) : R.act (T.fold U) U e=1 := by
  obtain ⟨x,hx,rfl⟩:=(T.mem_edges e).1 h
  have hv:T.parent x≠x := fun h => by have p:=T.closer x hx; rw [h] at p; exact p.false
  rcases T.joins x hx with ⟨a,b⟩|⟨a,b⟩
  · rw [act, a, b, fold, dif_neg hx]; simp [b,hv]
  rw [act, a,b,fold.eq_1 T U x,dif_neg hx]; dsimp only; rw [if_pos b,mul_inv_cancel]

lemma fold_dep (U V : R.Array G) (h : ∀ e∈ T.edges, U e=V e) : T.fold U=T.fold V := by
  funext x
  suffices hh : ∀ m y, T.rank y=m→ T.fold U y=T.fold V y from hh _ x rfl
  intro m; induction m using Nat.strong_induction_on with
  | h m ih =>
    intro y hy; by_cases he : y=T.root
    · simp [he]
    have p:= ih _ (hy ▸ T.closer y he) (T.parent y) rfl
    rw [fold,dif_neg he,fold.eq_1 T V y,dif_neg he]; dsimp only; rw [p,h _ ((T.mem_edges _).2 ⟨_,he,rfl⟩)]

abbrev Free := { i : R.Link // i ∉ T.edges }
abbrev Slice (G : Gauge) := T.Free → G.El

def splitLinks : R.Array G ≃ᵐ ((↥T.edges → G.El) × T.Slice G) := MeasurableEquiv.piEquivPiSubtypeProd _ _

def drape (u : T.Slice G) : R.Array G := T.splitLinks.symm (1,u)
@[simp] lemma drape_tree (u : T.Slice G) (i : ↥T.edges) : T.drape u i = 1 := congr_fun (congr_arg Prod.fst (T.splitLinks.apply_symm_apply (1,u))) i
@[simp] lemma drape_free (u : T.Slice G) (i : T.Free) : T.drape u i = u i := congr_fun (congr_arg Prod.snd (T.splitLinks.apply_symm_apply (1,u))) i
@[fun_prop] lemma continuous_drape : Continuous (T.drape (G:=G)) := by
  apply continuous_pi; intro i; by_cases he : i ∈ T.edges
  · have h (u : T.Slice G) : T.drape u i=1 := T.drape_tree u ⟨i,he⟩; simp_rw [h]; fun_prop
  have h (u : T.Slice G) : T.drape u i = u ⟨i,he⟩ := T.drape_free u ⟨i,he⟩; simp_rw [h]; fun_prop

def measure (G : Gauge) : Measure (T.Slice G) := Measure.pi fun _=>G.probHaar
instance (G : Gauge) : IsProbabilityMeasure (T.measure G) := by unfold Tree.measure; infer_instance

private def shift (a : R.Vertex → G.El) : T.Slice G ≃ᵐ T.Slice G where
  toFun u i:= a (R.src i.val)*u i*(a (R.dst i.val))⁻¹
  invFun u i:= (a (R.src i.val))⁻¹ * u i * a (R.dst i.val)
  left_inv _ := funext fun _ => by group
  right_inv _ := funext fun _ => by group
  measurable_toFun := by simp only [Equiv.coe_fn_mk]; fun_prop
  measurable_invFun := by simp only [Equiv.coe_fn_symm_mk]; fun_prop

private lemma shift_preserves (a : R.Vertex → G.El) : MeasurePreserving (T.shift a) (T.measure G) (T.measure G) :=
    measurePreserving_pi _ _ fun i : T.Free => G.preserve_two_sided (a (R.src i.val)) ((a (R.dst i.val))⁻¹)

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

theorem tree_gauge (F : R.Array G → X) (hf : Integrable F (R.measure G))
    (h : ∀ a : R.Vertex → G.El, a T.root=1 → ∀ U, F (R.act a U) = F U) :
    (∫ U, F U ∂R.measure G) = ∫ u, F (T.drape u) ∂T.measure G := by
  let M : Measure (↥T.edges → G.El) := Measure.pi (fun _ => G.probHaar)
  letI : IsProbabilityMeasure M := by unfold M; infer_instance
  letI : SFinite (T.measure G) := by unfold Tree.measure; infer_instance
  have hs : MeasurePreserving T.splitLinks (R.measure G) (M.prod (T.measure G)) := by
    unfold M Period.measure Tree.measure splitLinks
    convert! measurePreserving_piEquivPiSubtypeProd (fun _ : R.Link => G.probHaar) (fun i => i∈ T.edges)
  rw [← hs.symm.integral_comp' F]
  have hu : Integrable (fun x => F (T.splitLinks.symm x)) (M.prod (T.measure G)) := (hs.symm.integrable_comp_emb T.splitLinks.symm.measurableEmbedding).mpr hf
  rw [integral_prod _ hu]
  have he (x : ↥T.edges → G.El) : (∫ y,F (T.splitLinks.symm (x,y))∂T.measure G) = ∫ y,F (T.drape y) ∂T.measure G := by
    let U:=T.splitLinks.symm (x,(1:T.Slice G))
    let a:=T.fold U
    have q (y : T.Slice G) : F (T.splitLinks.symm (x,y))= F (T.drape (T.shift a y)) := by
      rw [← h a (T.fold_root _)]
      congr 1; funext i
      by_cases hi:i∈T.edges
      · have p : a=T.fold (T.splitLinks.symm (x,y)):=T.fold_dep _ _ fun j hj=>
          (congr_fun (congr_arg Prod.fst (T.splitLinks.apply_symm_apply (x,(1:T.Slice G)))) ⟨j,hj⟩).trans
          (congr_fun (congr_arg Prod.fst (T.splitLinks.apply_symm_apply (x,y))) ⟨j,hj⟩).symm
        exact Eq.trans (by rw [p]; exact T.pins _ _ hi) (T.drape_tree _ ⟨i,hi⟩).symm
      rw [show T.drape _ i = T.shift a y ⟨i,hi⟩ from T.drape_free _ ⟨i,hi⟩]
      change a (R.src i)* _*(a (R.dst i))⁻¹ = a (R.src i)* y _*(a (R.dst i))⁻¹
      rw [show T.splitLinks.symm (x,y) i= y ⟨i,hi⟩ from congr_fun (congr_arg Prod.snd (T.splitLinks.apply_symm_apply (x,y))) ⟨i,hi⟩]
    simp_rw [q]; exact (T.shift_preserves a).integral_comp' (fun y=> F (T.drape y))
  simp_rw [he]; simp

end Period.Tree

namespace Period
variable (R)

/-- The even-inversion-quotient regulator; same Wilson plaquette cost, half of the cover sum. -/
def energy (U : R.Array G) := Wilson.energy (R.restore U) / 2
@[fun_prop] lemma continuous_energy : Continuous (R.energy (G:=G)) := by unfold Period.energy; fun_prop
@[simp] lemma energy_invariant (a : R.Vertex → G.El) (U : R.Array G) : R.energy (R.act a U)=R.energy U := by unfold Period.energy; rw [act_restores,Wilson.energy_gauge]

def moment (b : ℝ) (F : R.Array G → ℂ) :=
    (∫ U, (Real.exp (-b * R.energy U) : ℂ)* F U ∂R.measure G)/(∫ U, Real.exp (-b * R.energy U) ∂R.measure G : ℝ)

lemma partition_pos (G : Gauge) (b : ℝ) : 0 < ∫ U, Real.exp (-b * R.energy U) ∂R.measure G := by
  let f (U : R.Array G) := Real.exp (-b * R.energy U)
  have hc : Continuous f:=by unfold f; fun_prop
  have hp (U : R.Array G) : 0 < f U := Real.exp_pos _
  letI : IsFiniteMeasure (R.measure G) := by unfold measure; infer_instance
  letI : IsFiniteMeasureOnCompacts (R.measure G):= ⟨fun _ _ => measure_lt_top _ _⟩
  refine (integral_pos_iff_support_of_nonneg (fun U=>(hp U).le) (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).2 ?_
  rw [show f.support = Set.univ from Set.eq_univ_of_forall (fun U => (hp U).ne')]; simp

theorem gauge_moment (b : ℝ) (T : R.Tree) (F : Config G R.side → ℂ) (hf : Continuous F)
    (hg : GaugeInvariant F) :
    R.moment b (F ∘ R.restore)=
      (∫ u, (Real.exp (-b * R.energy (T.drape u)) : ℂ)* F (R.restore (T.drape u)) ∂T.measure G)/
        (∫ u, Real.exp (-b * R.energy (T.drape u)) ∂T.measure G : ℝ) := by
  letI : IsFiniteMeasure (R.measure G) := by unfold measure; infer_instance
  letI : IsFiniteMeasureOnCompacts (R.measure G):= ⟨fun _ _ => measure_lt_top _ _⟩
  unfold Period.moment; congr 1
  · refine T.tree_gauge _ (Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _)) (fun k _ U=>?_)
    simp only [Function.comp_apply, act_restores, hg _ _, energy_invariant]
  rw [T.tree_gauge _ (Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _)) (by intros; simp)]
end Period
end YM.XSpace
