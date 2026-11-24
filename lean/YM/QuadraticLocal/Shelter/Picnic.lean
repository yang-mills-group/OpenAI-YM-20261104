import YM.QuadraticLocal.Tint.Alcove
import YM.Push.ABSOLUTE_SUMS.Animals
import YM.Push.LOCAL_SPLITTING.Atoms
import YM.Extra.MULTISOURCE_TRAJECTORIES.Algebra
/-!
## Assemble the controlled log comparison across *all* actual masks

Will plant mark-only mask changes (keyed by complete cluster) through the
second vacuum merger. First, the layout and log arithmetic. Each cluster has
its own root, nonempty mode, common comparison halo. On each of the sides of
the comparison, at most finitely many terms per cluster. (The sharp application
truncates to sufficiently large finite sublists, with norm estimates, before
invoking this operation). Clusters may use masks already (always evaluate fields
only as approved there), or global marks (unmasked, field independent), even from
mixed modes. No restriction e.g. on all root locations being near enough to fit
in a chart until actually preparing a called cluster. Countable layout, cluster
volume cost paid using the root anchor only (see Shelter.Corner).

Doesn't compare different regular label bases itself, but fixes the identity
 in ANY such comparison, including 'negative' occurrences. A signed remainder may
 already be held on the very halo used for aligning the masks. Requires a SINGLE
 representation uniform in the entire parameter type (use any T, usually a
 dependent product of test unit balls); authorization & cost of an additive log
comparison on that region through the full Holder radii remains to be supplied
from the finite comparison on actual momentum.Jet.Step.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Shelter
open Function Filter Finset Lattice Wilson RG Ac Marker Push Push.Local Push.Corrected Push.AbsoluteSums MeasureTheory
open Animals Next.Foundations Extra.Trajectories
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge}{n:Side}{V T ι μ C : Type}[DecidableEq V]{o:V→Site n}{R:Census V}{P:BudgetPoint} {B H:ℕ}
variable (L:Lamps T ι G P o R)(w:V→ℝ)(hw:∀ i,0<w i)
variable {a b r t ε δ:ℝ} {α:C→Type}
structure Terrain (C:Type)(R:Census V) where
    mode : C→R.Mode
    anchor : C→ V
    at_anchor i: anchor i∈ (mode i).val

namespace Terrain
variable (D:Terrain C R)
def center (o:V→Site n)(i:C):= o (D.anchor i)
def barrier (o:V→Site n)(H:ℕ)(i:C):= neighbors H (D.center o i)
theorem live (i:C): D.mode i ≠ R.quiet := fun h=>Finset.notMem_empty (D.anchor i) ((show (D.mode i).val=∅ from congr_arg Subtype.val h) ▸ D.at_anchor i)
end Terrain
variable (D:Terrain C R)
set_option quotPrecheck false
structure Deck (H:ℕ)(α:C→Type) where
    enrol : (Σ i:C,α i) ≃ ι
    calls i: L.mode (enrol i)= D.mode i.fst
    region (i:Σ j:C, α j) : L.ground (enrol i) ⊆ D.barrier o H i.fst
namespace Deck
variable {L D}
variable [∀ i,Fintype (α i)]
variable (d:Deck L D H α) (i:C) (x:T)(U:Config G n)
def round : ℂ:= ∑ a:α i,L.light x (d.enrol ⟨i,a⟩) U
def white : ℂ:= ∑ a:α i,L.nominal x (d.enrol ⟨i,a⟩) U
lemma shown (h:Healthy P.threshold (D.barrier o H i) U) : d.round i x U=d.white i x U:=by
  apply Finset.sum_congr rfl; intro a _; unfold Lamps.light; split; rfl; exact masked_eq _ _ _ _ (h.mono_left (d.region ⟨i,a⟩))
lemma extent : Poly.send (D.mode i) (d.round i x U)=∑ a:α i,L.frame (d.enrol ⟨i,a⟩) x U := by
    let F : ℂ→+ Poly R:=⟨⟨fun t=> Poly.send (D.mode i) t,Poly.send_zero _⟩,send_add (D.mode i)⟩ -- parent?
    change F _ = _; unfold round; rw [map_sum]; apply Finset.sum_congr rfl; intro a _; unfold Lamps.frame; rw [d.calls ⟨i,a⟩]; rfl
-- mask pointwise locality. L.legal certification doesn't itself include measurability behind ? yes
-- pressure using any t
omit [∀ i,Fintype (α i)] in
lemma locality (j:ι): Width.LocalCharge P o (L.ground j) (fun U=> L.frame j x U):=by
    let f:=fun U=> L.light x j U
    have hf:UsesFinal P.threshold (L.ground j) f∧GaugeInvariant f∧Measurable f:=by
          by_cases h:L.clear j; · have hv:f= L.nominal x j:= funext fun y=>if_pos h; rw [hv]; exact ⟨fun U V hP _=> (L.legal x j).sites U V hP,(L.legal x j).symmetry,(L.legal x j).borel⟩
          have hv:f=RG.masked P.threshold (L.ground j) _:= funext (g:=RG.masked _ _ (L.nominal x j)) (fun y=>if_neg h); rw [hv]; exact ⟨uses_mask _ (L.legal x j).sites,invariant_mask (L.legal x j).symmetry _ _,masked_measurable _ _ _ (L.legal x j).borel⟩
    let I := Poly.send (L.mode j); refine ⟨fun t U=> congr_arg I (hf.2.1 t U),?_,fun U V ht h=> congr_arg I (hf.1 U V ht h),fun U i h v hv=>?_⟩
    · -- Poly.port linear
      let F : ℂ →ₗ[ℂ] Poly R := { toFun:=I, map_add':=send_add _, map_smul':=?_ }
      swap
      · intro a b; change Poly.send (L.mode j) (a*b)=a • Poly.send (L.mode j) b; ext i; rw [Poly.part_smul, Poly.part_send,Poly.part_send]; split <;> simp
      exact F.toContinuousLinearMap.continuous.measurable.comp hf.2.2
    change (Poly.send _ _).part _≠0 at h; rw [Poly.part_send] at h; split at h; next h₁=> exact L.roots j v (h₁ ▸ hv)
    next=>contradiction

lemma gatheredSym : Width.LocalCharge P o (D.barrier o H i) (fun U=> Poly.send (D.mode i) (d.round i x U)):=by
    simp_rw [extent]
    refine ⟨fun t U=> Finset.sum_congr rfl (fun a _=>?_), Finset.measurable_sum _ (fun a _=> (locality x (d.enrol ⟨i,a⟩)).borel),fun U V ht hx=>Finset.sum_congr rfl (fun a _ =>?_),fun U j hj v hv=>?_⟩
    · exact (locality x (L:=L) (d.enrol ⟨i,a⟩)).gauge t U
    · exact ((locality x _).widen (d.region ⟨i,a⟩)).reads U V ht hx
    rw [Poly.part_sum] at hj; by_contra he; apply hj; apply Finset.sum_eq_zero; intro a _; exact Classical.byContradiction fun h=>he (((locality x _).widen (d.region ⟨i,a⟩)).carry U j h v hv)
lemma receipt (h: Summable (fun i=> L.frame i x U)): HasSum (fun i=> Poly.send (D.mode i) (d.round i x U)) (L.log x U):=by
   let g (i:Σ j:C,α j):=L.frame (d.enrol i) x U; have he: HasSum g (L.log x U):= d.enrol.hasSum_iff.mpr h.hasSum
   simp_rw [d.extent]; exact he.sigma (fun i=> (hasSum_fintype _)) -- check
end Deck
end YM.QuadraticLocal.Shelter
