import YM.Integration.WilsonOriginalStarSceneMasked
import YM.Integration.ConditionalAffineRouteJets

/-! The real collar correction for every original reporting coordinate. On its
nonzero branch an actual old compulsory owner occurs, and the inserted value
is bounded on its own unchanged healthy section footprint. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalStarFlagPrice
open Function Filter Finset Lattice Wilson RG Source Labels Marker QuadraticLocal Earn Sunrise
open PhysicalNext.Repeat.Legato WilsonOriginalStarSceneWords WilsonOriginalStarSceneRows
open WilsonOriginalStarSceneMasked ActualRunPhysicalPages
open Push.AbsoluteSums.Animals MeasureTheory
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) {V T : Type} [DecidableEq V] [Fintype V] (d : V → ℕ)

def extent := max (WilsonOriginalStarSceneMasked.range R d)
   (univ.sup fun j => (R.family.localSection (d j)).stencil.sup Laurent.size)

omit [DecidableEq V] in
theorem fit (simple : G.Simple) : ∀ᶠ k in atTop,∀ (N p:ℕ), k ≤ N →
    extent R d ≤ (R.family.path.rep N p k).p.B := by
  let a:=extent R d
  filter_upwards [(Real.tendsto_log_atTop.comp (Next.Rank.Station.hat_rate R.family.path.levels simple)).eventually_ge_atTop
    ((a:ℝ)+1)] with k hk N p top
  have eqBudget:(R.family.path.rep N p k).p=R.family.path.levels.budget k:=(R.makes.wilson.represents N p k top).vac
  rw [eqBudget,(Next.Rank.Paint.historic R.family.path.levels k).2.1]
  change a ≤ ⌈(Real.log (R.family.path.levels.clock.hatBeta k))^2⌉₊
  apply (Nat.cast_le (α:=ℝ)).mp
  apply le_trans _ (Nat.le_ceil _)
  change (a:ℝ)+1 ≤ Real.log (R.family.path.levels.clock.hatBeta k) at hk
  have non : (0:ℝ) ≤ a:=Nat.cast_nonneg _
  nlinarith only [non,hk,mul_nonneg (show 0 ≤ Real.log (R.family.path.levels.clock.hatBeta k) from by linarith) (show 0 ≤ Real.log (R.family.path.levels.clock.hatBeta k)-1 from by linarith)]

omit [DecidableEq V] in
theorem contained {n : Side} (o : V → Site n) (B : ℕ) (enough:extent R d ≤ B) (j : V) :
    (R.family.localSection (d j)).footprint (o j) ⊆ neighbors (B+1) (o j):=by
  intro y inSection
  obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp inSection
  apply (neighbors_mem ..).mpr
  rw [add_comm (wrap n a)]
  exact (ConditionalAffineRouteJets.cover_distance (o j) a).trans
    ((Finset.le_sup (f:=Laurent.size) ha).trans ((Finset.le_sup
      (f:=fun i:V=>(R.family.localSection (d i)).stencil.sup Laurent.size) (mem_univ j)).trans
      ((le_max_right ..).trans (enough.trans (Nat.le_succ _)))))

variable (N p k : ℕ) (v : (j:V)→R.family.label (d j))
  (o : V → Site (R.family.side k p))

set_option quotPrecheck false
local notation "P" => R.family.path.rep N p k
local notation "D" j:max => (R.family.localSection (d j)).footprint (o j)
local notation "H" j:max => neighbors ((P).p.B+1) (o j)
local notation "S" j:max => kernel R N p k (d j) ((R.family.labels.level (d j)).core (v j)) (o j)

def slip (j:V) (U : Config G (R.family.side k p)) :=
    if Healthy (P).p.threshold (D j) U ∧ ¬Healthy (P).p.threshold (H j) U then (S j) U else 0

omit [DecidableEq V] [Fintype V] in
theorem owner (j:V) (U : Config G (R.family.side k p)) (q:Finset ℕ)
    (selected : (P).activities.admissible (P).p U q) (actual : slip R d N p k v o j U ≠0) :
    ∃ x∈H j, x∈flags (P).p.threshold U ∧ ∃ i∈q,x∈((P).activities.forced i).inventory := by
  unfold slip at actual
  split at actual
  · rename_i live
    obtain ⟨x,hx,hflag⟩:= Finset.not_disjoint_iff.mp live.2
    exact ⟨x,hx,hflag,Finset.mem_biUnion.mp (selected.2.symm ▸ hflag)⟩
  · exact (actual rfl).elim

omit [DecidableEq V] [Fintype V] in
theorem size (j:V) (top:k ≤ N) (ref:R.family.ref (d j) ≤ k) (U : Config G (R.family.side k p)) :
    ‖slip R d N p k v o j U‖ ≤ price R k (d j) ((R.family.labels.level (d j)).core (v j)):=by
  have cost:=(priced R N p k (d j) top ref ((R.family.labels.level (d j)).core (v j)) (o j)).2
  unfold slip
  split
  next paid => exact cost.2 U paid.1 [] (Nat.zero_le _) (by simp)
  next => simpa only [norm_zero] using cost.1

omit [DecidableEq V] in
theorem posted (j:V) (enough:extent R d ≤ (P).p.B) (U : Config G (R.family.side k p)) :
    masked (P).p.threshold (H j) (S j) U + slip R d N p k v o j U =
      masked (P).p.threshold (D j) (S j) U:=by
  by_cases whole:Healthy (P).p.threshold (H j) U
  · have inner:Healthy (P).p.threshold (D j) U:=Disjoint.mono_left (contained R d o (P).p.B enough j) whole
    rw [masked_eq _ _ _ _ whole,masked_eq _ _ _ _ inner,slip,if_neg (fun h=>h.2 whole),add_zero]
  · rw [masked_ne _ _ _ _ whole,zero_add,slip]
    by_cases yy:Healthy (P).p.threshold (D j) U
    · rw [if_pos ⟨yy,whole⟩,masked_eq _ _ _ _ yy]
    · rw [if_neg (fun h=>yy h.1),masked_ne _ _ _ _ yy]

theorem all_fields (t:V→T→ℂ) (σ:ℝ) (top:k ≤ N) (enough:extent R d ≤ (P).p.B) (x:T) (U : Config G (R.family.side k p)) :
    let g:=Pert.Asymptotics.regulatorRun R.family N p k
    let bank:=rendered (rows R d o σ g (P).p.threshold v t) (P).p g
    bank.log x U + ∑j:V,Poly.send ((Stock.census V).fire j) (t j x*slip R d N p k v o j U) =
      ∑j:V,Poly.send ((Stock.census V).fire j)
        (t j x*(v j 0+masked (P).p.threshold (D j) (S j) U)):=by
  dsimp only
  rw [whole R d σ v t N p k top o ((le_max_left ..).trans enough) x U,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [←Extra.Trajectories.send_add,←mul_add,add_assoc,posted R d N p k v o j enough U]

end YM.Integration.WilsonOriginalStarFlagPrice
