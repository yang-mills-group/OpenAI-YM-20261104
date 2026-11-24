import YM.RG3.Law.Emerald
import YM.Push.LOCAL_SPLITTING.Atoms

/-!
# Bound on singleton coefficient extracted from a canonical model in the
multi-slot deck interface. One section letter (support given literally by
C.footprint) at (optional) index j. If several, combine those on their
SAME mask first, charging sum. Retained Captions and Unit globals on fire s
accumulate at pure unit. No rate claimed here when the provided model isn't
canonically closed; use registration interface/payment later before extraction.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Law
open Lattice Wilson RG Marker Overlay RG3.Forms Push.AbsoluteSums Source Function Finset MeasureTheory
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V} {G : Gauge} {n : Side} {P : Rep G n}
variable (s : V) (d : Deck R P)
variable {D : ℕ} {F : Labels.Frame G D} (H : Hol G) (C : SectionData F)

structure Canonical where
  drawer : ℕ
  -- coordinate grade0 moved to legend globally, use core only on stencil.
  user : F.Coeff
  pure : F.core user=user
  mask : d.contents.support drawer=C.footprint (d.contents.origins s)
  key : d.contents.rays drawer=R.fire s
  clears : d.contents.H drawer=C.places (F.scaled (P.p.threshold)⁻¹ user) (d.contents.origins s)
  no_flat i : i≠drawer → d.contents.rays i=R.fire s → d.contents.H i 1 = 0
  null i : i≠drawer → d.contents.rays i=R.fire s → Nonwrapping (d.contents.support i) (d.contents.origins s) → H.PiVanish D (d.contents.origins s) (d.contents.H i)

namespace Canonical
variable {s d H C} (t : Canonical s d H C)

def keep (i : ℕ) := i≠t.drawer ∧ d.contents.rays i=R.fire s
instance (i : ℕ) : Decidable (t.keep i) := by unfold keep; infer_instance

def index : Coefficient F n := {
  x := legend s d • F.e0+t.user
  support i := if t.keep i then d.contents.support i else univ
  regular i := if t.keep i then d.contents.H i else 0
  forced := solution s d }

omit [Fintype V] in
lemma healthy (h : d.Active) : t.index.Format (d.contents.origins s) H P := by
  have hi i (hu : t.keep i) : d.contents.origins s ∈ d.contents.support i := h.articles.pins i _ (hu.2.symm ▸ mem_singleton_self _)
  have he i := Emerald.access s d h i
  constructor
  · intro i; unfold index; dsimp only; split
    next hu => exact h.articles.regular _
    exact Push.Local.regular_const _
  · intro i; unfold index; dsimp only; split; next h => exact hi _ h
    exact mem_univ _
  · intro i; unfold index; dsimp only; split
    next h => exact t.no_flat i h.1 h.2
    rfl
  · intro i; unfold index; dsimp only; split
    next h => exact t.null i h.1 h.2
    intro _ j; constructor; exact contDiffAt_const
    intro k hk; simp only [Pi.zero_apply]
    rcases Nat.eq_zero_or_pos k with rfl|hp
    · simp
    rw [iteratedDeriv_const] -- search
    simp [hp.ne']
  · exact fun i => (he i).2.2.2.1
  · exact fun i => (he i).2.2.2.2
  · exact fun i => (he i).2.1
  · exact fun i => (he i).2.2.1
  exact fun i => (he i).1

omit [Fintype V] in
lemma remit {w a c δ b u} (hb : d.Budget w a c δ b u) :
    t.index.remBound (d.contents.origins s) P b (c/(w s)+δ/(w s)) := by
  have hr := hb.radial
  have hw := hr.pure s
  obtain ⟨y,hN,hr'⟩ := Emerald.credit s d hb
  obtain ⟨f,hf,hh⟩ := hr.bulk
  have hCp := budget_nonneg (hh s)
  obtain ⟨g,hG,h⟩ := hr.hits
  have hD := budget_nonneg (h s)
  have hb' := hr.factor
  let z i := if t.keep i then f i else 0
  refine ⟨c/(w s),δ/(w s),by positivity,div_nonneg (nonneg_of_mul_nonneg_left hD hb') hw.le,le_rfl,hr.factor,
    ⟨z,?_,fun i => ?_⟩,⟨y,?_,hN⟩⟩
  · rw [div_eq_inv_mul]
    refine budget_mono (budget_scale (x:=(w s)⁻¹) (by positivity) (hh s)) (fun i => ?_) (fun i => ?_)
    · unfold z; split
      · exact (hf i).1.trans (P.p.loMass _ _ (hf i).1)
      unfold BudgetPoint.mass; simp
    unfold z index; dsimp only; split
    next hu =>
      rw [hu.2,if_pos (show s∈ (R.fire s).val from mem_singleton_self _),Poly.solo_toll,←mul_assoc,inv_mul_cancel₀ hw.ne',one_mul]
    unfold BudgetPoint.mass; rw [mul_zero]
    exact mul_nonneg (inv_nonneg.mpr hw.le) ((hh s).1 i)
  · unfold index z; dsimp only; split
    next hu => exact (hf i).2 s (hu.2.symm ▸ mem_singleton_self _)
    change P.p.supBounds _ _ (fun _ => (0:ℂ)) _; simpa using Push.Local.bound_const (G:=G) (B:=P.p) (X:=univ) (o:=d.contents.origins s) (0:ℂ)
  exact (show δ*b/(w s)=b*(δ/(w s)) from by ring) ▸ hr'

lemma expose {w a c δ b u} (h : d.Active) (hb : d.Budget w a c δ b u) : casting s d C t.index := by
  constructor
  · intro U
    let q (i) := snapshots s d i U
    let x := q t.drawer
    let g i := t.index.maskedTerm P i U
    have H0 : x = masked P.p.threshold (C.footprint (d.contents.origins s))
        (C.places (F.scaled P.p.threshold⁻¹ (F.core t.index.x)) (d.contents.origins s)) U := by
      unfold x q snapshots verses
      rw [t.key, if_pos rfl, t.clears, t.mask]
      congr 3
      change t.user = F.core (legend s d • F.e0+t.user)
      rw [map_add,map_smul,t.pure]
      have ht : F.core F.e0 = 0 := by ext i; by_cases h : i=0 <;> simp [Labels.Frame.core,h,Labels.Frame.e0]
      rw [ht,smul_zero,zero_add]
    have hi i : q i = (if i=t.drawer then x else 0)+g i := by
      by_cases he : i=t.drawer
      · subst i; rw [if_pos rfl]; unfold g Coefficient.maskedTerm index; dsimp only; simp only [keep,ne_eq,not_true_eq_false,false_and,↓reduceIte]
        simp [masked,x]
      rw [if_neg he,zero_add]; unfold q snapshots verses g Coefficient.maskedTerm index; dsimp only
      by_cases hx : d.contents.rays i=R.fire s
      · simp [keep,hx,he]
      simp [keep,hx,masked]
    have hs : Summable q := by unfold q; simp_rw [← marked_ray]; exact (((d.contents.bulkBound h.articles hb.radial U).1).hasSum.map (Poly.get (R.fire s)) (Poly.part_cont _)).summable
    let y := fun i => if i=t.drawer then x else 0
    have he : HasSum y x := by convert! hasSum_ite_eq t.drawer x using 2 -- name
    have hg : Summable g := (hs.sub he.summable).congr (fun i => by
      change q i-y i=_; rw [hi]; unfold y; abel)
    unfold localRead Coefficient.exponentialEntry
    change legend s d + (tsum q) = t.index.x 0 + _ + tsum g
    rw [← H0,show q=fun i => y i+g i from funext hi,he.summable.tsum_add hg,he.tsum_eq]
    unfold index Labels.Frame.e0 -- name
    have hh : t.user 0=0 := by rw [← t.pure]; exact update_self (0 : F.Index) (0:ℂ) t.user
    simp [hh]; abel
  rfl

end Canonical
end YM.RG3.Law
