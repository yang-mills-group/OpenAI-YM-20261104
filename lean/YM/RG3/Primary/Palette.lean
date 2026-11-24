import YM.RG3.Law.Retrieve
import YM.RG3.Forms.Rewrite
/-!
# Section projection at a dispatched mark

`dress` uses the projection from `YM.Push.Local` on entries carrying the chosen mark.
The sequences `sales`, `copying` and `tagR` put the projected field first and
carry each earlier entry at its successor index.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Primary
open RG Push.Local Press RG3.Forms Law Finset Function Source Lattice Wilson Marker Overlay Ac MeasureTheory
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {P : Rep G n} {V : Type} [DecidableEq V] [Fintype V] {R : Census V} (s : V)
variable (d : Deck R P)

variable {D : ℕ} {F : Labels.Frame G D} (A : Hol G) (C : SectionData F)

abbrev earns (i : ℕ) := d.contents.rays i = R.fire s
/-- Don't extend through another label history's read footprint when erasing
accounts. All reads in this conversion on dispatched mark only and exactly
the old alignment project (which handles wrapping with local protocol). -/
def receipt (i : ℕ) (U : Config G n) := if earns s d i then
    rebate A C (d.contents.origins s) (d.contents.support i) P.p.threshold (d.contents.H i) U else 0

def fires (i : ℕ) := if earns s d i then
    residual A C (d.contents.origins s) (d.contents.support i) P.p.threshold (d.contents.H i) else d.contents.H i

def stem (i : ℕ) := joint C (d.contents.origins s) (d.contents.support i)
def grows (i : ℕ) := if earns s d i then stem s d C i else d.contents.support i

def vector (i:ℕ) : F.Coeff := if earns s d i then
    weighted A F (d.contents.origins s) (d.contents.support i) P.p.threshold (d.contents.H i) else 0

def comp (A : Hol G) (F : Labels.Frame G D) : F.Coeff := ∑' i, vector s d A i

def signal : Config G n → ℂ := presented C (d.contents.origins s) P.p.threshold (F.core (Primary.comp s d A F))

def copying : ℕ → Support n
  | 0 => C.footprint (d.contents.origins s)
  | Nat.succ i => grows s d C i

def tagR : ℕ → R.Mode
  | 0 => R.fire s
  | Nat.succ i => d.contents.rays i

def sales : ℕ → Config G n → ℂ
  | 0 => signal s d A C
  | Nat.succ i => fires s d A C i

/-- all old entries go one higher, also zeros. d2.forced are placeholder;
use density after `Test.stay` not here. -/
def dress : Deck R P := {
    contents := {
      d.contents with H := sales s d A C
                      support := copying s d C
                      rays := tagR s d
                      units := fun i => d.contents.units i + if i=s then (Primary.comp s d A F) 0 else 0 }
    captions := d.captions }

-- ALL slats carry the slot and section even if involves other markers
-- (then emitting 0). hit price allocated on nonzero slats only.
def feeds (h : (0:Cover)∈C.stencil) : Feed G n R ℕ := {
    column := fun i => (⟨stem s d C i, nonempty_iff_ne_empty.mpr fun he => notMem_empty (d.contents.origins s) (he ▸ (show d.contents.origins s ∈ stem s d C i from
      mem_union_right _ (by simpa only [stem,joint,SectionData.footprint,map_zero,zero_add] using mem_image_of_mem (fun v => wrap n v+d.contents.origins s) h)))⟩,R.fire s)
    value := receipt s d A C }

omit [Fintype V] in
lemma kept {w} (hw : Readable A C P.p n w) (hd : d.Active) : (feeds s d A C hw.sound.anchored).Keeps P.p d.contents.origins := by
  let o := d.contents.origins s
  let W i := stem s d C i
  have hs i := convert_atom o hw (hd.articles.regular i)
  have hA i : Attaches P.p.threshold (W i) (receipt s d A C i) := by
    unfold receipt; split
    · exact (hs i).2.2.2
    exact Attaches.zero ..
  refine ⟨fun i U he => (he (R.fire_hot _)).elim,fun i => (hA i).symmetry,fun i => (hA i).borel,fun i => (hA i).sites,
    fun i U he h => he ((hA i).healthy_zero U h),fun i U v H hi => ?_⟩
  obtain rfl := mem_singleton.mp hi
  exact mem_union_right (d.contents.support i) ((by simpa only [SectionData.footprint,map_zero,zero_add] using mem_image_of_mem (fun v' => wrap n v'+d.contents.origins _) hw.sound.anchored)) -- `stem` is X ∪ footprint.

omit [Fintype V] in
lemma colored {w} (hw : Readable A C P.p n w) (hd : d.Active) : Article.Contents (dress s d A C).contents := by
  constructor
  · rintro (_|i)
    · exact singleton_nonempty _
    exact hd.articles.proper i
  · rintro (_|i) j hj
    · rw [mem_singleton.mp hj]
      change d.contents.origins s ∈ C.footprint (d.contents.origins s)
      exact (by simpa only [SectionData.footprint,map_zero,zero_add] using mem_image_of_mem (fun v' => wrap n v'+d.contents.origins s) hw.sound.anchored)
    have hi := hd.articles.pins i j hj
    change _∈grows s d C i
    unfold grows; split
    · exact mem_union_left _ hi
    exact hi
  rintro (_|i)
  · exact (presented_good (d.contents.origins s) hw _).1
  change P.p.Regular (grows s d C i) (fires s d A C i)
  unfold fires grows; split
  · exact (convert_atom (d.contents.origins s) hw (hd.articles.regular i)).1
  exact hd.articles.regular _

/-- On any solution retaining the regular part of dress, s is now actually
canonical. -/
def drawer {w} (hw : Readable A C P.p n w) (hd : d.Active)
    (Q : Bands R P) (hQ : Q.support=(dress s d A C).contents.support)
    (he : Q.H=(dress s d A C).contents.H) (ht : Q.rays=(dress s d A C).contents.rays)
    (hO : Q.origins=d.contents.origins) (c : Captions R n) : Canonical s (⟨Q,c⟩ : Deck R P) A C := {
  drawer := 0
  user := F.core (Primary.comp s d A F)
  pure := by ext i; simp [Labels.Frame.core]
  mask := by change Q.support 0=C.footprint (Q.origins s); rw [hQ,hO]; rfl
  key := by change Q.rays 0=_; rw [ht]; rfl
  clears := by change Q.H 0=C.places _ (Q.origins s); rw [he,hO]; rfl
  no_flat := fun i hh e => by
    cases i with
    | zero => exact (hh rfl).elim
    | succ i =>
      change Q.rays _=_ at e; rw [ht] at e
      change Q.H _ _ = _; rw [he]; change fires s d A C i 1 = _
      rw [fires,if_pos (show earns s d i from e)]
      exact ((Next.Foundations.reads_null_iff ..).mp (convert_atom (d.contents.origins s) hw (hd.articles.regular i)).2.2.1).1
  null := fun i hh e h => by
    cases i with
    | zero => exact (hh rfl).elim
    | succ i =>
      dsimp only at e h ⊢
      rw [ht] at e; rw [he,hO]; rw [hQ,hO] at h
      change A.PiVanish D _ (fires s d A C i)
      change Nonwrapping (grows s d C i) _ at h
      have hv : earns s d i := e
      simp_rw [fires,if_pos hv]; simp_rw [grows,if_pos hv] at h
      exact ((Next.Foundations.reads_null_iff ..).mp (convert_atom (d.contents.origins s) hw (hd.articles.regular i)).2.2.1).2 h }
end YM.RG3.Primary
