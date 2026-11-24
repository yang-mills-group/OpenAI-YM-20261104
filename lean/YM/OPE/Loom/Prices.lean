import YM.OPE.Frame.Profiles
import YM.OPE.Loom.Last
/-!
# Matching inputs at k

These will have to come from estimates on the X columns in the theory where the logs
are to be proved. This states just pricing of one **field** in two directions;
no composite-root arrangement or tree prices (or OPE coefficients) need be among those
inputs. For matching direct and signed roots using `viable`, it suffices to have this
also in only a single filter finer than the established extraction, as in `Origins`; the
phase resolution of Final remains arbitrary thereafter.

No growth estimate here is supplied by the existing convergent Wick columns result by itself.
-/
set_option autoImplicit false
noncomputable section
open Filter Function Set MeasureTheory
open scoped Topology BigOperators Classical
namespace YM.OPE.Loom
open Lattice RG Wilson MergeProof Accent Ribbons Source Overlay Bid ManyCopies Next.Rank Next.UVStress PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Bandage
open Push Marker Cells Extraction
variable {G:Gauge} {C:Family G}{f:Extraction.Order}{T:Table C.book}{F:Spec.Final C f T}{W r D}(A : Sharper C W r D)
local notation "Y" => C.path.levels
local notation "X" => C.path.levels.clock.hatBeta
local notation "S*" => C.S
local notation "P" => C.path.levels.budget
set_option quotPrecheck false
variable {𝓛:Filter (ℕ×ℕ)}[𝓛.NeBot] (B:Frame.Scheme F)

-- any T clock, budgets carry uniformity in i, active eventually at each demand
structure Origins (B : Frame.Scheme F) (𝓛: Filter (ℕ×ℕ)) : Prop where
    extraction : 𝓛≤ f.fuse
    uses (d:ℕ) (z:T.Field d) : ∃ x:ℕ→ℝ, Coins atTop C.S.scale x ∧ ∀ᶠ k in atTop,
      0<x k ∧ ∃ (v : ℕ×ℕ→ C.label d)(u:C.label d), Tendsto v 𝓛 (𝓝 u) ∧ T.project d u=z ∧
        ∀ᶠ l:ℕ×ℕ in 𝓛,x k*C.S.a k^d * Spindle.paid C d k l.1 l.2 (v l) ≤ fly (G:=G) C.path.levels d k
    bounds (d:ℕ) : ∃ x:ℕ→ℝ, Coins atTop C.S.scale x ∧
      ∀ᶠ k in atTop, 0<x k ∧ ∀ (φ:Filter (ℕ×ℕ)), φ.NeBot → φ ≤ 𝓛 → ∀ (u:ℝ)(v:ℕ×ℕ→ C.label d)(p:C.label d), Tendsto v φ (𝓝 p) → (∀ᶠ l in φ, quota C d k l.1 l.2 (v l) ≤ u) → ∀ i∈ Frame.limits B.rings d,
          ‖B.representation.coord i d (T.project d p)‖ ≤ u*x k * (C.S.a k^i.1/C.S.a k^d)
-- qbt Gram inputs likely deliver, casting units. x depends demand d,basis ratios.
section
variable (L:Origins B 𝓛)
variable {I J E: Type}[Fintype J]{t:ℕ}{b:ℝ}{φ:Filter I} {T' a c : I→ℝ} {m k:I→ℕ}
include L
omit [𝓛.NeBot] in
lemma onload (hT:Tendsto T' φ atTop)(h:Height C.S φ T' k b)(s:J→ℕ)(v:∀ i,T.Field (s i)) :
    ∃ (x : I→ J→ℝ), (∀ i, Bi φ T' (fun j=>x j i) (fun j=> C.S.a (k j)^s i)) ∧ ∀ᶠ i in φ, ∀ l:J, 0<x i l ∧
     ∃ w : C.label (s l), T.project (s l) w=v l ∧ ∃ h:ℕ×ℕ→ C.label (s l), Tendsto h 𝓛 (𝓝 w) ∧
         ∀ᶠ y:ℕ×ℕ in 𝓛, x i l* Spindle.paid C (s l) (k i) y.1 y.2 (h y)≤ fly (G:=G) C.path.levels (s l) (k i):= by
    choose x hx ht using fun l=>L.uses (s l) (v l)
    let y (i:I) (l:J):= x l (k i)* C.S.a (k i)^s l; have hp := cheap_by_ratio hT h.pace
    refine ⟨y,fun i=>?_ ,eventually_all.mpr fun l=>?_⟩
    · have hy: Coins φ T' (fun j=> x i (k j)):= ⟨Bill.enlarge ((hx i).up.of_tendsto h.grows) hp,Bill.enlarge ((hx i).down.of_tendsto h.grows) hp⟩
      simpa only [one_mul] using Bi.mul hy (Bi.refl φ T' (fun j=> C.S.a (k j)^s i))
    filter_upwards [h.grows.eventually (ht l)] with i ⟨hi,w,v,hy,hv,hx⟩; exact ⟨mul_pos hi (pow_pos (C.S.a_pos _) _),v,hv,w,hy,hx⟩
omit [𝓛.NeBot] in
lemma ship (u : I→ℝ) (g:I→ C.label t) -- t unknown
    (e : Bill φ T' u (fun i=>C.S.a (k i)^t * c i))(hT:Tendsto T' φ atTop)(h:Height C.S φ T' k b)
    (hp: ∀ᶠ i in φ,∃ π:Filter (ℕ×ℕ),π.NeBot∧ π≤𝓛 ∧ ∃ x:ℕ×ℕ→ C.label t,Tendsto x π (𝓝 (g i))∧∀ᶠ y in π,quota C t (k i) y.1 y.2 (x y)≤ u i)
    (z:Frame.Row B.rings)(hz:z∈ Frame.limits B.rings t) : Bill φ T' (fun i=> B.representation.coord z t (T.project t (g i))) (fun i=> C.S.a (k i)^z.1*c i):=by
   obtain ⟨x,hx,hv⟩:=L.bounds t; let f i:= x (k i)*(C.S.a (k i)^z.fst/C.S.a (k i)^t)*u i; have H₀: Bill φ T' f (fun i=> C.S.a (k i)^z.fst*c i) := by
      have he := (hx.up.of_tendsto h.grows).enlarge (cheap_by_ratio hT h.pace)
      apply ((Cheap.times he (Bill.same φ T' (fun i=> C.S.a (k i)^z.fst/C.S.a (k i)^t))).mul e).congr (EventuallyEq.refl ..) (Eventually.of_forall ?_)
      intro i; have ht:=C.S.a_pos (k i); field_simp
   refine H₀.norm_le ?_; filter_upwards [hp,h.grows.eventually hv] with i ⟨π,ht,hπ,w,hW,hh⟩ hi
   refine (hi.2 π ht hπ (u i) w (g i) hW hh z hz).trans (le_trans (le_of_eq ?_) (Real.le_norm_self (f i))); unfold f; ring
end
end YM.OPE.Loom
