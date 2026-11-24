import YM.Integration.MSExteriorTestProjection

/-! Common translations of the complete independent MS joining recursion and
the compact tested OPE at the original exterior center. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.MSExteriorOrigins
open Set Function Filter Finset MeasureTheory Real MS
open Plane Koszul Heat Tone Momentum Landau Detect Book High Frame Flux Osc Fiddle Snap City Wire Wind Signal Latch Job Belt
open Garment Outlook Land Pearl Train Dock Emit Menus Book.Convolve Rake Rake.Geo Local.Physical Tide Dial Vane
open Pert.Position RG11.Neighborhood MSExteriorDilation MSExteriorCompactTests MSExteriorTestProjection
open scoped Topology BigOperators Classical
variable {G : Gauge} {I W : Type} [LinearOrder W]

abbrev transported (b : I → QP) (x : Position W I) : Position W I := fun w i => b i + x w i
abbrev shiftedBy {l : ℕ} (b : QP) (x : Fin l → QP) : Fin l → QP := fun w => b + x w

theorem root (b : I → QP) (x : Position W I) (s : Finset W) (hs : s.Nonempty) :
    rootX (transported b x) s = b + rootX x s := by
  simp only [rootX,dif_pos hs]
  rfl

/-- The actual joining source is unchanged as a whole external-momentum field,
before any integral over running cutoff is taken. -/
theorem source (b : I → QP) (x : Position W I) (μ : I → Measure QP) (K L : Planet G I)
    (F H : Site G I) (A : Dance G I W) (n : ℕ) (s : Finset W) :
    multi μ (transported b x) K L F H A n s = multi μ x K L F H A n s := by
  unfold multi
  apply congrArg (fun z : Glade G I => lonely K F H n + z)
  refine Finset.sum_congr rfl fun t ht => ?_
  obtain ⟨hle,hn,_,_⟩ := n_small ht
  have he : rootX (transported b x) t-rootX (transported b x) s = rootX x t-rootX x s := by
    rw [root b x t hn,root b x s (hn.mono hle.le)]
    abel
  exact congrArg (fun z : I → QP => ∑ j ∈ HasAntidiagonal.antidiagonal n,
    regionC μ z L (A t j.1) (A (s \ t) j.2)) he

theorem field_record (b : I → QP) (x : Position W I) (μ : I → Measure QP) (K L : Planet G I)
    (F : Site G I) (g : W → Site G I) (A : Dance G I W) :
    Fields (transported b x) μ K L F g A ↔ Fields x μ K L F g A := by
  simp only [Fields,source]

variable {B : Deck G} {Q : Booked B} (M : MS_Data G Q) (w : W → Label B)

/-- The actual fallback and chosen ordinary field agree at all configurations,
including collisions, because the two predicates for the original solution coincide. -/
theorem ordinary (b : QP) (x : W → QP) (μ : ℝ) :
    spine M w μ (fun j => b+x j) = spine M w μ x := by
  let select (P : Dance G Unit W → Prop) : Dance G Unit W := if h : ∃ Y, P Y then h.choose else 0
  change select (fun U => DOrd Q (frameF Unit μ) M w (fun j _ => b+x j) U) =
    select (fun U => DOrd Q (frameF Unit μ) M w (fun j _ => x j) U)
  apply congrArg select
  exact funext fun U => propext (field_record (fun _ : Unit => b) (fun j (_ : Unit) => x j) _ _ _ _ _ U)

theorem vacuum (b : QP) (x : W → QP) (μ : ℝ) (s : Finset W) (n : ℕ) :
    Dial.tour M w μ (fun j => b+x j) s n = Dial.tour M w μ x s n := by
  unfold Dial.tour Dial.book
  rw [ordinary M w b x μ]

variable {n m H : ℕ}

theorem row (R : Fin n → Label B) (b : QP) (x : Fin n → QP) (μ : ℝ) (k : ℕ) :
    moment M R μ (shiftedBy b x) k = moment M R μ x k := vacuum M R b x μ univ k

abbrev relative (y : Tail m) : Fin m → QP := fun a => Theater.out (y.y a - y.c)

theorem join_positions (y : Tail m) (s : ℝ) (x : Points n) :
    positions (driven (exp (-s)) x y) = shiftedBy (Theater.out y.c) (contracted s (positions x) (relative y)) := by
  funext j
  induction j using Fin.addCases with
  | left i => simp [positions,driven,points,shiftedBy,contracted,stretch,Theater.out,map_add,map_smul]
  | right i => simp [positions,driven,points,shiftedBy,contracted,relative,Theater.out,map_sub]

theorem closed_positions (y : Tail m) : positions (close y) = shiftedBy (Theater.out y.c) (origin (relative y)) := by
  funext j
  induction j using Fin.addCases <;> simp [positions,close,coupled,points,shiftedBy,origin,relative,Theater.out,map_sub]

theorem remote (y : Tail m) : Injective (origin (relative y)) := by
  intro i j h
  apply OPEMSReport.close_conf y
  apply Theater.out.injective
  change positions (close y) i = positions (close y) j
  rw [closed_positions]
  exact congrArg (Theater.out y.c + ·) h

variable (R : Fin n → Label B) (L : Fin m → Label B)

theorem shift_profile (f : Test n) (C : Points n → MSExteriorDilation.Table B H) (μ s : ℝ) (k : ℕ)
    (q : Points n → Fin (n+m) → QP) (u : Fin (1+m) → QP) (b : QP) :
    difference M R L f C μ s (fun x => shiftedBy b (q x)) (shiftedBy b u) k = difference M R L f C μ s q u k := by
  simp only [difference,row]

theorem original (f : Test n) (C : Points n → MSExteriorDilation.Table B H) (μ s : ℝ) (k : ℕ) (y : Tail m) :
    difference M R L f C μ s (fun x => positions (driven (exp (-s)) x y)) (positions (close y)) k =
      difference M R L f C μ s (fun x => contracted s (positions x) (relative y)) (origin (relative y)) k := by
  simp_rw [join_positions,closed_positions]
  exact shift_profile M R L f C μ s k _ _ _

/-- The compact remainder is uniform across actual arbitrary centers. Compactness
is required only on the relative exterior shape family. -/
theorem tested_original (f : Test n) (C : Points n → MSExteriorDilation.Table B H) (Y : Set (Tail m))
    (hy : IsCompact (relative '' Y)) (μ : ℝ) (k : ℕ)
    (hc : ∀ a j, j ≤ k → ∀ v : ℝ, ContinuousOn (fun z => C z a j v) (conf n))
    {K : ℝ} (hK : 0 ≤ K) (j : ℕ)
    (hf : ∀ᶠ s : ℝ in atTop, ∀ x ∈ tsupport f, ∀ y ∈ Y, ∀ v : ℝ,
      ‖far M R L (C x) v (receding s (positions x) (relative y)) (origin (stretch s (relative y))) k‖ ≤
        K * (((1+|v|)*(1+s))^j * exp (-((H:ℝ)+1+weight L)*s))) :
    ∀ᶠ s : ℝ in atTop, ∀ y ∈ Y,
      ‖difference M R L f C μ s (fun x => positions (driven (exp (-s)) x y)) (positions (close y)) k‖ ≤
        (∫ x, ‖f x‖) * ((K*(1+|μ|)^j) * (exp (((weight R : ℝ)-H-1)*s) * (1+|s|)^(2*j))) := by
  have ht := measured M R L f C (relative '' Y) hy (fun _ ⟨y,_,e⟩ => e ▸ remote y) μ k hc hK j
    (hf.mono fun s hs x hx _ ⟨y,hy,e⟩ v => e ▸ hs x hx y hy v)
  filter_upwards [ht] with s hs y hy
  rw [original]
  exact hs _ ⟨y,hy,rfl⟩

end YM.Integration.MSExteriorOrigins
