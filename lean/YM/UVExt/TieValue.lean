import YM.UVExt.FiniteFirst
import Mathlib.MeasureTheory.Measure.OpenPos
import YM.UVExt.GridDifference

/-!
# Through projection ties with an actual first-difference bound

The UV and then volume subsequences here are genuine, not asserted full-sequence. The
quantifiers give a **common tail of the retained physical periods** for a fixed compact/list,
after which the UV limit is on the entire retained mesh subsequence at each such period.
We can do this without differentiating the table. Separate all-order argument required.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Grid
open Function Set Filter Extraction Lattice Metric TopologicalSpace
open scoped Topology BigOperators Classical
variable {n : ℕ}
variable {G : Gauge} {C : Family G} {o : Extraction.Order}

def film (C : Family G) {n} (q : Fin n→C.book.Token) (N p : ℕ) (W := ([]:List (Index n))) :=
    interpolate (C.S.a N) (mixed (C.S.a N) W (lifted C N p q))
def chosenValue (F : ℕ→Points n→ℂ) (x : Points n) := if h: ∃ y, Tendsto (fun i=>F i x) atTop (𝓝 y) then h.choose else 0
def picture (C : Family G) (f : Extraction.Order) (p n : ℕ) (q : Fin n→C.book.Token) (W := ([]:List (Index n))) : Points n → ℂ :=
    chosenValue fun i => film C q (f.mesh i) p W
lemma choose_eq {U : ℕ→Points n→ℂ} {x : Points n} {y : ℂ} (h : Tendsto (fun i=> U i x) atTop (𝓝 y)) :
    chosenValue U x=y := by
  have he : ∃ v, Tendsto (fun i=>U i x) atTop (𝓝 v) := ⟨y,h⟩; rw [chosenValue,dif_pos he]; exact tendsto_nhds_unique he.choose_spec h

lemma meets_eq {U : Set (Points n)} {T : ℕ→Points n→ℂ} {s : Points n → ℂ} (h : Meets U T s) :
    Meets U T (chosenValue T) := by
  have hw (x : Points n) (hx : x∈U) : chosenValue T x = s x := choose_eq (Metric.tendsto_nhds.mpr (fun ε hε=>by simpa using h.uniform {x} (singleton_subset_iff.mpr hx) isCompact_singleton _ hε))
  refine ⟨h.continuousOn.congr (fun x hx=>hw x hx),fun K hs hk ε hε=> (h.uniform K hs hk ε hε).mono (fun i hi x hx=>?_)⟩
  rw [hw x (hs hx)]; exact hi x hx

-- Canonical labels obey a uniform first-difference cap on the full mutually separated compact
-- data in the late filter if `first_difference` is prepared; WORK now on the same sequence.
lemma oscillate_lattice (n) (K : Set (Points n)) {F:ℕ→ℕ→Args n→ℂ} {s A : ℝ}
    (hs : 0<s) (hA : 0≤A) (t : ℕ→ℝ) (ht : ∀ i,0<t i) (h₁ : Tendsto t atTop (𝓝 0))
    (hc : ∀ᶠ p : ℕ in atTop, ∀ᶠ i in atTop, ∀ y : Args n, tag (t i) y ∈ cthickening (3*s) K →
      ∀ a, ‖differences (t i) (F p i) a y‖ ≤ A) {ε : ℝ} (hε : 0<ε) : ∃ δ : ℝ, 0<δ ∧ ∀ᶠ p : ℕ in atTop,
      ∀ᶠ i in atTop, ∀ x∈cthickening s K, ∀ y∈cthickening s K, dist x y < δ →
        dist (interpolate (t i) (F p i) x) (interpolate (t i) (F p i) y) ≤ ε := by
  let L : ℝ := (4*n+1)*(A+1)
  let u:=min s (ε/L)
  have hL : 0 < L := by unfold L; positivity
  have hu : 0 < u := lt_min hs (by exact div_pos hε hL)
  refine ⟨u/3,by positivity,?_⟩
  filter_upwards [hc] with p h
  have hD : Tendsto (fun i=> (4*n:ℝ)*(t i)) atTop (𝓝 ((4*n:ℝ)*0)) := h₁.const_mul _
  have He : ∀ᶠ i in atTop, ∀ x : Points n, ∀ w,
      dist (tag (t i) (pos (address (t i) x) w)) x ≤ u/3 :=
    (hD.eventually (gt_mem_nhds (by simpa using (show 0<u/(3:ℝ) from (by positivity))))).mono fun i hi x w=> (corner_dist (ht i) x w).trans hi.le
  filter_upwards [h,He] with i hi hδ x hx y hy hk
  let a:=t i; let X (x:Points n) w:= pos (address a x) w
  have hdist k l : dist (tag a (X x k)) (tag a (X y l)) ≤ u :=
    by
    have ht := dist_triangle (tag a (X x k)) x y; have hy:= dist_triangle (tag a (X x k)) y (tag a (X y l))
    specialize ht; have hm := hδ y l; rw [dist_comm] at hm; dsimp [X,a] at *
    linarith [hm,hδ x k]
  apply bound_dist a (ht i); intro k; rw [dist_comm]; apply bound_dist a (ht i); intro l; rw [dist_comm]
  calc
    _ ≤ A*(4*n)*dist (tag a (X x k)) (tag a (X y l)) := close_lattice (ht i) hA (s:=s) (cthickening (2*s) K) _ _ _ ?_
      ((hdist k l).trans (min_le_left ..)) (fun z hz r=>hi z ?_ r)
    _ ≤ L*u := mul_le_mul (by unfold L; nlinarith) (hdist k l) dist_nonneg hL.le
    _ ≤ ε := (le_div_iff₀' hL).mp (min_le_right ..)
  · have hp : u/3 ≤ s := (div_le_self hu.le (by norm_num)).trans (min_le_left ..)
    have hh := (cthickening_cthickening_subset (le_of_lt hs) (le_of_lt hs) K)
      (mem_cthickening_of_dist_le _ _ s _ hy ((hδ y l).trans hp))
    rwa [show 2*s=s+s by ring]
  have hv := (cthickening_cthickening_subset hs.le (mul_nonneg (by positivity) hs.le) K) hz
  rwa [show 3*s=s+2*s by ring]

lemma film_at_cyclic {M : ℕ→Table C.book} (hl : o.Meshes C M) (q : Fin n→C.book.Token)
    {p : ℕ} {x : Points n} (hx : x∈Cyclic C.S p n) :
    Tendsto (fun i=> film C q (o.mesh i) p [] x) atTop (𝓝 ((M p).read x q)) := by
  have he (k : Corners n) := Order.evaluated o C hl p n q x hx
    (fun i=> pos (address (C.S.a (o.mesh i)) x) k) (tendsto_iff_dist_tendsto_zero.mpr (squeeze_zero (fun _=>dist_nonneg)
    (fun i=> corner_dist (C.S.a_pos _) x k) (by convert (C.S.shrinks.comp o.mesh.cofinal).const_mul (4*n:ℝ) using 1 <;> simp)))
  refine Metric.tendsto_nhds.mpr fun ε hε=>((eventually_all.mpr (fun k=>Metric.tendsto_nhds.mp (he k) (ε/2) (by positivity))).mono ?_)
  intro i hhi
  apply lt_of_le_of_lt (bound_dist (C.S.a (o.mesh i)) (C.S.a_pos _) x _ _ (fun j=>(hhi j).le)) (by linarith)

lemma tie_Cauchy {M : ℕ→Table C.book} (H : FiniteFirstDifference C o) (hl : o.Meshes C M)
    (n) (K : Set (Points n)) (q : Fin n → C.book.Token) (hk : IsCompact K) (hc : K ⊆ conf n) :
    ∀ᶠ p : ℕ in atTop, ∃ U : Set (Points n), K ⊆ U ∧ IsOpen U ∧ Meets U (fun i => film C q (o.mesh i) (o.per p))
       (picture C o (o.per p) n q) := by
  obtain ⟨s,hs,h⟩ := hk.exists_cthickening_subset_open (conf_open _) hc
  obtain ⟨A,hA,hq⟩ := H n q _ hk.cthickening h
  let U:= Metric.thickening (s/3) K
  suffices hw : ∃ V : Set ℕ, (∀ᶠ p in atTop, p ∈ V) ∧ ∀ p∈V, oscillation U (fun i => film C q (o.mesh i) (o.per p)) by
    filter_upwards [hw.choose_spec.1] with p hp
    obtain ⟨_,hg⟩ := growFrom (U:=U) (isOpen_thickening) (hw.choose_spec.2 _ hp) (Cyclic C.S (o.per p) n)
      (MeasureTheory.volume.dense_of_ae (almostCyclic C.S _ _)) (fun x hx=> (film_at_cyclic hl q hx.1).cauchySeq)
    exact ⟨U,self_subset_thickening (by exact (by positivity:0<s/3)) K,isOpen_thickening, meets_eq hg⟩
  refine ⟨{p|∀ᶠ i in atTop, ∀ r, tag (C.S.a (o.mesh i)) r ∈ cthickening s K → ∀ a, ‖differences (C.S.a (o.mesh i)) (lifted C (o.mesh i) (o.per p) q) a r‖≤ A}, ?_,?_⟩
  · filter_upwards [hq] with p hB; filter_upwards [hB] with i hi r hr a
    dsimp [differences,mixed,jump,Work.D03.jump]; rw [norm_mul,Complex.norm_real,norm_inv,Real.norm_of_nonneg (C.S.a_pos _).le]; exact hi _ hr a.1 a.2
  intro p hp T hT ht ε hε
  obtain ⟨δ,hδ,hC⟩ := oscillate_lattice n K (s:=s/3) (A:=A) (by positivity) hA (fun i=>C.S.a (o.mesh i)) (by intro; exact C.S.a_pos _) (C.S.shrinks.comp o.mesh.cofinal)
     (F:=fun _ i=>lifted C (o.mesh i) (o.per p) q) (Eventually.of_forall fun b=> by rw [show 3*(s/3)=s by ring]; exact hp) (ε:=ε/2) (by positivity)
  refine ⟨δ,hδ,hC.exists.choose_spec.mono fun i hi x hx y hy h=>?h⟩
  case h => exact (hi _ (thickening_subset_cthickening _ _ (hT hx)) _ (thickening_subset_cthickening _ _ (hT hy)) h).trans_lt (by linarith)

lemma tie_picture (n : ℕ) (q : Fin n→C.book.Token) (K : Set (Points n)) (hk : IsCompact K) (hc : K ⊆ conf n)
    {M : ℕ→Table C.book} (hl : o.Meshes C M) (H : FiniteFirstDifference C o) :
    ∀ᶠ p : ℕ in atTop, ContinuousOn (picture C o (o.per p) n q) K ∧ TendstoUniformlyOn
      (fun i=>film C q (o.mesh i) (o.per p)) (picture C o (o.per p) n q) atTop K := by
  filter_upwards [tie_Cauchy H hl n K q hk hc] with p hp
  obtain ⟨U,h₁,h₂,h₃⟩ := hp
  refine ⟨h₃.continuousOn.mono h₁,Metric.tendstoUniformlyOn_iff.mpr (fun ε hε=> (h₃.uniform K h₁ hk _ hε).mono ?_)⟩
  intro i hi a ha; rw [dist_comm]; exact hi _ ha

lemma volume_fill (n : ℕ) (q : Fin n→C.book.Token) {T} (ht : ContinuousOn (fun x : Points n=> T.read x q) (conf n))
    {M : ℕ→Table C.book} (hl : RawLimits C o T M) (H : FiniteFirstDifference C o) :
    Meets (conf n) (fun p=>picture C o (o.per p) n q) (fun x : Points n => T.read x q) := by
  let U := generic n
  let D:= fun p=>picture C o (o.per p) n q
  have hd (x) (hx:x∈U) : Tendsto (fun p=>D p x) atTop (𝓝 (T.read x q)) := by
    have hroom := o.per.cofinal.eventually (room C.S (isCompact_singleton (x:=x)))
    apply Metric.tendsto_nhds.mpr; intro ε hε
    filter_upwards [hl.volume n {x} isCompact_singleton (singleton_subset_iff.mpr hx) q ε hε,hroom] with i hi hr
    rw [dist_eq_norm,show D i x=(M (o.per i)).read x q from choose_eq (film_at_cyclic hl.mesh q
      ((no_wrap_tie C.S (hr (mem_singleton x))).2 hx))]; exact hi _ (mem_singleton x)
  suffices hO : oscillation (conf n) D by
    have hu := MeasureTheory.volume.dense_of_ae (almostGeneric n); change Dense U at hu
    obtain ⟨S,h⟩ := growFrom (conf_open n) hO U hu (fun x hx=> (hd x hx.1).cauchySeq)
    refine ⟨ht,fun K hK hk ε hε=>(h.uniform K hK hk ε hε).mono (fun i hi x hx=>?_)⟩
    rw [show T.read x q=S x from ?_]; exact hi _ hx
    have he := (conf_open n).mem_nhds (hK hx)
    suffices ∃ᶠ y : Points n in 𝓝 x, T.read y q=S y from
      tendsto_nhds_unique_of_frequently_eq ((ht x (hK hx)).continuousAt he) ((h.continuousOn x (hK hx)).continuousAt he) this
    refine (mem_closure_iff_frequently.mp (hu x)).mono fun y hy=> tendsto_nhds_unique (hd y hy) ?_
    apply Metric.tendsto_nhds.mpr fun ε hε=>?_
    simpa using h.uniform {y} (singleton_subset_iff.mpr (generic_conf _ hy)) isCompact_singleton ε hε
  intro K hh hk ε hε
  obtain ⟨s,hs,h⟩ := hk.exists_cthickening_subset_open (conf_open _) hh
  obtain ⟨A,hA,hq⟩ := H n q _ hk.cthickening h
  obtain ⟨δ,hδ,hC⟩ := oscillate_lattice n K (s:=s/3) (A:=A) (by positivity) hA (fun i=>C.S.a (o.mesh i)) (by intro; exact C.S.a_pos _) (C.S.shrinks.comp o.mesh.cofinal)
     (F:=fun p i=>lifted C (o.mesh i) (o.per p) q) (by
    filter_upwards [hq] with p h₁; filter_upwards [h₁] with i hi y hy a
    rw [show 3*(s/3)=s by ring] at hy
    unfold differences; rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (C.S.a_pos _).le)]; exact hi _ hy a.1 a.2) (ε:=ε/2) (by positivity)
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hC,tie_Cauchy H hl.mesh n K q hk hh] with p hp hw x hx y hy hd
  suffices ∀ z∈K, Tendsto (fun i=>film C q (o.mesh i) (o.per p) [] z) atTop (𝓝 (D p z)) from
    (le_of_tendsto ((this x hx).dist (this y hy)) (hp.mono fun i hi=> by
      exact hi x (self_subset_cthickening _ hx) y (self_subset_cthickening _ hy) hd)).trans_lt (by linarith)
  obtain ⟨U,h₁,h₂,h₃⟩ := hw
  refine fun z hz=> Metric.tendsto_nhds.mpr fun ε hε=> (h₃.uniform {z} (singleton_subset_iff.mpr (h₁ hz)) isCompact_singleton ε hε).mono ?_
  exact fun i hi=>hi z (mem_singleton z)
end YM.UVExt.Grid
