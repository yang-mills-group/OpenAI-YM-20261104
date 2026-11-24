import YM.RG12.Arche.Align
import YM.MergeProof.East.Pint
/-!
# Relative limits defining the *actual* Gram pivots in S
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Arche
open Function Set Filter Finset Lattice RG Source Next.Rank.Price
open Work.G08 Next.Rank.East
open MergeProof.East PhysicalNext.RankCovariance PhysicalNext.InteractingRank.Soft Next.Rank Next.Rank.Tapes
open scoped Topology BigOperators
variable {G:Gauge} {C:Family G} {d N p k n:ℕ} {M: ∀ d, ℕ → RepChart C d}
  {ϕ:Filter UVIndex} [ϕ.NeBot]
  {hC:C.Makes} (h:Observing C hC ϕ M)
set_option quotPrecheck false
local notation "A"=> C.path.levels
local notation "F"=> C.labels.level d

/-- Holds on the whole simultaneous reader of horizons through d. Prices in l1 mass. -/
structure Comparer (l : Filter UVIndex) (k n : ℕ) (T:ℕ→ℕ→TableL C n) (b:ℝ)
    (Z:∀ i:Fin (n+1),Module.End ℂ (C.label i)) : Prop where
  filter_le : l ≤ ϕ
  limits i v : Tendsto (fun j:UVIndex=> localFit hC k j.1 j.2 (T j.1 j.2 i) b v) l (𝓝 (Z i v))
  ceiling i v : mass _ _ (Z i v) ≤ 2*(2*(A).clock.monitor k)^i.val*b^i.val*mass _ _ v
  base i v : mass _ _ v ≤ 2^i.val*(3/2)*mass _ _ (Z i v)

private lemma acting {d:ℕ} {I:Type} {l:Filter I} {A1:I→RepChart C d} {A2:RepChart C d} (hA:Tendsto A1 l (𝓝 A2)) {V:I→C.label d} {v:C.label d}(hv:Tendsto V l (𝓝 v)): Tendsto (fun i=> A1 i (V i)) l (𝓝 (A2 v)):=
  ((continuous_fst.clm_apply continuous_snd : Continuous fun i:RepChart C _ × C.label d=> i.1 i.2).continuousAt.tendsto.comp
      (hA.prodMk_nhds hv))

omit h [ϕ.NeBot] in -- h.grows used anyway
private lemma bounded_one (hg : Tendsto Prod.fst ϕ atTop) (hr:∀ d ≤ n,C.ref d ≤ k) {T:ℕ→ℕ→TableL C n}
    (ht: ∀ N p, k<N → Charting n k (T N p) N p) (b:ℝ) (hb:1≤b) (i : Fin (n+1)) (u : Ultrafilter UVIndex) (hu: (u:Filter UVIndex) ≤ ϕ) :
    ∃ Z : RepChart C i, Tendsto (fun j:UVIndex=>LinearMap.toContinuousLinearMap (localFit hC k j.1 j.2 (T j.1 j.2 i) b)) (u:Filter _) (𝓝 Z):=by
  let c (i:Fin (n+1)):=2*(2*(A).clock.monitor k : ℝ)^i.val*b^i.val*(((C.labels.level i).extra+1:ℕ):ℝ)
  have hC':0 ≤ (A).clock.monitor k:=(Real.exp_pos _).le; have hN:0≤b:= zero_le_one.trans hb
  apply ultrafilter_converges u _ (c i)
  filter_upwards [(hg.mono_left hu).eventually_gt_atTop k] with j hj
  apply ContinuousLinearMap.opNorm_le_bound _ (by unfold c; positivity)
  intro x; apply (norm_le_mass C _ _).trans
  apply (priced hC (hr _ i.is_le) hj.le (ht j.1 j.2 hj i).1 b hb x).trans
  unfold c; rw [mul_assoc _ _ ‖x‖]; gcongr
  exact mass_le_norm ..

include h
omit [ϕ.NeBot] in
lemma compare_in (hr:∀ d ≤ n,C.ref d ≤ k) {T:ℕ→ℕ→TableL C n}
    (ht: ∀ N p, k<N → Charting n k (T N p) N p) (b:ℝ) (hb:1≤b) (u:Ultrafilter UVIndex) (hu : (u:Filter UVIndex) ≤ ϕ) :
    ∃ Z, Comparer (ϕ:=ϕ) (hC:=hC) (↑u) k n T b Z:=by
  choose Z hz using fun i=> bounded_one (hC:=hC) h.grows hr ht b hb i u hu
  have he(i : Fin (n+1)) (v:C.label i) := acting (hz i) (tendsto_const_nhds (x:=v))
  have he(i : Fin (n+1)) (v:C.label i) := (continuous_mass C _).continuousAt.tendsto.comp (he i v)
  have hw :∀ᶠ j : UVIndex in (u:Filter UVIndex), k < j.1 := (h.grows.mono_left hu).eventually_gt_atTop _
  refine ⟨fun i=> (Z i).toLinearMap,hu,fun i v=> acting (hz i) (tendsto_const_nhds (x:=v)),?_,?_⟩
  · intro i v; exact le_of_tendsto (he i v) (hw.mono fun j hj=>priced hC (hr _ i.is_le) hj.le (ht j.1 j.2 hj i).1 b hb v)
  intro i v; exact ge_of_tendsto ((he i v).const_mul (2^i.val*(3/2))) (hw.mono fun j hj=>unpriced hC (hr _ i.is_le) hj.le (ht j.1 j.2 hj i).1 b hb v)

section columns
variable {l : Filter UVIndex} {k n : ℕ} {T:ℕ→ℕ→TableL C n} {b:ℝ} {Z:∀ i:Fin (n+1),Module.End ℂ (C.label i)}
    (A':Comparer (ϕ:=ϕ) (hC:=hC) l k n T b Z)
def aligned (C:Family G) (M : ∀ d, ℕ → RepChart C d) (k : ℕ) (z:Module.End ℂ (C.label d)) : Module.End ℂ (C.label d) := (((C.S.a k ^ d : ℝ):ℂ)) • ((M d k).toLinearMap.comp z)
include A'
omit h [ϕ.NeBot] in
theorem produced (i:Fin (n+1)) : Function.Bijective (Z i):=by
  have hi: Injective (Z i) := LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr (by
     intro v hv; have hh:=A'.base i v
     rw [hv,show mass C i 0=0 from by simp [mass,Labels.Frame.coeffSize],mul_zero] at hh; exact size_separates _ _ hh))
  exact ⟨hi,LinearMap.surjective_of_injective hi⟩
omit [ϕ.NeBot] in
lemma tends_aligned (i:Fin (n+1)) (v:C.label i) (hr:C.ref i ≤ k) :
    Tendsto (fun j:UVIndex=>ladd C b k j.1 j.2 _ (T j.1 j.2 i) v) l (𝓝 (aligned C M k (Z i) v)):=by
    have he:= (A'.limits i v)
    let t:=(↑(C.S.a k ^ i.val:ℝ):ℂ)
    have hv:= (tendsto_const_nhds (x:=t)).smul (acting ((h.tends i k hr).mono_left A'.filter_le) he)
    exact hv.congr (fun j=> atK_local hC b v)
variable [l.NeBot]
include h
omit [ϕ.NeBot] in
lemma star_aligned (T':∀ N p, k<N → Charting n k (T N p) N p) (i:Fin (n+1)) (v:C.label i) (hr:C.ref i ≤ k) :
    aligned C M k (Z i) (star v)=star (aligned C M k (Z i) v) :=by
    apply tendsto_nhds_unique_of_eventuallyEq (tends_aligned h A' i (star v) hr) ((tends_aligned h A' i v hr).star)
    have hw :∀ᶠ j : UVIndex in l,k<j.1:= (h.grows.mono_left A'.filter_le).eventually_gt_atTop _
    filter_upwards [hw] with j hj using purer hC hr hj.le b (T j.1 j.2 i) (T' j.1 j.2 hj i).1 _
omit [ϕ.NeBot] in
lemma acts_aligned (T':∀ N p, k<N → Charting n k (T N p) N p) (i:Fin (n+1)) (s:Signed) (v:C.label i) (hr:C.ref i ≤ k) :
    aligned C M k (Z i) ((C.labels.level i).act s.ortho v) = (C.labels.level i).act s.ortho (aligned C M k (Z i) v) := by
    let H:=(C.labels.level i).act s.ortho
    apply tendsto_nhds_unique_of_eventuallyEq (tends_aligned h A' i (H v) hr) (g:=fun j:UVIndex=>H (ladd C b k j.1 j.2 _ (T j.1 j.2 i) v)) (H.continuous_of_finiteDimensional.continuousAt.tendsto.comp (tends_aligned h A' i v hr))
    have hw :∀ᶠ j : UVIndex in l,k<j.1:= (h.grows.mono_left A'.filter_le).eventually_gt_atTop _
    filter_upwards [hw] with j hj using rider hC hr hj.le b (T j.1 j.2 i) (T' j.1 j.2 hj i).1 (T' j.1 j.2 hj i).2 s v
end columns
end YM.RG12.Arche
