import YM.Integration.FVA1Physical.TwoReset.ClubAssembly

/-!
Use the seam bill ONLY for identifying the coefficients. It lets us take the
whole input sum INSIDE the cover procedure (with arbitrary multiple cover test
period), not extrapolating identity __observe__ finite named inputs. This estimate is
before restoring the real masks. Physical estimates don't use a period dependent
constant for their error.
-/
set_option autoImplicit false
set_option maxHeartbeats 390000
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.FVA1Physical.TwoReset
open Function Filter Finset Lattice RG Precision Tree YM.Wilson QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Sunrise Comparison Comparison.RG02 Comparison.RG02.Bulk
open Next.SectorChange Marker Multi PertExtension.Series Extra.Trajectories
open AllOrder AllOrder.Floe Further.PhysicalPeriodLimitF933 Macrame Shingle
open Primitives.TwoWave Primitives.TwoWave.RealSlice QuadraticLocal.Aperture AllOrder.Ker
open Laurent AllOrder.Ink QuadraticLocal.Echo QuadraticLocal.Poetry Push.AbsoluteSums
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {V ι α : Type} [DecidableEq V] [Fintype V] {c f C : Side}
  {J : Passport f V} {R : Census V} {p : ℕ} {a b : ℝ}
variable (M : ι→Row J R G α) (Q : Ratio c f)
    (B : Press M p) (L : Press.Receipt M B a b)
    (d : ℝ) (h : c.val ∣ C.val)
variable (t : α) (x : Stationary.Link G C) (i : ℕ) (hi : i ≤ p)
variable (D : Layout G) (T : Finset Age) (w : V→ℕ)
variable {σ σ' : ℝ} {o o' : ℕ}
variable {C' F : Side} (h' : C.val ∣ C'.val) (hF : f.val∣F.val)
variable {S : StepData C' F} {P : Clip} {Y' : PathData G} {O : ChartRatio G}
variable (K : Kernel S P Y' O) (A : Forest S.ratio) (ν : S.Choices)
variable (E : S.ratio.count=Q.count)
local notation "Y" => Scene.letters M Q B L d
local notation "δ" => Pages c C
local notation "ζ" => Pages C C'
local notation "paint" => (fun i:ι=> (M i).paint t)
local notation "watches" => (fun j: Solo.Watching M=> Pages c C • ScatterR.drawing M (fun i=> (M i).paint t) i j.val)
local notation "mixed" => (fun j:Club M=> periodic_cluster M Q B j h t x i)
local notation "x'" => convey (coverWin h') x
local notation "cθ" => LinearLetters.mixedTerm (QuadraticLocal.Fk.money D T) (copiesLetter hF M) M paint K A ν (Stationary.arm G C' 1 x') p i
local notation "literal" => copyColor hF M w paint D T
local notation "__observe__" X:max => Order.observe R p (Order.logMarked (Bulk.Fk K A ν X (Stationary.arm G C' 1 x') p)) i

variable [DecidableEq ι]
private abbrev invited (F:Finset ι) : Finset (Solo.Watching M) :=
  F.preimage Subtype.val Subtype.val_injective.injOn

omit [Fintype V] in
private lemma large_request : Tendsto (ScatterR.lounge M) atTop atTop ∧ Tendsto (invited M) atTop atTop := by
  constructor
  · apply tendsto_atTop.mpr; intro S
    filter_upwards [eventually_ge_atTop (S.biUnion (fun i:Club M=>i.val))] with i hi
    exact fun j hj=> Finset.mem_preimage.mpr (Finset.mem_powerset.mpr
      (Finset.Subset.trans (Finset.subset_biUnion_of_mem _ hj) hi))
  apply tendsto_atTop.mpr; intro S
  filter_upwards [eventually_ge_atTop (S.image Subtype.val)] with i hi
  exact fun z hz=> mem_preimage.mpr (hi (mem_image_of_mem _ hz))

omit [Fintype V] in
private lemma attendees (s:Finset ι) : (invited M s).image Subtype.val = ScatterR.opening M s := by
  ext i; constructor
  · intro h; obtain ⟨j,hj,rfl⟩ := mem_image.mp h; exact mem_filter.mpr ⟨mem_preimage.mp hj,j.prop⟩
  intro h; obtain ⟨a,b⟩:= mem_filter.mp h; exact mem_image.mpr ⟨⟨i,b⟩,mem_preimage.mpr a,rfl⟩

variable (H : Air.Staff (Scene.letters M Q B L d) (fun j=> (Scene.letters M Q B L d j).paint t) w σ o)
variable (Hp : Air.Staff M (fun i:ι=> (M i).paint t) w σ' o')
variable (ρ : ℝ) (g:V→ℝ) (hg:∀ i,0<g i)
local notation "fZ" => (fun X:Finset ι => finiteColor hF M w paint D T X)

include Hp h E hi
private lemma authorized (s:Finset ι) : ζ • (∑ j∈invited M s, δ •
    ScatterR.drawing M paint i j.val) + (∑ j∈ScatterR.lounge M s,cθ j) = __observe__ (fZ s) := by
  rw [literal_finite_copy hF M w paint D T K A ν (Stationary.arm G C' 1 x') s (fun i _=> Hp.written i) _ _ hi,
    ← attendees M s,Finset.sum_image Subtype.val_injective.injOn, Finset.smul_sum]
  apply congr_arg (· + _)
  apply Finset.sum_congr rfl; intro j _; rw [smul_smul, pages_fine Q S.ratio E, pages_mul h h']

include hg H
lemma cover_tolerance (hs:SumBudget (fun j:Club M=> Poly.price g
    ((cθ j) - periodic_cluster M Q B j (h.trans h') t (convey (coverWin h') x) i)) ρ) : Poly.price g ((__observe__ literal) - ζ • peek h Y w D T t i x) ≤ ρ := by
  obtain ⟨hc,hM,hp⟩:= repeated_formal_assembly M Q B L d h t x i D T w H
  have U := copied_output hF M w paint D T Hp K A ν (Stationary.arm G C' 1 x') p i
  have hw : Tendsto (fun s:Finset ι=> ζ • ( (∑ j∈ invited M s, watches j) +
      ∑ j∈ScatterR.lounge M s,mixed j)) atTop (𝓝 (ζ • peek h Y w D T t i x)) := by
    rw [hp]
    exact ((hc.hasSum.comp (large_request M).2).add (hM.hasSum.comp (large_request M).1)).const_smul _
  apply le_of_tendsto' ((Poly.price_cont g).continuousAt.tendsto.comp (U.sub hw))
  intro s
  let f(j:Club M):= cθ j - periodic_cluster M Q B j (h.trans h') t x' i
  change Poly.price g ((__observe__ (fZ s)) - ζ • (_+ _)) ≤ _  -- type annot
  suffices he : __observe__ (fZ s) - ζ • ((∑ j∈ invited M s, watches j) + ∑ j∈ScatterR.lounge M s,mixed j) =
      ∑ j∈ScatterR.lounge M s, f j by
    rw [he]; exact (Poly.batch hg _ f).trans (budget_sum hs _)
  rw [← authorized M Q h t x i hi D T w h' hF K A ν E Hp s] -- order
  rw [smul_add,add_sub_add_left_eq_sub,Finset.smul_sum]; unfold f; simp_rw [show ∀ j,periodic_cluster M Q B j (h.trans h') t x' i=ζ • periodic_cluster M Q B j h t x i from fun j=> clusters_scale M Q B h t x i h' j]; rw [Finset.sum_sub_distrib]
end YM.Integration.FVA1Physical.TwoReset
