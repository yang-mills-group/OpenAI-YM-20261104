import YM.GradedFar.Empty

/-! Read also the OPE vector on subarrays. It agrees on using the vacuum labels on
missing Near inputs, even though implementation simply does standard OPE here (without
special-case with other test configuration). Verify the convention. -/
namespace YM.FVA2.GradedFar.Subarray
noncomputable section
open Set Filter Function Real PowerSeries
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Dframe
open scoped Topology BigOperators Classical
variable {G : Gauge} {n m k h : ℕ} {d : Fin n → ℕ} {N : WilsonPrescription G} {simple : G.Simple}
  {T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
  {A : Prescription (Press.portDeck G)} (H : Main.Match N simple T A true)
variable (a : Fin k ↪ Fin n)

section
variable {x : Points n}
def bare (P : Album G) (x : Points n) (u : Inputs G d) (v : Scan G m) (y : Points m) : PowerSeries ℂ :=
  ∑ c : Choices G d, C (combo u c) * party P x y (roll c) v

lemma tactic (a : Choices G d) {ℓ : ℕ} (hd : ∀ i, d i ≤ ℓ) : Guarded (roll a) ℓ :=
  fun i => (Dframe.size_le (a i)).trans (hd i)

include H
lemma bare_coeff (u : Inputs G d) (v : Scan G m) (y : Points m) (h : forest x y ∈ conf (n+m))
    {ℓ : ℕ} (hw : Guarded v ℓ) (hd : ∀ i, d i ≤ ℓ) (j : ℕ) : coeff j (bare (ordinary N) x u v y) =
    book N ℓ _ ⟨forest x y,h⟩ j (Fin.append (installedInputs hd u) (tape v hw)) := by
  unfold bare
  obtain ht := (H.separatedOPE (Teller.logNu 1)).wilson.dimensions
  simp_rw [map_sum,coeff_C_mul, spelled_party _ ht _ _ (tactic _ hd) hw h j]
  exact (expand_near (book N _ _ _ _) u _ hd).symm

lemma no_col (u : Inputs G d) (v : Scan G m) (y : Points m) (h : forest x y ∈ conf (n+m))
    (hu : ∀ i ∉ range a, u i = leaf G _) :
    bare (ordinary N) (config a x) (tuple a u) v y = bare (ordinary N) x u v y := by
  let k0 := Function.Embedding.refl (Fin m); let e := joint a k0
  let z := (⟨forest x y,h⟩ : Scale.Stage (n+m))
  have ht : config e z.val = forest (config a x) y := subforest a k0 x y
  have hy : config e z.val ∈ conf _ := configuration _ z.property
  have h' : forest (config a x) y ∈ conf _ := ht ▸ hy
  let L := totalG v + ∑ i, d i
  have hf : Guarded v L := fun i => (guardT v i).trans (by dsimp [L]; omega)
  have hd (i) : d i ≤ L := by
    obtain p := Finset.single_le_sum (f:=d) (fun i (_:i∈Finset.univ) => Nat.zero_le (d i)) (Finset.mem_univ i)
    dsimp [L]; omega
  ext j
  have hp (i) (hi : i ∉ range a) : installedInputs hd u i = leaf G L := by
    unfold installedInputs; rw [hu i hi]; rfl
  have Hm (i) (hi : i ∉ range k0) : tape v hf i = leaf G L := False.elim (hi ⟨i,rfl⟩)
  have Hr := book_unit H e L z (Fin.append _ _) (lonely a k0 _ _ _ hp Hm) j
  rw [show (⟨config e z.val,_⟩ : Scale.Stage (k+m)) = ⟨forest (config a x) y,h'⟩ from Subtype.ext ht] at Hr
  unfold e at Hr; rw [join] at Hr
  rw [bare_coeff H _ _ _ h hf hd j, bare_coeff H (d:=d ∘ a) _ _ _ h' hf (fun i => hd (a i)) j]
  exact Hr.symm
omit H
private lemma sum_linear (P : Album G) (F Q : Q G → PowerSeries ℂ) (v : Scan G m) (y : Points m) (h : ℕ) :
    Lamp P h y v (F-Q) = Lamp P h y v F - Lamp P h y v Q := by
  simp only [Lamp, Settle, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

include H
lemma bare_fare (u : Inputs G d) (v : Scan G m) (hx : x ∈ conf n)
    {S : Set (Points m)} (hS : IsCompact S) (hy : S ⊆ O.Enh.Outside m) (j h : ℕ) :
    ChargeP (j+1) ((h:ℝ)+1+(totalG v:ℝ)) (fun (i : ↥S) s => bare (ordinary N) x u v
      (squeeze (-s) i.val) - Lamp (ordinary N) h (squeeze (-s) i.val) v (seriesComponent N x u)) := by
  let T e c : PowerSeries ℂ := C (combo u e) * Basket (ordinary N) (roll e) v
    (FarCoefficients (book N) (roll e) x) h x c
  have z (c : Points m) : bare (ordinary N) x u v c - Lamp (ordinary N) h c v (seriesComponent N x u) =
      ∑ e : Choices G d, T e c := by
    simp_rw [T,Basket,mul_sub,Finset.sum_sub_distrib,bare]
    congr 1
    -- reindex
    simp_rw [← LampT, Finset.mul_sum, seriesComponent, Finset.sum_mul]
    rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_assoc ..
  simp_rw [z]
  let hh (i : ↥S) := ((⟨x, mem_singleton _⟩ : ({x} : Set _)), i)
  exact ChargeP.sum _ fun e _ => ChargeP.times (ChargeP.fixed _) ((FO H (roll e) v isCompact_singleton
    (singleton_subset_iff.mpr hx) hS hy j h).pull hh)

/-- Small difference of all projections (uncropped, unconverted Far rows, all Far bases including
empty and horizon-basis choices) at the two vectors for consistency. -/
lemma difference (u : Inputs G d) (v : Scan G m) (hx : x ∈ conf n)
    {S : Set (Points m)} (hS : IsCompact S) (hy : S ⊆ O.Enh.Outside m)
    (hu : ∀ i ∉ range a, u i = leaf G _) (j h : ℕ) :
    ChargeP (j+1) ((h:ℝ)+1+(totalG v:ℝ)) (fun (i : ↥S) s =>
      Lamp (ordinary N) h (squeeze (-s) i.val) v (seriesComponent N x u -
        seriesComponent N (config a x) (tuple a u))) := by
  let w c := bare (ordinary N) (config a x) (tuple a u) v c - Lamp (ordinary N) h c v
    (seriesComponent N (config a x) (tuple a u)) -
    (bare (ordinary N) x u v c - Lamp (ordinary N) h c v (seriesComponent N x u))
  have hw : ChargeP (j+1) ((h:ℝ)+1+(totalG v:ℝ)) (fun (i : ↥S) s => w (squeeze (-s) i.val)) :=
    ChargeP.sub (bare_fare H (tuple a u) v (configuration a hx) hS hy j h)
      (bare_fare H u v hx hS hy j h)
  intro k hk
  refine Rain.raise (hw k hk) ?_
  filter_upwards [eventually_conf isCompact_singleton (singleton_subset_iff.mpr hx) hS hy] with s hs
  intro i
  unfold w
  rw [no_col H a u v _ (hs.1 _ (mem_singleton _) _ i.property) hu, sum_linear, sub_sub_sub_cancel_left]

/-- By uniqueness in the original FVA2 matching package. Since the
original implementation's choice by uniqueness is at homogeneous inputs,
work a bit to apply it to the linear extension (use uniqueness on
modifying the answer on the arity-zero test by the difference). -/
theorem series_vacancies (u : Inputs G d) (hx : x ∈ conf n)
    (hu : ∀ i ∉ range a, u i = leaf G _) : seriesComponent N x u =
      seriesComponent N (config a x) (tuple a u) := by
  let w : Scan G 0 := fun i => i.elim0
  let V := FarCoefficients (book N) w
  let diff := seriesComponent N x u - seriesComponent N (config a x) (tuple a u)
  let X : Fable G 0 := fun i => V i - diff
  have r := (H.separatedOPE (Teller.logNu 1)).wilson
  have ho : Bind.AllC (ordinary N) w V := r.far w
  have hr : Bind.AllC (ordinary N) w X := by
    refine ⟨fun i h => False.elim (h (fun k => k.elim0)), fun i j => ?_, ?_⟩
    · have he (v) : coeff j (X v i)=coeff j (V v i)-coeff j (diff i) := by simp only [X,Pi.sub_apply,map_sub]
      simp_rw [he]; exact (ho.2.1 i j).sub continuousOn_const
    intro W hW hz k j m S v hS hy
    have he (c : Points 0) (y : Points m) : Basket (ordinary N) w v (X c) k c y =
        Basket (ordinary N) w v (V c) k c y + Lamp (ordinary N) k y v diff := by
      unfold X Basket; rw [sum_linear]; abel
    unfold RangeP
    simp_rw [he]
    refine ChargeP.plus (ho.2.2 W hW hz k j m S v hS hy) ?_
    exact ((difference H a u v hx hS hy hu j k).pull Prod.snd).move (Nat.le_succ j)
  have hs : V=X := r.uniqueF w hr
  have hv : V (0:Points 0) - 0 = V 0 - diff := (sub_zero _).trans (congrFun hs _)
  exact sub_eq_zero.mp (sub_right_injective hv.symm)

theorem vector_mask (u : Inputs G d) (hx : x ∈ conf n)
    (hu : ∀ i ∉ range a, u i = leaf G _) (t : ℝ) (p h : ℕ) : cActual N x u h p t =
      cActual N (config a x) (tuple a u) h p t := by
  unfold cActual vector; rw [series_vacancies H a u hx hu]

end

end
end YM.FVA2.GradedFar.Subarray
