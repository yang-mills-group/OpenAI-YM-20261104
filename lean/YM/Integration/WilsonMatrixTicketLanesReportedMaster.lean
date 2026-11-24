import YM.Integration.WilsonMatrixTicketLanesReportedPivot
import YM.RG12.Arche.Align
import YM.RG17.Gathers

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesReportedMaster
open Function Filter Set Metric Real OPE Labels RG12 RG17 Extraction Spec Wilson
open RGComparison.Core16.Astage Next.Rank.Price PhysicalNext.Repeat.Legato
open scoped Topology BigOperators Classical
variable {G : Gauge} (R : Run G) {f : Extraction.Order} {S : Table R.family.book}
  (F : Spec.Final R.family f S) (L : RG17.Layout F)

/-- The scalar converting the two actual reporting conventions uses the genuine upper temperature. -/
def color (d m N p : ℕ) (x : R.family.label d) : R.family.label d :=
  (R.family.labels.level d).scaled (shrink R.family m N p) x

theorem atK (d m N p : ℕ) (hm : R.family.ref d ≤ m) (hN : m ≤ N) (x : R.family.label d) :
    Axle.root (C:=R.family) R.makes d m N p (color R d m N p x) =
      ((R.family.S.a m^d : ℝ):ℂ) • RG12.atK R.family R.makes d m (N,p) x := by
  let W := Extra.Histories.Charts.window R.family R.makes d m N p
  let T := RG12.charts R.family R.makes d m (N,p)
  have same (z : R.family.label d) : W z = T z := by
    rw [Extra.Histories.Charts.peek R.family R.makes d N p m hm hN z]
    unfold T RG12.charts
    rw [dif_pos (show R.family.ref d ≤ m ∧ m ≤ (N,p).1 from ⟨hm,hN⟩)]
    rfl
  have inverse (z : R.family.label d) : W.symm z = T.symm z := by
    apply W.injective
    rw [W.apply_symm_apply, same, T.apply_symm_apply]
  let k := shrink R.family m N p
  have kn : k ≠ 0 := (shrink_pos R.family R.makes hN p).ne'
  have cancellation : (R.family.labels.level d).scaled k⁻¹ ((R.family.labels.level d).scaled k x) = x := by
    simpa only [inv_inv] using (R.family.labels.level d).scaled_inv (inv_ne_zero kn) x
  change W.symm (((R.family.S.a m^d : ℝ):ℂ) • (R.family.labels.level d).scaled k⁻¹ ((R.family.labels.level d).scaled k x)) =
    ((R.family.S.a m^d : ℝ):ℂ) • T.symm x
  rw [cancellation, map_smul, inverse]

theorem finite (d : ℕ) (r : ℝ) (w : R.family.label d) (N p : ℕ)
    (hm : R.family.ref d ≤ L.level r) (hN : L.level r ≤ N) :
    Axle.root (C:=R.family) R.makes d (L.level r) N p (color R d (L.level r) N p (L.shift d r w)) =
      RG17.atRef L d r (N,p) w :=
  atK R d (L.level r) N p hm hN (L.shift d r w)

/-- Choose the change of reporting units once on the same original ultrafilter, before every field and test. -/
theorem units (U : Ultrafilter (ℕ×ℕ)) (hu : (U : Filter (ℕ×ℕ)) ≤ f.fuse) :
    ∃ τ : ℕ → ℝ, ∀ m, 0 < τ m ∧ τ m ≤ 2 ∧
      Tendsto (fun z : ℕ×ℕ => shrink R.family m z.1 z.2) (U : Filter (ℕ×ℕ)) (𝓝 (τ m)) := by
  have atStage (m : ℕ) : ∃ t : ℝ, 0 < t ∧ t ≤ 2 ∧
      Tendsto (fun z : ℕ×ℕ => shrink R.family m z.1 z.2) (U : Filter (ℕ×ℕ)) (𝓝 t) := by
    let var (z : ℕ×ℕ) := shrink R.family m z.1 z.2
    let k := 2*R.family.path.levels.clock.monitor m
    have kpos : 0 < k := mul_pos zero_lt_two (exp_pos _)
    have box : Icc k⁻¹ 2 ∈ U.map var := by
      apply Ultrafilter.mem_map.mpr
      filter_upwards [((Cards.largeMesh f).eventually_ge_atTop m).filter_mono hu] with z hz
      have pos := shrink_pos R.family R.makes hz z.2
      have cap := shrink_min R.family R.makes hz z.2
      exact ⟨(inv_anti₀ (inv_pos.mpr pos) cap).trans_eq (inv_inv _),
        RG12.Arche.shrink_current (C:=R.family) (p:=z.2) R.makes hz⟩
    obtain ⟨t,inside,limit⟩ := isCompact_Icc.ultrafilter_le_nhds' (U.map var) box
    exact ⟨t,(inv_pos.mpr kpos).trans_le inside.1,inside.2,limit⟩
  choose τ ht using atStage
  exact ⟨τ,ht⟩

private theorem vary {ι : Type} {l : Filter ι} (d : ℕ) (x : R.family.label d) {s : ι → ℝ} {t : ℝ}
    (h : Tendsto s l (𝓝 t)) :
    Tendsto (fun i => (R.family.labels.level d).scaled (s i) x) l (𝓝 ((R.family.labels.level d).scaled t x)) := by
  apply tendsto_pi_nhds.mpr
  intro j
  simp only [Frame.scaled_apply]
  exact ((Complex.continuous_ofReal.tendsto _).comp (h.pow _)).mul_const _

/-- The very same linear operator limit sends the compensated original reported source to the prescribed master. -/
theorem measured (U : Ultrafilter (ℕ×ℕ)) (hu : (U : Filter (ℕ×ℕ)) ≤ f.fuse)
    (cut : (U : Filter (ℕ×ℕ)) ≤ L.lens) (A : Axle.TransferLimit R.family R.makes U)
    (τ : ℕ → ℝ) (limit : ∀ m, Tendsto (fun z : ℕ×ℕ => shrink R.family m z.1 z.2) (U : Filter (ℕ×ℕ)) (𝓝 (τ m)))
    (d : ℕ) (r : ℝ) (w : R.family.label d) (hm : R.family.ref d ≤ L.level r) :
    let x := (R.family.labels.level d).scaled (τ (L.level r)) (L.shift d r w)
    Axle.full F d A (L.level r) x = RG17.master L d r w := by
  intro x
  let m := L.level r
  let v := L.shift d r w
  have hx : Tendsto (fun z : ℕ×ℕ => color R d m z.1 z.2 v) (U : Filter (ℕ×ℕ)) (𝓝 x) :=
    vary R d v (limit m)
  let evaluate : (R.family.label d →L[ℂ] R.family.label d) × R.family.label d → R.family.label d :=
    fun q => q.1 q.2
  have smooth : Continuous evaluate := continuous_fst.clm_apply continuous_snd
  have pair : Tendsto (fun z : ℕ×ℕ => Axle.root (C:=R.family) R.makes d m z.1 z.2 (color R d m z.1 z.2 v))
      (U : Filter (ℕ×ℕ)) (𝓝 (A.fieldMap d m x)) := (smooth.tendsto _).comp ((A.lim d m hm).prodMk_nhds hx)
  have same : (fun z : ℕ×ℕ => Axle.root (C:=R.family) R.makes d m z.1 z.2 (color R d m z.1 z.2 v)) =ᶠ[U]
      (fun z : ℕ×ℕ => RG17.atRef L d r z w) := by
    filter_upwards [((Cards.largeMesh f).eventually_ge_atTop m).filter_mono hu] with z hz
    exact finite R F L d r w z.1 z.2 hm hz
  have fixed := RG17.tendsRef (L:=L) (D:=d) (r:=r) (u:=(U:Filter (ℕ×ℕ))) (v:=fun _ => w) cut tendsto_const_nhds hm
  have join := tendsto_nhds_unique (pair.congr' same) fixed
  exact (congrArg (S.project d) join).trans (RG17.payRef (D:=d) (r:=r) L w)

end YM.Integration.WilsonMatrixTicketLanesReportedMaster
