import YM.Integration.WilsonSignedEquationColumns

/-! Retain the cutoff discount through the entire complex coordinate sum.
This is necessary when the true terminal inverse changes with the cutoff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCutoffEquationRows
open Function Filter Set MeasureTheory Lattice Wilson RG Labels Source Push
open Next.Extract MergeProof PhysicalNext.Repeat.Legato Cells Extra.Histories Motion
open Push.RelayDifference Extra.Multi Accent WilsonSignedReportPrice WilsonCutoffDiscrepancyPrice
open scoped Classical Topology BigOperators
variable {G : Gauge} {C : Family G} {d : ℕ}
variable (V : SectionData (C.labels.level d))
local notation "F" => C.labels.level d
local notation "T" => C.localSection d

theorem column (E : ℕ → ℝ) (m k N p : ℕ) (hk : k≤N) :
    cider C (Bandage.fly C.path.levels) d m k * E N * flight C (-gamma) (N,p) ≤
      conversion C d m k * price C E k N := by
  have hs := (OPE.scale_mono C.S).monotone hk
  rw [price,max_eq_right (sub_nonneg.mpr hs)]
  apply le_trans _ (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
    (le_abs_self (E N)) (Real.exp_pos _).le) (conversion_pos C _ _ _).le)
  have split : Real.exp (-gamma*(C.S.scale N-C.S.scale k)) =
      Real.exp (gamma*C.S.scale k)*Real.exp (-gamma*C.S.scale N) := by
    rw [← Real.exp_add]; congr 1; ring
  apply le_of_eq
  unfold cider WilsonSignedReportPrice.conversion marker flight
  rw [alto_norm,split,div_eq_mul_inv]; ring

theorem physical {P : ℕ → ℕ → (C.label d ≃ₗ[ℂ] C.label d)}
    {U : ℕ → ℕ → (C.labels.level d).Index → C.label d} {E : ℕ → ℝ}
    (H : C.Makes) (valid : V.Sound C.params) (h : Hearth V (Bandage.fly C.path.levels) E P U) :
    ∀ᶠ N in atTop, ∀ p k m, C.ref d ≤ k → k<N → Stock.Tabs.opens C.path.levels 1 m k →
    ∀ hm : m≤N, (↑(V.footprint (0 : Site (C.side N p))) : Set _) ⊆ (center C.S p hm 0).chamber 0 →
      (↑((T).footprint (0 : Site (C.side N p))) : Set _) ⊆ (center C.S p hm 0).chamber 0 →
    ∀ x : C.label d, (center C.S p hm 0).rootTest (C.beta N p)
        (initial T C.path N p (P N p x) 0 - initial V C.path N p x 0) ≤
      orbitCost F * (F).coeffSize x * (conversion C d m k * price C E k N) := by
  filter_upwards [h.stamped] with N ns
  intro p k m hk hN op hm fv ft x
  let t:=center C.S p hm 0
  let B:= conversion C d m k*price C E k N
  let A (i : Motion.Tally F) := WilsonSignedEquationColumns.piece V N p (U N p) i
  have fit (i : Motion.Tally F) : Interior (t.chamber 0) (A i) := by
    have ht := (WilsonSignedEquationColumns.inside T (H.sections d) 0
      (Motion.patch F i.1 (U N p i.2))).enlarges ft
    have hv := (WilsonSignedEquationColumns.inside V valid 0
      (Motion.patch F i.1 (Size.axis F i.2))).enlarges fv
    change Interior _ (fun z => _-_ )
    simpa only [sub_eq_add_neg,neg_one_mul] using ht.plus (hv.scale (-1:ℂ))
  have bnd (i : Motion.Tally F) : t.rootTest (C.beta N p) (A i) ≤ B := by
    have raw := ((ns p).2.2 i.2 k m hk hN op i.1 hm).trans (column (C:=C) (d:=d) E m k N p hN.le)
    change t.rootTest _ (WilsonSignedReportPrice.column V N p (U N p) i.2 i.1) ≤ B at raw
    rw [WilsonSignedEquationColumns.turn V H valid N p (U N p) i] at raw
    exact (unitsC _ t (A i) (C.beta N p)).le.trans raw
  rw [WilsonSignedEquationColumns.expand V N p (P N p) (U N p) (ns p).1 x]
  apply (rooted t (C.beta N p) (seamless H N p) Finset.univ A (chips F x) (fun i _ => fit i)).2.trans
  apply (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (bnd i) (norm_nonneg _)).trans
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (chipcost F x) (mul_nonneg (conversion_pos C _ _ _).le
    (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le))

end YM.Integration.WilsonCutoffEquationRows
