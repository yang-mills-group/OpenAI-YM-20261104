import YM.Integration.WilsonCapturedSignedRemainder

/-! The genuine winding charge for the stored coefficient of a
zero-germ physical remainder is flat to every engineering power,
even after paying the original projected split. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedWindingCharge
open Filter Lattice RG Source Labels PhysicalNext.Repeat.Legato
open Trace.Physical Trace.Physical.GermGraph Work.G08 YM.MergeProof YM.MergeProof.Ribbons
open scoped Classical Topology
variable {G : Gauge} (R : Run G) (d : ℕ)

theorem tariff (hG : G.Simple) (D : ℝ) :
    ∀ᶠ u : ℕ in atTop, ∀ p, invoice (C:=R.family) d u p * (1+4*stock R.family u) ≤
      Real.exp (-D*R.family.S.scale u) := by
  let A := max 1 (price (C:=R.family) d)
  have hA : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have cap := ((Note.notes R.family.S (5*A) (by positivity)).mills (Ribbons.fuNote R.family)).outweigh
    (Note.bell_exp R.family.S 1) (by norm_num)
  filter_upwards [cap,cut_flat R.family hG (-(D+1))] with u bound wrap
  intro p
  have hstock : 1 ≤ stock R.family u := (stage R.family u).columns_ge
  have hc : 0 ≤ cut (C:=R.family) p u := (Real.exp_pos _).le
  have hpay : price (C:=R.family) d ≤ A := le_max_right _ _
  change (5*A)*stock R.family u ≤ Real.exp (1*R.family.S.scale u) at bound
  calc
    _ ≤ (A * cut (C:=R.family) p u) * (5*stock R.family u) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hpay hc) (by linarith) (by linarith) (mul_nonneg hA.le hc)
    _ = ((5*A)*stock R.family u)*cut (C:=R.family) p u := by ring
    _ ≤ Real.exp (1*R.family.S.scale u) * Real.exp (-(D+1)*R.family.S.scale u) :=
      mul_le_mul bound (wrap p) hc (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem physical (hG : G.Simple) (D : ℝ) :
    ∀ᶠ u : ℕ in atTop, ∀ p N, u ≤ N →
      ∀ (q : Coefficient (R.family.labels.level d) (R.family.side u p)) {r : ℝ},
        reads (C:=R.family) d N p u q r → (R.family.labels.level d).coeffSize q.x ≤ r →
        ∃ (s : Coefficient (R.family.labels.level d) (R.family.side u p)) (x : R.family.label d),
          page (C:=R.family) d p u s = 0 ∧
          reads (C:=R.family) d N p u s ((1+4*stock R.family u)*r) ∧
          value (C:=R.family) d N p u q - calValues (C:=R.family) d N p u x = value (C:=R.family) d N p u s ∧
          page (C:=R.family) d p u ((R.family.factory d N p).entries u x) = page (C:=R.family) d p u q ∧
          (R.family.labels.level d).coeffSize s.x ≤ Real.exp (-D*R.family.S.scale u)*r := by
  filter_upwards [open_late R.family hG d,tariff R d hG D] with u opening waive
  intro p N hN q r paid old
  obtain ⟨s,x,hs,hzero,actual,hx,_⟩ := fresh_split (d:=d) (N:=N) (p:=p) (i:=u) R.makes (opening p) hN q paid old
  have head := measured_diff d N p u R.makes (opening p).post hN hs
  rw [hzero,zero_sub,count_neg,←mul_assoc] at head
  have hr : 0 ≤ r := le_trans (Finset.sum_nonneg fun _ _ => norm_nonneg _) old
  exact ⟨s,x,hzero,hs,sub_eq_iff_eq_add.mpr actual,(fitting_apply d N p u R.makes (opening p) hN x).symm.trans hx,
    head.trans (mul_le_mul_of_nonneg_right (waive p) hr)⟩

end YM.Integration.WilsonCapturedWindingCharge
