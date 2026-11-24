import YM.Integration.WilsonThermometerWeakColumnRead

/-! A paid original group row on a local physical aperture. Occurrences reaching outside
that aperture retain their own original mask and are charged at their purchased long rate. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakGroupAperture
open Function Filter Set MeasureTheory Lattice Wilson RG Source Labels RG12 Extra.Histories
open Next.Rank.Spindle Next.Rank Configuration Normal Rise Source.Drops
open Atlas Beamer Common LiftMark Perch Glimmer Station Asymptotics MvPolynomial
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge} {n:Side} {D b:ℕ} {P:BudgetPoint} {S:Rules G}
variable {ι:Type*} {X:ι→Support n} {A:ι → Config G n→ℂ} {f:ι→ℂ}
variable {rent cash:ℝ} {L:poly (links G (0:Site n) b)}

theorem deposit (H:Summary S P b D X A f rent cash L) (U:Config G n) :
    Summable (fun i=>‖f i*masked P.threshold (X i) (A i) U‖) ∧
      ‖∑' i,f i*masked P.threshold (X i) (A i) U‖≤cash := by
  obtain ⟨e,ce,T⟩:=H
  have term i : ‖f i*masked P.threshold (X i) (A i) U‖≤‖f i‖*e i := by
    rw [norm_mul]
    by_cases ok:Healthy P.threshold (X i) U
    · rw [masked_eq _ _ _ _ ok]; exact mul_le_mul_of_nonneg_left
        ((T.contact i).2 U ok [] (Nat.zero_le _) (by simp)) (norm_nonneg _)
    · rw [masked_ne _ _ _ _ ok,norm_zero,mul_zero]; exact ce.1 i
  have paid:=T.collects.of_nonneg_of_le (fun _=>norm_nonneg _) term
  exact ⟨paid,(norm_tsum_le_tsum_norm paid).trans ((paid.tsum_le_tsum term T.collects).trans ce.2.2)⟩

private theorem mask {t:ℝ} {Y Z:Support n} {U:Config G n} (h:Healthy t Z U)
    (ht:t≤P.threshold) (hY:Y⊆Z) : Healthy P.threshold Y U := by
  apply (Disjoint.mono_left hY h).mono_right
  intro i hi
  obtain ⟨p,hi,hp⟩:=(flags_spec _ _ _).mp hi
  exact (flags_spec _ _ _).mpr ⟨p,hi,ht.trans_lt hp⟩

theorem localWord (H:Summary S P b D X A f rent cash L) (inside:∀ i,X i⊆Spindle.patch b 0)
    (live:2*(b+1)<n.val) (U:Config G n) {t:ℝ} (ht:0<t) (ht':t≤P.threshold)
    (good:Healthy t (Spindle.patch b 0) U) (small:4*b*t≤S.c)
    (radius:2*(4*b*t)/P.threshold≤pane S) :
    let x:=wired P.threshold 0 b U
    ‖(∑' i,f i*masked P.threshold (X i) (A i) U)-text (scan x) L‖≤
      cash*(2*(4*b*t)/P.threshold)^(D+1) := by
  intro x
  obtain ⟨e,ce,T⟩:=H
  obtain ⟨ha,hg,-⟩:=closer S live U good P.threshold P.threshold_pos ht small
  have hv:‖x‖≤pane S:=ha.trans radius
  let U':=net P (0:Site n) b x
  have eqx:Agrees (Spindle.patch b (0:Site n)) U' (spine U 0) := by
    intro j hj hj'
    let i:Dim (0:Site n) b:=⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ j,hj,hj'⟩⟩
    exact (net_in P x i).trans (hg i)
  have eq i : masked P.threshold (X i) (A i) U=A i U' := by
    rw [masked_eq _ _ _ _ (mask good ht' (inside i))]
    exact ((T.smooth i).symmetry (fingers U 0) U).symm.trans
      (((T.smooth i).sites _ _ (agrees_mono eqx (inside i))).symm)
  simp_rw [eq]
  exact ((T.calls x hv).2).trans (mul_le_mul ce.2.2 (pow_le_pow_left₀ (norm_nonneg _) ha _)
    (pow_nonneg (norm_nonneg _) _) (le_trans (tsum_nonneg ce.1) ce.2.2))

theorem farWord (H:Summary S P b D X A f rent cash L) (U:Config G n)
    (x:Space G (0:Site n) b) (hx:‖x‖≤pane S) :
    ‖(∑' i,f i*masked P.threshold (X i) (A i) U)-text (scan x) L‖≤
      cash*(2+‖x‖^(D+1)) := by
  obtain ⟨e,ce,T⟩:=H
  let U':=net P (0:Site n) b x
  have hz:flags P.threshold U'=∅:=voids (occupied P x S hx) le_rfl
  have eq i:masked P.threshold (X i) (A i) U'=A i U' :=
    masked_eq _ _ _ _ (by unfold Healthy;rw [hz];simp)
  have hi:Summary S P b D X A f rent cash L:=⟨e,ce,T⟩
  have here:=(deposit hi U).2
  have there:=(deposit hi U').2
  simp_rw [eq] at there
  have hdiff:=(T.calls x hx).2
  have bill:‖text (scan x) L‖≤cash+cash*‖x‖^(D+1) := by
    have h:=norm_sub_le (∑' i,f i*A i U') ((∑' i,f i*A i U')-text (scan x) L)
    rw [sub_sub_cancel] at h
    exact h.trans (add_le_add there (hdiff.trans
      (mul_le_mul_of_nonneg_right ce.2.2 (pow_nonneg (norm_nonneg _) _))))
  exact (norm_sub_le ..).trans ((add_le_add here bill).trans_eq (by ring))

end YM.Integration.WilsonThermometerWeakGroupAperture
end
