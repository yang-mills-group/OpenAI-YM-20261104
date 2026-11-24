import YM.Integration.WilsonThermometerWeakWickRoom

/-! The nonzero current primary of an arbitrarily placed original weak column.
Each canonical section is paid at its native angular grade. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakPrimary
open Function Set Filter Lattice Wilson RG Source Labels RG12 Extra.Histories
open Next.Rank.Spindle Next.Rank Configuration Normal Rise Source.Drops
open LiftMark MvPolynomial Atlas Tariffs MeasureTheory
open scoped ContDiff Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge} (C:Family G) {d k N p b m D:ℕ}

def weights (t:ℝ) (x:C.label d) : LA C d→ℂ :=
  Sum.elim (fun _=>x 0) (fun i=> ((C.labels.level d).scaled t⁻¹ ((C.labels.level d).core x)) i)

theorem restored (t:ℝ) (ht:0<t) (x:C.label d) :
    ∑ j:LA C d,weights C t x j • (C.labels.level d).scaled t (lightKey C j)=x := by
  let F:=C.labels.level d
  let z:=F.scaled t⁻¹ (F.core x)
  have raw : ∑ j:LA C d,weights C t x j • lightKey C j=x 0 • F.e0+z := by
    rw [Fintype.sum_sum_type,Fintype.sum_unique]
    change x 0 • F.e0+(∑ i:F.Index,z i • Pi.single i 1)=_
    congr 1;funext i;simp [Pi.single_apply]
  simp_rw [← _root_.map_smul]
  rw [← _root_.map_sum,raw,map_add,_root_.map_smul,Frame.scaled_unit,show F.scaled t z=F.core x from F.scaled_inv ht.ne' _]
  ext1 i
  by_cases h:i=0 <;>simp [h,Frame.e0,Frame.core,Function.update]

variable {C}
theorem paid (h:C.Makes) (hk:C.ref d≤k) (hn:k≤N) (x:C.label d) :
    let P:=(C.path.rep N p k).p
    let a:=(C.path.levels.params k).columns
    Wrapper P (verseX C d k p) (verseA C d k p) (weights C P.threshold x)
      (2*(a*(C.labels.level d).coeffSize x)) := by
  let F:=C.labels.level d
  intro P a
  have hp:= (h.wilson.represents N p k hn).vac
  let t:=P.threshold
  have ht:0<t:=P.threshold_pos
  let price : LA C d→ℝ:= Sum.elim (fun _=>1) (fun i:F.Index=>a*t^(F.grades i).2)
  have each (j:LA C d) :
      P.Regular (verseX C d k p j) (verseA C d k p j) ∧
      P.supBounds 0 (verseX C d k p j) (verseA C d k p j) (price j) := by
    cases j with
    | inl z => exact zeroLoan ..
    | inr j =>
      change P.Regular _ _ ∧ P.supBounds _ _ _ (a*P.threshold^(F.grades j).2)
      rw [show P=_ from hp];exact h.priced d k p hk 0 j
  constructor
  · refine ⟨price,each,fun j=>mul_nonneg (norm_nonneg _) (each j).2.1,(hasSum_fintype _).summable,?_⟩
    rw [tsum_fintype,Fintype.sum_sum_type,Fintype.sum_unique]
    change ‖x 0‖*1+(∑ i:F.Index,‖(F.scaled t⁻¹ (F.core x)) i‖*(a*t^(F.grades i).2))≤_
    have cancel (i:F.Index) : ‖(F.scaled t⁻¹ (F.core x)) i‖*(a*t^(F.grades i).2)=a*‖F.core x i‖ := by
      rw [Frame.scaled_apply,norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
      rw [inv_pow];field_simp
    simp_rw [cancel];rw [← Finset.mul_sum,mul_one]
    have h0 : ‖x 0‖ ≤F.coeffSize x :=
      Finset.single_le_sum (fun i _=>norm_nonneg (x i)) (Finset.mem_univ 0)
    have ha:1≤a:=(C.path.levels.params k).columns_ge
    have a0:=zero_le_one.trans ha
    have h1:=h0.trans (le_mul_of_one_le_left (Work.G08.size_nonneg F x) ha)
    have h2:=mul_le_mul_of_nonneg_left (rotate_core F x) a0
    change ‖x 0‖+a*F.coeffSize (F.core x)≤ _
    linarith only [h1,h2]
  · intro j
    cases j with
    | inl z=>exact Finset.mem_singleton_self _
    | inr j=>
      change (0:Site (C.side k p))∈(C.localSection d).stencil.image (fun s=>wrap _ s+0)
      exact Finset.mem_image.mpr ⟨0,(h.sections d).anchored,by rw [map_zero,zero_add]⟩

theorem angular (S:Rules G) (h:C.Makes) (hk:C.ref d≤k) (hn:k≤N)
    (H:Provision C d k N p m b) (x:C.label d) {rent:ℝ}
    (q:poly (Up C k p b)) {e:LA C d→ℝ} (A:Snap G d)
    (read:Teller S (0:Site (C.side k p)) b (C.path.rep N p k).p D
      (verseX C d k p) (verseA C d k p) (weights C (C.path.rep N p k).p.threshold x) e rent q)
    (hd:d≤D) :
    evaluate_ray (walked (snips C.params H.length (C.path.rep N p k).p A) q) d=
      aeval (kp d A) (expose (C.labels.level d) x) := by
  let P:=(C.path.rep N p k).p
  let F:=C.labels.level d
  let v:=snips (o:=0) C.params H.length P A
  let w:=weights C P.threshold x
  obtain ⟨Q,hq,hQ⟩:=read.produced
  obtain ⟨c,l,hc,probes⟩:=shades C.params A d D
  obtain ⟨W,applyW⟩:=costs_ray d v (probes _ _ _ H.length P).1
  have paid (j:LA C d) : W (Q j)=w j * aeval (kp d A) (expose F (F.scaled P.threshold (lightKey C j))) := by
    let u:=fun r=>verseA C d k p j (south C.params 0 A P.threshold r)
    have contained : verseX C d k p j ⊆ Next.Rank.Spindle.patch b 0 :=
      H.contained (h:=h) (hk:=hk) (hN:=hn) (0:C.label d) (Sum.inl j)
    obtain ⟨hv,hp⟩:=industry (v:=(0:C.label d)) h hk hn H A (Sum.inl j)
    obtain ⟨hs,ha⟩:=genuine C.params (verseX C d k p j) (verseA C d k p j) P (w j) (Q j) S _
      (read.smooth j) contained H.length A (mul_nonneg (norm_nonneg _) (read.contact j).1) hd (hQ j).2
    rw [applyW,←show evaluate_ray (w j • u) d=evaluate_ray _ d from trill d
      ((contDiffAt_const (c:=w j)).smul hv) hs ha]
    have hx : evaluate_ray u d=aeval (kp d A) (expose F (F.scaled P.threshold (lightKey C j))) := hp
    rw [←hx]
    have he (i) (hi:i≤d) : iteratedDeriv i (w j • u) 0=w j • iteratedDeriv i u 0 :=
      iteratedDeriv_const_smul (show ContDiffAt ℝ i u 0 from hv.of_le (by exact_mod_cast hi)) _
    change evaluate_ray (w j • u) d=w j • evaluate_ray u d
    unfold evaluate_ray;rw [Finset.smul_sum];refine Finset.sum_congr rfl fun i hi=>?_
    rw [he i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)),smul_comm]
  rw [←applyW,←(value_at hq W).tsum_eq,tsum_fintype,←restored C P.threshold P.threshold_pos x,map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [paid j]; simp only [_root_.map_smul];rfl

end YM.Integration.WilsonThermometerWeakPrimary
end
