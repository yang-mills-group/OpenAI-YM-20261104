import YM.Pert.Attach.Links

/-! Genuine corrections when aligning two unmasked regular representations. Only equality on the full shared good region is used. Norm smallness still has to be paid before the forest lemma; no estimate at enlarged exponents is inferred. -/

set_option autoImplicit false
noncomputable section
namespace YM.Pert.Attach
open Function Lattice Wilson MeasureTheory RG Finset Filter
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {n : Side} {G : Gauge} (A R:Activities G n) (t:ℝ)

def foot (i:ℕ) := (A.reg i).support ∪ (R.reg i).support
def shiftLog (i:ℕ) (V:Config G n) := masked t (R.reg i).support (R.E i) V - masked t (A.reg i).support (A.E i) V
def readjust : Corrections G n := ⟨foot A R, fun i U=>Real.exp (shiftLog A R t i U)-1⟩

variable {A R t} {s:Signed} {b:Site n}
open Work.H03
lemma healthy_iff {z:Support n} {U:Config G n} : Healthy t (z.image (affine s b)) U ↔ Healthy t z (pull s b U) := by
    unfold Healthy; rw [← flags_send s b _ U]; exact Finset.disjoint_image (fun i j e=>s.act_injective (add_right_cancel e))
lemma mapped {i} (h : A.Moves s b) (U:Config G n) :
    masked t (A.reg (h.ep i)).support (A.E (h.ep i)) U = masked t (A.reg i).support (A.E i) (pull s b U) := by
   rw [h.reg_support]; by_cases he : Healthy t (A.reg i).support (pull s b U)
   · rw [masked_eq _ _ _ _ he, masked_eq _ _ _ _ (healthy_iff.mpr he)]; exact h.valuesE i U
   rw [masked_ne _ _ _ _ he,masked_ne _ _ _ _ fun k=>he (healthy_iff.mp k)]

variable {P Q: BudgetPoint} {δa δr w v:ℝ} (ha:A.Valid Q δa w) (hr:R.RegularFamily P) (ht:Q.threshold=P.threshold)
    (hmotion:∀ s b,∃ (u:A.Moves s b) (v:R.Moves s b),u.ep=v.ep)
    (halign:∀ i U,Healthy P.threshold (foot A R i) U → R.E i U = A.E i U)
include ha hr ht hmotion halign

omit ha hr ht hmotion halign in
lemma masked_reads {p:BudgetPoint} {s:Support n} {E : Config G n → ℝ} (he:p.Regular s E) : UsesFinal p.threshold s (masked p.threshold s E) := by
    intro U V ha hf; by_cases h:Healthy p.threshold s U
    · have hd : Healthy p.threshold s V := Finset.disjoint_iff_inter_eq_empty.mpr (hf ▸ Finset.disjoint_iff_inter_eq_empty.mp h)
      rw [masked_eq _ _ _ _ hd,masked_eq _ _ _ _ h]; exact he.sites _ _ ha
    have hd : ¬Healthy p.threshold s V := fun k=>h (Finset.disjoint_iff_inter_eq_empty.mpr (hf.symm ▸ Finset.disjoint_iff_inter_eq_empty.mp k))
    rw [masked_ne _ _ _ _ hd,masked_ne _ _ _ _ h]
omit ha hr ht hmotion halign in
lemma masked_gauge {p:BudgetPoint}{s:Support n}{E : Config G n → ℝ} (he:p.Regular s E) : GaugeInvariant (masked p.threshold s E) := by
    intro i U; by_cases h:Healthy p.threshold s U
    · rw [masked_eq _ _ _ _ h,masked_eq _ _ _ _ (by unfold Healthy; rwa [gauge_flags])]; exact he.symmetry _ _
    rw [masked_ne _ _ _ _ h,masked_ne _ _ _ _ (by unfold Healthy; rwa [gauge_flags])]

lemma authorized : Prepared P.threshold (readjust A R P.threshold) := by
   refine ⟨fun i U h=>?_,fun i k U=>?_,fun i=>?_,fun i U V h he=>?_,?_⟩
   · change Real.exp (shiftLog _ _ _ i U)-1=0
     unfold shiftLog; rw [masked_eq _ _ _ _ (h.mono_left Finset.subset_union_right),masked_eq _ _ _ _ (h.mono_left Finset.subset_union_left),halign _ U h]; simp
   · change Real.exp (shiftLog A R P.threshold i _)-1= Real.exp (shiftLog A R P.threshold i U)-1
     unfold shiftLog; rw [masked_gauge (hr.smooth i) k U,←ht,masked_gauge (ha.regular.smooth i) k U]
   · refine ((masked_measurable _ _ _ (hr.smooth i).borel).sub (masked_measurable _ _ _ (ha.regular.smooth i).borel)).exp.sub_const 1
   · change Real.exp (shiftLog _ _ _ i U)-1=Real.exp (shiftLog _ _ _ i V)-1
     unfold shiftLog; rw [reads_larger (q:=foot A R i) Finset.subset_union_right (masked_reads (hr.smooth i)) U V h he, ←ht]
     rw [←ht] at he
     rw [reads_larger (q:=foot A R i) Finset.subset_union_left (masked_reads (ha.regular.smooth i)) U V h he]
   intro s c; obtain ⟨u,w,e⟩:= hmotion s c; refine ⟨⟨u.ep,?_,fun i U=>?_⟩⟩
   · intro i; change foot A R (u.ep i) = (foot A R i).image _; unfold foot; rw [image_union,u.reg_support,e,w.reg_support]
   change Real.exp (shiftLog _ _ _ _ U)-1=Real.exp (shiftLog _ _ _ _ (pull s c U))-1
   unfold shiftLog; rw [mapped u, e,mapped w]
end YM.Pert.Attach
