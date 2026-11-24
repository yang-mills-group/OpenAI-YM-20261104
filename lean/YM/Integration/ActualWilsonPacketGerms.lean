import YM.Integration.LocalComparisonPackets
import YM.Integration.WilsonLocalKernelMoments
import YM.Work.G05.Taylor
import YM.Next.FOUNDATIONS.Readout

/-! Physical chart germs of the original, charged one-mark curvature packet rows. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualWilsonPacketGerms
open Lattice Wilson RG Marker Function Finset MeasureTheory Source Labels
open Comparison.Density.RenderM Comparison.Density.RenderM.Token
open Pert.Attach Push.AbsoluteSums Extra.Iteration
open Progress.DirectedRecipe AnalyticBridge.VerifiedReset AnalyticBridge.VerifiedReset.Collection
open WilsonStartup Averaging Geo UVNext.CouplingReset Next.Scheduling Precision Next.Foundations
open AnalyticBridge.SectorAffine.Offset FreeResolvent.Affine FreeResolvent.TestD
open LocalComparison Classical
open scoped Classical Topology BigOperators Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {V : Type} [DecidableEq V] {n : Side}
  {D : V → ComparisonDensity.Address.Orbit} {R : Census V} {P : MarkedPackets D G n R}
  {p : BudgetPoint} {address : V → Support n}
  {region : Comparison.Density.Testing.Region (fun v => (D v).Mood) n} {w : V → ℝ}
  {g width budget : ℝ} {off slope : ℕ}
  (H : P.Paid p address region w g width budget off slope)
  {i : ℕ} {T : Token G n (fun v => (D v).Mood) (P.rank i)} (hT : P.packet i=some T)

include H hT in
private theorem invariant (z : TestSpace D) : (T.re z).Invariant ∧ (T.im z).Invariant := by
  refine ⟨fun a U => ?_,fun a U => ?_⟩
  · rw [←(T.real_and_imag ..).1,H.symmetry i T hT z,(T.real_and_imag ..).1]
  · rw [←(T.real_and_imag ..).2,H.symmetry i T hT z,(T.real_and_imag ..).2]

include H hT in
theorem regular_at (B : BudgetPoint) (z : TestSpace D) : B.Regular T.plot (T.read z) := by
  obtain ⟨hr,hi⟩ := invariant H hT z
  rw [T.reading z]
  refine regular_larger (regular_add (regular_mapped Complex.ofRealCLM ?_)
    (regular_smul _ (regular_mapped Complex.ofRealCLM ?_))) (H.paths i T hT z).2
  · exact Derivs.canonical_regular _ _ _ hr
  exact Derivs.canonical_regular _ _ _ hi

include H hT in
theorem regular_term (B : BudgetPoint) (z : TestSpace D) : B.Regular T.plot (fun U => P.term z g U i) := by
  have he : (fun U => P.term z g U i)=((g:ℂ)^P.power i) • T.read z := by
    funext U
    simp [MarkedPackets.term,hT]
  rw [he]
  exact regular_smul _ (regular_at H hT B z)

include H hT in
private theorem magnitude (x : IndependentTests D) :
    (T.re (testInclusion D x)).magnitude≤T.coin ∧ (T.im (testInclusion D x)).magnitude≤T.coin := by
  have h := (H.coefficient i T hT).2 x
  exact ⟨(Finset.sum_le_sum (fun j _ => Complex.abs_re_le_norm (T.gem j (testInclusion D x)))).trans h,
    (Finset.sum_le_sum (fun j _ => Complex.abs_im_le_norm (T.gem j (testInclusion D x)))).trans h⟩

include H hT in
/-- Native gauge-covariant support and its derivatives at the actual packet root. -/
theorem rooted (B : BudgetPoint) (x : IndependentTests D) : B.supBounds T.root T.plot (T.read (testInclusion D x)) (units B T) := by
  let z := testInclusion D x
  obtain ⟨hr,hi⟩ := invariant H hT z
  have h := (H.paths i T hT z)
  obtain ⟨hrc,hic⟩ := magnitude H hT x
  let F := T.re z
  let K := T.im z
  have ht := Derivs.canonical_regular F T.root B hr
  have hf := Derivs.canonical_regular K T.root B hi
  rw [T.reading (testInclusion D x)]
  apply bound_larger (Push.Local.bound_weaken (bound_add (regular_mapped Complex.ofRealCLM ht)
    (regular_smul _ (regular_mapped Complex.ofRealCLM hf)) ((sup_real ht).2 (Wages.total B F T.root))
    (bound_smul _ ((sup_real hf).2 (Wages.total B K T.root)))) ?_) h.2
  rw [Complex.norm_I,one_mul]
  refine (add_le_add (pays_can G B F h.1 hrc) (pays_can G B K h.1 hic)).trans_eq ?_
  unfold units subtotal
  ring

include H hT in
/-- The same coupled, signed row can be rooted at any actual address of its retained mark. -/
theorem address_germ (B : BudgetPoint) (x : IndependentTests D) (v : V) (hv : v∈(P.mode i).val)
    (o : Site n) (ho : o∈address v) :
    B.supBounds o T.plot (fun U => P.term (testInclusion D x) g U i)
      (‖(g:ℂ)^P.power i‖*touched B T) := by
  let z := testInclusion D x
  have hK := rooted H hT B x
  have ht : T.root∈T.plot := (H.paths i T hT z).2 (mem_image.mpr ⟨0,mem_insert_self ..,by simp⟩)
  have he := Corona.extent T.plot B.B ht (H.addresses i T hT v hv ho)
  have had : B.supBounds o T.plot (T.read z) (touched B T) := by
    refine Push.Local.bound_weaken (Push.Local.bound_shift hK (regular_at H hT B z) _) (mul_le_mul_of_nonneg_right ?_ hK.1)
    rw [pow_mul]
    gcongr
    exact he
  have raw := bound_smul ((g:ℂ)^P.power i) had
  have hu : (fun U => P.term z g U i)=((g:ℂ)^P.power i) • T.read z := by
    funext U
    simp [MarkedPackets.term,hT]
  rw [show (fun U => P.term (testInclusion D x) g U i) = ((g:ℂ)^P.power i) • T.read z from hu]
  exact raw

/-- True charged rows have zero flat derivatives strictly below their actual curvature rank. -/
theorem valuation (z : TestSpace D) {k : ℕ} (hk : k<P.rank i) :
    iteratedFDeriv ℝ k (T.read z ∘ increment 1) 0 = 0 := T.order_z z hk

include H hT in
/-- Original real and imaginary atoms of the tester are evaluated on the same field and direction. -/
theorem chart (x : IndependentTests D) (k : ℕ) (A : Directions G n) (hA : ‖A‖≤1) :
    Through k (T.read (testInclusion D x) ∘ increment 1) A (stamp k T) := by
  let z := testInclusion D x
  let c := T.coin*Comparison.Density.Render.entry G (P.rank i) k*(1+(T.fall:ℝ))^(k*P.rank i)
  have hp := H.paths i T hT z
  obtain ⟨hR,hI⟩ := magnitude H hT x
  have hE : 0≤ Comparison.Density.Render.entry G (P.rank i) k :=
    pow_nonneg (mul_nonneg (Comparison.Density.Render.code_nn _) (Comparison.Density.Render.pass_nn ..)) _
  have hc := (H.coefficient i T hT).1
  have atom (F : Atom G (P.rank i)) (hl : F.length≤T.fall) (hj : F.magnitude≤T.coin) :
      Through k (fun a : Directions G n => F.unmasked (increment 1 a) T.root) A c := by
    have h : 0≤F.magnitude := Finset.sum_nonneg fun _ _ => abs_nonneg _
    apply (Comparison.Density.Render.reserved F T.root hA).mono
    unfold Comparison.Density.Render.fareAt c
    gcongr
  let f := fun a : Directions G n => (T.re z).unmasked (increment 1 a) T.root
  let h := fun a : Directions G n => (T.im z).unmasked (increment 1 a) T.root
  let I := Complex.I • Complex.ofRealCLM
  have hr : Through k f A c := atom (T.re z) hp.1 hR
  have hi : Through k h A c := atom (T.im z) hp.1 hI
  have hcast : ‖Complex.ofRealCLM‖≤1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => by simp
  have hi' : ‖I‖≤1 := by simpa only [I,norm_smul,Complex.norm_I,one_mul] using hcast
  have h1 : Through k (Complex.ofRealCLM ∘ f) A c :=
    (Comparison.Density.Render.abroad hr _).mono (mul_le_of_le_one_left hr.nonneg hcast)
  have h2 : Through k (I ∘ h) A c :=
    (Comparison.Density.Render.abroad hi I).mono (mul_le_of_le_one_left hi.nonneg hi')
  have he : T.read z ∘ increment 1 = (Complex.ofRealCLM ∘ f)+(I ∘ h) := by
    funext a
    rw [T.reading z]
    rfl
  rw [show T.read (testInclusion D x) ∘ increment 1 = _ from he]
  refine ⟨h1.smooth.add h2.smooth,fun j hj => ?_⟩
  rw [iteratedFDeriv_add_apply (Comparison.Density.Transport.through_le h1 hj).smooth (Comparison.Density.Transport.through_le h2 hj).smooth]
  exact (norm_add_le ..).trans ((add_le_add (h1.pay _ hj) (h2.pay _ hj)).trans_eq (by change c+c=2*c;ring))

include H hT in
theorem flat_term (x : IndependentTests D) {k : ℕ} (hk : k<P.rank i) :
    iteratedFDeriv ℝ k ((fun U => P.term (testInclusion D x) g U i) ∘ increment 1) 0=0 := by
  let L : ℂ →L[ℝ] ℂ := ((g:ℂ)^P.power i) • ContinuousLinearMap.id ℝ ℂ
  have he : (fun U => P.term (testInclusion D x) g U i) ∘ increment 1 = L ∘ (T.read (testInclusion D x) ∘ increment 1) := by
    funext a
    simp [L,MarkedPackets.term,hT]
  rw [he,L.iteratedFDeriv_comp_left (chart H hT x k 0 (by simp)).smooth le_rfl,T.order_z _ hk]
  ext
  simp


include H hT in
/-- Every actual finite holonomy reading is zero for this high-rank charged row. -/
theorem fit_with_read (W : Rep G n) (x : IndependentTests D) (d : ℕ) (hd : d<P.rank i)
    (L : Hol G) (v : V) (hv : v∈(P.mode i).val) (o : Site n) (ho : o∈address v) :
    Extra.Histories.RegFit W o d L T.plot (fun U => P.term (testInclusion D x) g U i) ∧
      L.PiVanish d o (fun U => P.term (testInclusion D x) g U i) := by
  let f := fun U => P.term (testInclusion D x) g U i
  let F := f ∘ increment 1
  have hr := regular_term H hT W.p (testInclusion D x)
  have hj (j : ℕ) (hjd : j≤d) : iteratedFDeriv ℝ j F 0=0 := flat_term H hT x (hjd.trans_lt hd)
  let Z : ℂ →L[ℝ] ℂ := ((g:ℂ)^P.power i) • ContinuousLinearMap.id ℝ ℂ
  have he : F = Z ∘ (T.read (testInclusion D x) ∘ increment 1) := by
    funext a
    simp [F,f,Z,MarkedPackets.term,hT]
  have hF : ContDiffAt ℝ (d:WithTop ℕ∞) F 0 := by
    rw [he]
    exact Z.contDiff.contDiffAt.comp 0 (chart H hT x d 0 (by simp)).smooth
  have hproj (J : Jet G) : ContDiffAt ℝ (d:WithTop ℕ∞) (fun t => f (L.testLinks d o J t)) 0 ∧
      ∀ j≤d,iteratedDeriv j (fun t => f (L.testLinks d o J t)) 0=0 := by
    let t := testLog L d o J
    have ht : ContDiffAt ℝ (d:WithTop ℕ∞) t 0 := (testLog_diff ..).of_le le_top
    have ht0 : t 0=0 := testLog_zero ..
    have hF' : ContDiffAt ℝ (d:WithTop ℕ∞) F (t 0) := by rw [ht0];exact hF
    have he' : (fun s => f (L.testLinks d o J s))=ᶠ[𝓝 0] F ∘ t :=
      (increment_testLog L d o J).mono fun s hs => congrArg f hs
    refine ⟨(hF'.comp 0 ht).congr_of_eventuallyEq he',fun j h => ?_⟩
    rw [iteratedDeriv_eq_iteratedFDeriv,(he'.iteratedFDeriv ℝ j).eq_of_nhds]
    have hz : ContDiffAt ℝ (d:WithTop ℕ∞) (0 : Directions G n→ℂ) (t 0) := contDiffAt_const
    have hj' : ∀ k≤d,iteratedFDeriv ℝ k F (t 0)=iteratedFDeriv ℝ k (0 : Directions G n→ℂ) (t 0) := by
      rw [ht0]
      intro k hk
      rw [hj k hk]
      by_cases h0 : k=0
      · subst k; simp_rw [iteratedFDeriv_zero_eq_comp];rfl
      ext;rw [Pi.zero_def,iteratedFDeriv_const_of_ne h0];rfl
    rw [Work.G05.jets_comp ht ht hF' hz rfl (fun _ _ => rfl) hj' j h]
    by_cases h0 : j=0
    · subst j;simp_rw [iteratedFDeriv_zero_eq_comp];rfl
    change iteratedFDeriv ℝ j (fun _ : ℝ => (0:ℂ)) 0 _=0
    rw [iteratedFDeriv_const_of_ne h0];rfl
  refine ⟨⟨hr,H.addresses i T hT v hv ho,?_,fun _ J => hproj J⟩,fun J => hproj J⟩
  simpa only [iteratedDeriv_zero,test_one] using! (hproj 0).2 0 (Nat.zero_le d)

include H hT in
theorem fit (W : Rep G n) (x : IndependentTests D) (d : ℕ) (hd : d<P.rank i)
    (L : Hol G) (v : V) (hv : v∈(P.mode i).val) (o : Site n) (ho : o∈address v) :
    Extra.Histories.RegFit W o d L T.plot (fun U => P.term (testInclusion D x) g U i) :=
  (fit_with_read H hT W x d hd L v hv o ho).1

include H hT in
/-- Native ordinary jet on the literal coupled packet field. -/
theorem chart_term (x : IndependentTests D) (k : ℕ) (A : Directions G n) (hA : ‖A‖≤1) :
    Through k ((fun U => P.term (testInclusion D x) g U i) ∘ increment 1) A
      (‖(g:ℂ)^P.power i‖*stamp k T) := by
  let L : ℂ →L[ℝ] ℂ := ((g:ℂ)^P.power i) • ContinuousLinearMap.id ℝ ℂ
  have hL : ‖L‖≤‖(g:ℂ)^P.power i‖ := ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun u => by
    change ‖((g:ℂ)^P.power i) • u‖≤‖(g:ℂ)^P.power i‖*‖u‖
    rw [norm_smul]
  have he : (fun U => P.term (testInclusion D x) g U i) ∘ increment 1 = L ∘ (T.read (testInclusion D x) ∘ increment 1) := by
    funext a
    simp [L,MarkedPackets.term,hT]
  rw [he]
  have h := chart H hT x k A hA
  exact (Comparison.Density.Render.abroad h L).mono (mul_le_mul_of_nonneg_right hL h.nonneg)

def amplifier (G : Gauge) (cap k : ℕ) (width : ℝ) :=
  (∑ r∈range (cap+1),2*Comparison.Density.Render.entry G r k)*
    (((k*cap).factorial:ℝ)/(min width 1)^(k*cap))*Real.exp (min width 1)

private theorem entry_nonneg (G : Gauge) (r k : ℕ) : 0≤ Comparison.Density.Render.entry G r k :=
  pow_nonneg (mul_nonneg (Comparison.Density.Render.code_nn _) (Comparison.Density.Render.pass_nn ..)) _

theorem amplifier_nonneg (G : Gauge) (cap k : ℕ) {a : ℝ} (ha : 0<a) : 0≤amplifier G cap k a := by
  have h : 0≤∑ r∈range (cap+1),2*Comparison.Density.Render.entry G r k :=
    sum_nonneg fun r _ => mul_nonneg (by norm_num) (entry_nonneg G r k)
  have hp : 0 < min a 1 := lt_min ha zero_lt_one
  unfold amplifier
  positivity

theorem cost (G : Gauge) (cap k : ℕ) {width s : ℝ} (hw : 0 < width) (hs : 1 ≤ s) (hinv : width⁻¹ ≤ s) :
    amplifier G cap k width ≤
      ((∑ r∈range (cap+1),2*Comparison.Density.Render.entry G r k)*((k*cap).factorial:ℝ)*Real.exp 1)*s^(k*cap) := by
  let a := min width 1
  have ha : a⁻¹≤ s := by
    rcases le_total width 1 with h|h
    · simpa only [a,min_eq_left h] using hinv
    · simpa only [a,min_eq_right h,inv_one] using hs
  have hd : (a⁻¹)^(k*cap)≤ s^(k*cap) := pow_le_pow_left₀ (inv_nonneg.mpr (le_min hw.le zero_le_one)) ha _
  have he : Real.exp a≤Real.exp 1 := Real.exp_le_exp.mpr (min_le_right _ _)
  have hc : 0≤∑ r∈range (cap+1),2*Comparison.Density.Render.entry G r k :=
    sum_nonneg fun r _ => mul_nonneg (by norm_num) (entry_nonneg G r k)
  calc
    _ = (∑ r∈range (cap+1),2*Comparison.Density.Render.entry G r k)*
        ((k*cap).factorial:ℝ)*(a⁻¹)^(k*cap)*Real.exp a := by unfold amplifier a;rw [div_eq_mul_inv,←inv_pow];ring
    _ ≤ (∑ r∈range (cap+1),2*Comparison.Density.Render.entry G r k)*
        ((k*cap).factorial:ℝ)*s^(k*cap)*Real.exp 1 := by gcongr
    _ = _ := by ring

include H hT in
/-- Each actual visit length is paid by its own original exponential reserve. -/
theorem visit (k cap : ℕ) (hcap : P.rankCap≤cap) :
    stamp k T ≤ amplifier G cap k width*(T.coin*Real.exp (width*T.fall)) := by
  let d := k*cap
  have hr := (P.rank_bounded i T hT).trans hcap
  have he : 2*Comparison.Density.Render.entry G (P.rank i) k ≤
      ∑ r∈range (cap+1),2*Comparison.Density.Render.entry G r k :=
    single_le_sum (fun r _ => mul_nonneg (by norm_num) (entry_nonneg G r k)) (mem_range.mpr (by omega))
  have hD : k*P.rank i≤d := Nat.mul_le_mul_left k hr
  have hp : (1+(T.fall:ℝ))^(k*P.rank i) ≤ (1+(T.fall:ℝ))^d :=
    pow_le_pow_right₀ (le_add_of_nonneg_right (Nat.cast_nonneg T.fall)) hD
  let a := min width 1
  have ha : 0<a := lt_min H.width_pos zero_lt_one
  have hp' := WilsonLocalKernelMoments.power (x:=1+(T.fall:ℝ)) (by positivity) ha d
  have hwa : Real.exp (a*(T.fall:ℝ))≤Real.exp (width*T.fall) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _))
  have hc := (H.coefficient i T hT).1
  calc
    _ = 2*Comparison.Density.Render.entry G (P.rank i) k*((1+(T.fall:ℝ))^(k*P.rank i))*T.coin := by unfold stamp;ring
    _ ≤ (∑ r∈range (cap+1),2*Comparison.Density.Render.entry G r k)*
          (((d.factorial:ℝ)/a^d)*Real.exp (a*(1+(T.fall:ℝ))))*T.coin :=
        mul_le_mul_of_nonneg_right (mul_le_mul he (hp.trans hp') (by positivity) (sum_nonneg fun r _ =>
          mul_nonneg (by norm_num) (entry_nonneg G r k))) hc
    _ ≤ (∑ r∈range (cap+1),2*Comparison.Density.Render.entry G r k)*
          (((d.factorial:ℝ)/a^d)*(Real.exp a*Real.exp (width*T.fall)))*T.coin := by
        rw [mul_add,mul_one,Real.exp_add]
        have hsum : 0≤∑ r∈range (cap+1),2*Comparison.Density.Render.entry G r k :=
          sum_nonneg fun r _ => mul_nonneg (by norm_num) (entry_nonneg G r k)
        gcongr
    _ = _ := by unfold amplifier d a;ring

/-- Rooted charge of a source row's actual k-th derivative on the measured field direction. -/
def axis (P : MarkedPackets D G n R) (w : V → ℝ) (g : ℝ) (x : IndependentTests D)
    (k : ℕ) (v : V) (A : Directions G n) (i : ℕ) : ℝ :=
  if P.mode i=R.fire v then w v * ‖iteratedFDeriv ℝ k
    ((fun U => P.term (testInclusion D x) g U i) ∘ increment 1) A‖ else 0

include H in
/-- Full absolute summability at the genuine singleton, with every signed source germ and its true support still available. -/
theorem paid (x : IndependentTests D) (k cap : ℕ) (hcap : P.rankCap≤cap)
    (v : V) (A : Directions G n) (hA : ‖A‖≤1) :
    SumBudget (axis P w g x k v A) (amplifier G cap k width*budget) := by
  have hK := amplifier_nonneg G cap k H.width_pos
  apply budget_mono (budget_scale hK (H.roots v))
  · intro i
    by_cases hm : P.mode i=R.fire v
    · simp only [axis,hm,ite_true]
      exact mul_nonneg (H.positive v).le (norm_nonneg _)
    · simp [axis,hm]
  · intro i
    by_cases hm : P.mode i=R.fire v
    · have hv : v∈(R.fire v).val := Finset.mem_singleton_self v
      cases e : P.packet i with
      | none => simp [axis,hm,e,MarkedPackets.term,Function.comp_def]
      | some T =>
        simp only [axis,hm,if_true,Poly.solo_toll]
        rw [if_pos hv]
        have ht := (chart_term H e x k A hA).pay k le_rfl
        have hp := visit H e k cap hcap
        calc
          _ ≤ w v*(‖(g:ℂ)^P.power i‖*stamp k T) := mul_le_mul_of_nonneg_left ht (H.positive v).le
          _ ≤ w v*(‖(g:ℂ)^P.power i‖*(amplifier G cap k width*(T.coin*Real.exp (width*T.fall)))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp (norm_nonneg _)) (H.positive v).le
          _ = _ := by ring
    · simpa only [axis,if_neg hm] using mul_nonneg hK ((H.roots v).1 i)

end YM.Integration.ActualWilsonPacketGerms
