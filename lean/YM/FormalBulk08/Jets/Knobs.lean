import YM.FormalBulk08.Jets.Glean
import YM.PertExtension.PTBills

/-! Match Taylor stencils under arbitrary simultaneous coordinate substitutions;
these are non-mixing step data, formal equality only. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Jets
open Series Wick Function Filter Set Metric PowerSeries
open scoped Classical ContDiff Topology BigOperators
open PertExtension.Series Tested
variable {I W : Type*}

def glimpse (x : Rays I) : Plate ℝ I →+* PowerSeries ℝ := PowerSeries.map (MvPolynomial.aeval x).toRingHom
lemma glimpse_coeff (x : Rays I) (p : Plate ℝ I) (n) : coeff n (glimpse x p)=traceP x (coeff n p) := coeff_map ..
lemma photo {p q : Plate ℝ I} (h : ∀ x:Rays I, glimpse x p=glimpse x q):p=q := integral_ext h
lemma glimpse_slide (x : Rays W) (z : I→Plate ℝ W) (p : Plate ℝ I) : glimpse x (roam ℝ z p)=roam ℝ (fun i=>glimpse x (z i)) p := by
   unfold glimpse roam; rw [change_beam, show (PowerSeries.map (MvPolynomial.aeval x).toRingHom).comp (insertAt ℝ z) = insertAt ℝ (fun i=>PowerSeries.map (MvPolynomial.aeval x).toRingHom (z i)) from ?hex]
   case hex => ext <;> simp

def gaze (f : ℝ→ℝ) (F : PowerSeries ℝ) := Aspiration f (Tested.term F)
lemma unique_gaze {f : ℝ→ℝ} {F G : PowerSeries ℝ} (hf : gaze f F) (hg : gaze f G) : F=G := PowerSeries.ext (fun n=> congr_fun (Aspiration.unique hf hg) n)
lemma gaze_replace {f g:ℝ→ℝ} {F : PowerSeries ℝ} (hf : gaze f F) (he : f=ᶠ[Tested.germ] g) : gaze g F := by
   intro n; obtain ⟨C,hC,h⟩:=hf n; exact ⟨C,hC,(he.and h).mono fun x h=>by simpa only [Pi.sub_apply,←h.1] using h.2⟩
lemma gaze_plus {f g:ℝ→ℝ} {F G:PowerSeries ℝ} (hf : gaze f F) (hg : gaze g G) : gaze (f+g) (F+G) := by have h:=Aspiration.add hf hg; unfold gaze; convert! h using 1
lemma gaze_neg {f:ℝ→ℝ} {F : PowerSeries ℝ} (hf : gaze f F) : gaze (-f) (-F) := by
   intro n; have h:= bill_neg (hf n); convert! h using 1; ext x; simp [peval,PertExtension.Series.Zone.eval,term,Finset.sum_neg_distrib,sub_eq_add_neg]; abel
lemma gaze_fade {f g:ℝ→ℝ} {F G : PowerSeries ℝ} (hf : gaze f F) (hg : gaze g G): gaze (f*g) (F*G) := by
   unfold gaze; convert! Aspiration.prod hf hg using 1; funext i; simp [conv,term, coeff_mul]
lemma gaze_leaf (x : ℝ) (n : ℕ) : gaze (fun r=> r^n*x) (X^n*C x) := by
   unfold gaze; convert! Aspiration.single x n using 1; funext m; by_cases h:m=n <;> simp [term, coeff_X_pow,h]
lemma gaze_exact (x : ℝ) : gaze (fun _=>x) (C x) := by simpa using (gaze_leaf x 0)
lemma gaze_sum {A : Type*} {s : Finset A} {F : A→PowerSeries ℝ} {f : A→ℝ→ℝ} (h : ∀ i∈s,gaze (f i) (F i)) : gaze (∑ i∈s,f i) (∑ i∈s,F i) := by
   unfold gaze; convert! Aspiration.sum s f (fun i=>term (F i)) h using 1; funext i; simp [term]
lemma gaze_path (z : ℝ→ Rays I) (w : I→PowerSeries ℝ) (p : Glyphs ℝ I) (h : ∀ i,gaze (fun r=>z r i) (w i)) : gaze (fun r:ℝ=>traceP (z r) p) (insertAt ℝ w p) := by
   induction p using MvPolynomial.induction_on with
   | C a=> simpa [traceP] using gaze_exact a
   | add p q hp hq=> simpa [traceP,Pi.add_def] using! gaze_plus hp hq
   | mul_X p i hp=> simpa [traceP,Pi.mul_def] using! gaze_fade hp (h i)

variable [Fintype I]
lemma fixed_path (x : Rays I) (f : Rays I→ℝ) (hp : ContDiffAt ℝ ∞ f 0) : gaze (fun r:ℝ=> f (r • x)) (glimpse x (paste f)) := by unfold gaze term; simp_rw [glimpse_coeff,trace_paste]; exact directions hp x
lemma fitted_path (x : ℝ→ Rays I) (z : I→PowerSeries ℝ) (f : Rays I→ℝ) (hc : ContDiffAt ℝ ∞ f 0) (hp : ∀ i,gaze (fun r=> x r i) (z i)) : gaze (fun r:ℝ => f (r • x r)) (roam ℝ z (paste f)) := by
   intro n
   let p:= paste f; let g (r:ℝ) := f (r•x r)
   let H (r:ℝ) := ∑ i∈Finset.range (n+1),r^i * traceP (x r) (coeff i p)
   let a:=∑ i∈Finset.range (n+1), insertAt ℝ z (coeff i p)*X^i
   have he : gaze H a := by
      have h (i:ℕ) := gaze_fade (gaze_path x z (coeff i p) hp) (gaze_leaf 1 i)
      simp only [mul_one,map_one] at h
      unfold a; apply gaze_replace (gaze_sum (fun i hi=>h i))
      exact Eventually.of_forall fun r=>by unfold H; simp [Finset.sum_apply,mul_comm]
   have hh : Bill (n+1) (g-H) := by
      obtain ⟨δ,C,hδ,hC,h⟩:= Radial.deposition f n hc
      let U : Rays I := fun i=>term (z i) 0
      have hX : Tendsto x Tested.germ (𝓝 U) := tendsto_pi_nhds.mpr fun i=> Aspiration.tendsto_first (hp i)
      let D : ℝ:=‖U‖+1; have hpD : 0<D := by unfold D; positivity
      refine ⟨C*D^(n+1),by positivity,?_⟩
      filter_upwards [hX.norm.eventually (gt_mem_nhds (lt_add_one ‖U‖)),eventually_small (div_pos hδ hpD)] with r hr hv
      have ht : ‖x r‖ < D := hr
      have h1 : 0<r := hv.1
      rw [show (g-H) r=f (r•x r) - Zone.eval (Radial.jet f) n r (x r) from (by unfold Zone.eval; simp [H,g,p,← trace_paste])];
      refine (h (x r) r h1 ?_).trans ?_
      · exact (mul_le_mul_of_nonneg_left ht.le h1.le).trans ((lt_div_iff₀ hpD).mp hv.2).le
      gcongr
   have hx : Through n (roam ℝ z p) a:= liquid _ _ _
   have h := bill_add hh (he n)
   have heq : peval (term a) n=peval (term (roam ℝ z p)) n := by ext r; unfold peval Zone.eval; exact Finset.sum_congr rfl (fun i hi=>congr_arg (fun c:ℝ=> r^i • c) (hx i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))).symm)
   rw [heq] at h; rw [sub_add_sub_cancel] at h; exact h
end YM.FormalBulk08.Jets
