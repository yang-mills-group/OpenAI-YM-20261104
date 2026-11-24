import YM.RegulatorIR.Gain.Pins

/-!
# Read on any finitely supported screen; no polynomial growth on tests

Pulse filtration alignment done coefficient-wise with cover tensors. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Gain
open Function Budget Spatial Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Step Matrix StopB Ward Uniform Finset Halo Halo.Sight
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff
variable {G:Gauge}{I J X Y Z:Type}{f c:Side}{m e p i b k:ℕ}
section Fin
variable [Fintype I][Fintype J]
omit [Fintype I] in
lemma color_map (Γ:Curve I J)(z:J→ℝ)(x:I):PowerSeries.map (MvPolynomial.eval z) (related Γ x)= circ Γ z x:=by ext1 i; rw [PowerSeries.coeff_map,related, circ,coeff_mk,coeff_mk]; exact (pluck ..).symm
omit [Fintype I] in
lemma lens_ink (Γ:Curve I J)(z:J→ℝ)(v:Jet I) : PowerSeries.map (MvPolynomial.eval z) (alter Γ v)= MvPolynomial.aeval (circ Γ z) v:=by
 induction v using MvPolynomial.induction_on with
 | C k=> unfold alter;simp [PowerSeries.algebraMap_apply, MvPolynomial.algebraMap_eq]
 | add i j h he=> rw [map_add,map_add,map_add,h,he]
 | mul_X i a h=>rw [map_mul,map_mul,map_mul,h];simp only [alter,MvPolynomial.aeval_X]; rw [color_map]
lemma chill (Γ:Curve I J)(T:Orders I)(x:J→ℝ)(m:ℕ)(e:ℕ): MvPolynomial.eval x (Gradient.ink Γ T (fun i=>i+m) e)=rhymeR (circ Γ x) T m e:=by
 unfold Gradient.ink; rw [map_sum];apply sum_congr rfl;intro p _; rw [← PowerSeries.coeff_map,lens_ink,Diagram.packed,map_sum,map_sum]; exact sum_congr rfl fun _ _=> (rhyme_f ..).symm
lemma finite_path (Γ:Curve I J)(T:Orders I)(H:Ranks m T)(e:ℕ)(x:J→ℝ) : MvPolynomial.eval x (packed (shot Γ T e) (e+m))=rhymeR (circ Γ x) T m e :=by rw [← show PowerSeries.coeff e (Cluster.printed m (shot Γ T))=packed (shot Γ T e) (e+m) from (by rw [Cluster.printed,coeff_mk]),Cluster.printedShot H]; exact chill ..
end Fin

section Infinite
-- finite screen from source. To obtain `tides` only pointwise. Need `Cluster.Bill` on cover inputs.
variable [Fintype X]
variable (Γ : Curve I J)(T:Orders I)
variable (V : J→ Y)
variable (A:X↪J) (x:X→ℝ)
-- width budgets supplied by constructive diagonal guarantee. Enough for boundedness of its finite projections. -/
def Steam (Γ:Curve I J)(e:ℕ):Prop:=∀ i ≤ e,∃ c:ℝ≥0∞,c≠⊤ ∧ ∀ u,quota (Γ u i) 1≤c
lemma Steam.row {Γ:Curve I J}(h:Steam Γ p) :CostRow Γ p:=by
 intro i hi; obtain ⟨c,hc,H⟩:= h i hi
 exact ⟨_,hc,fun z v=>(by apply le_trans _ (H z); rw [quota_base]; exact ENNReal.le_tsum v)⟩
lemma mantle (S:Steam Γ p) : Full (fun _:Unit=>circ Γ (dilute A x)) p:=by
 intro a ha; obtain ⟨c,hc,H⟩:=S a ha
 let m:= Finset.univ.sup fun v:Tuple X (a+1)=> ‖noodle x v‖ₑ
 have hm :m≠⊤:= ne_of_lt (Finset.sup_lt_iff (by simp)|>.mpr (fun i _=>enorm_lt_top))
 refine ⟨_,ENNReal.mul_ne_top hc hm,fun _ i=>?_⟩
 change ‖coeff a (circ Γ _ i)‖ₑ≤_; rw [circ, PowerSeries.coeff_mk,crops x A (Γ i a)] -- order inspect
 have ht:= quota_restrict _ (injectT A) (Γ i a) 1 |>.trans (H i)
 apply le_trans enorm_tsum_le_tsum_enorm; apply le_trans _ (mul_le_mul_left ht m);change _≤ quota (crop A (Γ i a)) 1 *m;rw [quota_base,← ENNReal.tsum_mul_right]; exact ENNReal.tsum_le_tsum fun i=> by rw [enorm_mul]; exact mul_le_mul_right (Finset.le_sup (f:=fun v:Tuple X (a+1)=> ‖noodle x v‖ₑ) (Finset.mem_univ _)) _

-- crop at output finite size, compare at that section via E algebra
lemma wave_eval (H:Steam Γ e)(V:Ranks m T)(ht:Cluster.Bill T e) : MvPolynomial.eval x (packed (fun i=>crop A (shot Γ T e i)) (e+m))=rhymeR (circ Γ (dilute A x)) T m e:=by
 let τ:=fun l:Finset I=> measureT l T; let f:= fun l: Finset I=> shot (house A Γ l) (τ l) e
 let P(l:Finset I):= MvPolynomial.eval x (packed (f l) (e+m))
 let p : Ranked X:=fun i=> crop A (shot Γ T e i); let r:= circ Γ (dilute A x)
 have he:Tendsto P atTop (𝓝 (MvPolynomial.eval x (packed p (e+m)))):=by
    unfold P; simp_rw [← speaking]
    apply tendsto_finsetSum; intro i _
    have hh:= tides (r:=i) A Γ H.row ht le_rfl
    unfold strum; simp_rw [tsum_fintype]; apply tendsto_finsetSum;intro j _
    exact (tendsto_pi_nhds.mp hh j).mul_const _
 apply tendsto_nhds_unique he; unfold P f; simp_rw [fun l=>finite_path (house A Γ l) (τ l) (measure_price l T V) e x,rhymeR];apply tendsto_finsetSum;intro x' hx;apply tendsto_finsetSum;intro i _
 let b:=x'.1;let s:=x'.2
 have hb: b+s=e:=mem_antidiagonal.mp hx
 obtain ⟨c,hc,H'⟩:=(mantle Γ A x H).pipes i s (by omega)
 let u:=fun z:Tuple I i=>T b i z*coeff s (pip r z)
 have hu : Summable u:= quota_summable (w:=1) (fun _=>le_rfl) (rhyme_abs r (T b i) s (ht b (by omega) i) hc (H' ()))
 have hp (l: Finset I)(p:l):circ (house A Γ l) x p=r p.val:=by ext t; rw [circ, coeff_mk]; unfold r; rw [circ,coeff_mk]; exact (crops ..).symm
 have hy(l:Finset I): rhyme (circ (house A Γ l) x) (τ l b i) s=∑ z∈tent i l,u z:=by
    rw [rhyme, tsum_fintype]; apply sum_bij (fun a _=> acrossT (Cluster.Brief.tile l) a)
    · intro a ha; exact Fintype.mem_piFinset.mpr (fun i=>(a i).property)
    · intro _ _ _ _ h; exact injectT _ h
    · intro a ha; exact ⟨fun i=>⟨a i,Fintype.mem_piFinset.mp ha i⟩,mem_univ _,rfl⟩
    intro a _; unfold pip; simp_rw [hp]; rfl
 change Tendsto (fun l=> rhyme (circ (house A Γ l) x) (τ l b i) s) _ _; simp_rw [hy]; exact hu.hasSum.comp (tent_wide ..)
end Infinite

-- proof demanded on all finite supports

def Voice (Γ Ω:Curve I J)(Z:Orders I) (m p:ℕ):Prop:=∀ L:Finset J,∀ x:L→ℝ,∀ e ≤ p,rhymeR (circ Γ (dilute (Cluster.Brief.tile L) x)) Z m e=rhymeR (circ Ω (dilute (Cluster.Brief.tile L) x)) Z m e
lemma consents (Γ Ω:Curve I J)(Z:Orders I)(H:Ranks m Z)(V:Voice Γ Ω Z m e)(hx:Steam Γ e)(hy:Steam Ω e)(hq: Cluster.Bill Z e):shot Γ Z e=shot Ω Z e:=by
 ext1 r; ext1 x
 by_cases h:e+m < r
 · rw [show shot Γ Z e r=0 from Classical.not_not.mp (fun hk=>(not_le.mpr h) (shot_rank H Γ e r hk)),show shot Ω Z e r=0 from Classical.not_not.mp (fun hk=>(not_le.mpr h) (shot_rank H Ω e r hk))]
 let L:= Finset.univ.image x;let T:=Cluster.Brief.tile L;let A k:= crop T (shot Γ Z e k);let B k:=crop T (shot Ω Z e k)
 have hb: packed A (e+m)=packed B (e+m):=MvPolynomial.funext (fun v=> ((wave_eval Γ Z T v hx H hq)).trans ((V L v e le_rfl).trans (wave_eval Ω Z T v hy H hq).symm))
 have hp:r∈ Finset.range (e+m+1):= mem_range.mpr (by omega);have hh:= identified (A r) (B r) (crop_symm _ _ (shiftSym _ _ _ _)) (crop_symm _ _ (shiftSym _ _ _ _)) ((Diagram.isolate _ hp).symm.trans ((congr_arg (MvPolynomial.homogeneousComponent r) hb).trans (Diagram.isolate _ hp)))
 exact congr_fun hh (fun i=>⟨x i,mem_image_of_mem x (mem_univ i)⟩)
end YM.RegulatorIR.Gain
