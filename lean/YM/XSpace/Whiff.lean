import YM.XSpace.Nested

/-!
# A uniform estimate for the profile tests after positioning (order zero)

Users may multiply by bounded finite family coefficients, and the same fixed C1
seminorm continues to suffice; estimates billed before increasing smooth orders.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.TestBudget
open Function Set Filter Maxwell Maxwell.Free Maxwell.Wick MeasureTheory Expense Normalize
open scoped BigOperators Topology Classical ContDiff
variable {G:Gauge} {d l n:ℕ} {ι:Type*} {F:Filter ι} {s:ι→Mesh} {A:Screen G d}

-- allocated rate on test knots
structure Knot (K:Set (Points n)) (F:Filter ι) (s:ι→Mesh) (X:ι→ Test n→ℂ) (Y:Test n→ℂ):Prop where
  right : ∃ C:ℝ,0≤C∧∀ f:Test n,tsupport f⊆K→∀ b:ℝ,Bound f b→ ‖Y f‖ ≤ b*C
  land : ∃ C:ℝ,0≤C∧∀ᶠ i in F,∀ f:Test n,tsupport f⊆K →∀ b:ℝ,Bound f b→ ‖X i f-Y f‖≤ b*C*(s i).spacing

namespace Knot
variable {K:Set (Points n)} {X X':ι→Test n→ℂ} {Y Y':Test n→ℂ}
lemma zero : Knot K F s (fun _ _=>0) (fun _=>0):= ⟨⟨0, le_rfl, by simp⟩,⟨0,le_rfl,Eventually.of_forall (by simp)⟩⟩
lemma add (h: Knot K F s X Y) (h':Knot K F s X' Y'): Knot K F s (fun i f=>X i f+ X' i f) (fun f=>Y f+Y' f):=by
  constructor
  · obtain ⟨C,hC,h⟩:=h.right; obtain ⟨B,hB,h'⟩:=h'.right; refine ⟨C+B,add_nonneg hC hB,fun x hx b hb=> (norm_add_le ..).trans ?_⟩; rw [mul_add]; exact add_le_add (h x hx b hb) (h' x hx b hb)
  obtain ⟨C,hC,h⟩:= h.land; obtain ⟨B,hB,h'⟩:=h'.land; refine ⟨C+B,add_nonneg hC hB,?_⟩
  filter_upwards [h,h'] with i hi hi' x hx b hb; rw [show X i x+X' i x-(Y x+Y' x) = _ from (sub_add_sub_comm (X i x) (Y x) (X' i x) (Y' x)).symm,mul_add,add_mul]; exact (norm_add_le ..).trans (add_le_add (hi x hx b hb) (hi' x hx b hb))
lemma sum {J : Type*} (u:Finset J) {x:J→ι→Test n→ℂ} {y:J→Test n→ℂ} (h:∀ j∈u,Knot K F s (x j) (y j)): Knot K F s (fun i f=>∑ j∈u,x j i f) (fun f=>∑ j∈u,y j f):=by
  induction u using Finset.induction_on with
  | empty=> simp only [Finset.sum_empty]; exact zero
  | insert a J hJ ih=> simp_rw [Finset.sum_insert hJ]; exact (h a (Finset.mem_insert_self ..)).add (ih (fun i hi=>h i (Finset.mem_insert_of_mem hi)))
lemma scalar (S:Stretched F s) {u:ι→ℝ} {c:ℝ} (T: Rate F s u (fun _=>c)) (h:Knot K F s X Y): Knot K F s (fun i f=>u i • X i f) (fun f=> c • Y f):=by
  obtain ⟨a,ha,hf⟩:=h.right; constructor
  · refine ⟨‖c‖*a,by positivity,fun f hx b hb=>?_⟩; rw [norm_smul,mul_left_comm]; exact mul_le_mul_of_nonneg_left (hf f hx b hb) (norm_nonneg _)
  obtain ⟨D,hD,H⟩:= T.bounds; obtain ⟨r,hr,hp⟩:=h.land; obtain ⟨g,hg,hK⟩:=(Cap.higher S (Cap.const F c) T).bounds
  refine ⟨g*r+D*a,by positivity,?_⟩; filter_upwards [H,hp,hK] with i hi hp hk f hx b hb
  have hk':= hf f hx b hb; have he:= bound_nonneg f hb; specialize hp f hx b hb; change ‖u i-c‖ ≤ D*(s i).spacing at hi
  rw [show u i • X i f-c • Y f = u i • (X i f-Y f)+(u i-c) • Y f from by rw [smul_sub,sub_smul]; abel]
  apply (norm_add_le ..).trans; rw [norm_smul,norm_smul]
  exact (add_le_add (mul_le_mul hk hp (norm_nonneg _) hg.le) (mul_le_mul hi hk' (norm_nonneg _) (mul_nonneg hD.le (s i).positive.le))).trans_eq (by ring)
end Knot
lemma seed_test (R:Initialize G) (K:Set (Points n)) (h:IsCompact K) (hk: K⊆ conf n) (p:Fin n→Sec G d) (S:Stretched F s): Knot K F s (fun i f=> batch R (s i) d 0 n f p) (fun f=> reference G d n f p):=by
  refine ⟨?_,waist R S p K h hk⟩
  -- bound by integral restricted real volume
  obtain ⟨C,hc⟩:= (h.image_of_continuousOn ((smooths p).mono hk|>.norm)).bddAbove; let c:= max C 0; have hu : 0≤c:=le_max_right ..; let a:=volume.real K; refine ⟨c*a,mul_nonneg hu ENNReal.toReal_nonneg,fun f he b hb=>?_⟩
  rw [reflects,Test.applyTo, ← setIntegral_eq_integral_of_forall_compl_eq_zero (s:=K) (fun x hx=> mul_eq_zero_of_left (image_eq_zero_of_notMem_tsupport (fun hv=> hx (he hv))) _)]; apply (norm_setIntegral_le_of_norm_le_const h.measure_lt_top (C:=b*c) (fun x hx=> ?_)).trans_eq (by unfold a; ring)
  rw [norm_mul]; exact mul_le_mul (hb x).1 (le_trans (hc (mem_image_of_mem _ hx)) (le_max_left ..)) (norm_nonneg _) (bound_nonneg f hb)
lemma seeds_pay (D:Normalize.Fray A) (H:A.Prepared) (R:Initialize G) (K:Set (Points n)) (h:IsCompact K) (hk: K⊆ conf n) (p:Fin n→Sec G d) (S:Stretched F s) :
    Knot K F s (fun i f=> (D.fit H (batch R (s i) d)) 0 n f p) (fun f=> reference G d n f p):=by
  let T i:=batch R (s i) d; let v i:= guide G d (D.Lays H (T i) 0); let B i:=stand (D.Lays H (T i) 0); let P:=(tableD G d); let Q j:= reference G d n j
  let a (j:Fin n→ Pin G d) (g:MoveSpace G d):= ∏ i : Fin n,P (Normalize.Fray.box g (p i)) (j i)
  let x (j: Fin n→Pin G d) i (f: Test n):= T i 0 n f (fun k=>Module.finBasis ℝ (Sec G d) (j k)); let y (j:Fin n→Pin G d) (f : Test n):= Q f (fun k=> Module.finBasis ℝ (Sec G d) (j k))
  suffices hV: Knot K F s (fun i f=>∑ j, a j (v i) • x j i f) (fun f=>∑ j,a j 0 • y j f) by
    have ht i (f:Test n): (D.fit H (T i)) 0 n f p= ∑ j, a j (v i) • x j i f:=by
      unfold Fray.fit; rw [rest, PowerSeries.coeff_zero_eq_constantCoeff_apply, const_deck, recruits]; unfold a v Fray.box; simp_rw [LinearEquiv.symm_apply_apply]; exact medium _ ((T i 0 n f).restrictScalars ℝ)
    have he (f:Test n): reference G d n f p= ∑ j,a j 0 • y j f:=by unfold a Fray.box; simp_rw [map_zero,stand0]; exact medium p ((Q f).restrictScalars ℝ)
    simp_rw [show ∀ i f,D.fit H (batch R (s i) d) 0 n f p= _ from ht,he]; exact hV
  apply Knot.sum (x:=fun j i f=> a j (v i) • x j i f) (y:=fun j f=> a j 0 • y j f); intro j _; apply Knot.scalar S _ (seed_test R K h hk _ S) -- may need annotate
  have hx (p): ContDiff ℝ ω (fun v:MoveSpace G d=> P (Fray.box v p)):=by
    let U : MoveSpace G d →ₗ[ℝ] RSpace G d:= { toFun v:= P (((guide G d).symm v).val p), map_add' u v:=by rw [map_add]; exact map_add P _ _, map_smul' a v:=by rw [map_smul]; exact map_smul P _ _ }
    simp_rw [Fray.box,stood,map_add]; exact (contDiff_const (c:=P p)).add (LinearMap.toContinuousLinearMap U).contDiff
  have hh : ContDiff ℝ ω (a j):= contDiff_prod (fun i _=>contDiff_pi.mp (hx (p i)) (j i)); have hp : Tendsto v F (𝓝 0):=by unfold v; simp_rw [Fray.leads]; exact D.turns_approach H (D.gait R S)
  exact Asymptotics.IsBigO.trans (((hh.differentiable (by simp) 0).isBigO_sub).comp_tendsto hp) (D.costsPass H R S)
end YM.XSpace.TestBudget
