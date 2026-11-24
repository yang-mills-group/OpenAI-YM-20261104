import YM.XSpace.Batches

/-!
# Reality and parity of the actual input arrays to positioning
(still before solving). Include test functions and check mesh measure.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Normalize
open Function Set Filter Maxwell Maxwell.Free Maxwell.Wick MeasureTheory Taylor PowerSeries
open TestBudget Expense Lattice
open scoped BigOperators Topology Classical ContDiff
variable {G:Gauge} {d n:ℕ}

lemma lift_splint (p:WickPol G): On.lifting (mirror _ p)=mirror _ (On.lifting p):=by
  suffices h: On.lifting.comp (mirror (Maxwell.Slot G))=(mirror (Labels.Key G)).comp On.lifting from AlgHom.congr_fun h p
  ext1 i; rw [AlgHom.comp_apply,AlgHom.comp_apply, mirror,MvPolynomial.aeval_X,map_neg]; unfold On.lifting; simp [Taylor.mirror]

lemma splinted {p q:On.Grade G d} (h: q.val=mirror _ p.val) (g:Mesh) (D:Initialize G) (c:g.Sites):
    D.atSite g d c q =Bare.reverseArgs (D.tree g.p) G (D.atSite g d c p):=by
  let T := D.tree g.p; let H:= D.surveys d; let z (v:On.Grade G d):= On.sectionMap d (en (Nat.le_refl d) v)
  let C (v:On.Grade G d):=On.stencil _ H g.p T c v
  have he : Bare.reverseArgs T G (C p)= C q:=by
    change Bare.reverseArgs T G (Bare.column T H c (z p)) = Bare.column T H c (z q)
    rw [Bare.column_formula,Bare.column_formula,Bare.reverse_raw,Survey.insertW_val, Survey.insertW_val, ← Taylor.reflected_milk, show (z q).val=mirror _ (z p).val by change On.lifting q.val=mirror _ (On.lifting p.val); rw [h,lift_splint]]
  unfold Initialize.atSite; rw [LinearMap.smul_apply,LinearMap.smul_apply,Bare.reverse_scalar,show Bare.reverseArgs _ _ _ = C q from he]
lemma staunch (S:Period) (T:S.Tree) (z:ℂ) (p:Bare.Series T G): Bare.conjugate T G (z • p) = star z • Bare.conjugate T G p:=by
  rw [Algebra.smul_def,Algebra.smul_def,map_mul,Bare.conjugate]; simp [Taylor.conjPol, PowerSeries.algebraMap_apply, MvPolynomial.algebraMap_eq]
lemma spoke {p q:On.Grade G d} (h:q.val=realForm p.val) (g:Mesh) (D:Initialize G) (c:g.Sites): D.atSite g d c q = Bare.conjugate (D.tree g.p) G (D.atSite g d c p):=by
  rw [Initialize.atSite,LinearMap.smul_apply,LinearMap.smul_apply,staunch]
  let T:= D.tree g.p; let H:= D.surveys d; let z (v:On.Grade G d):= On.sectionMap d (en (Nat.le_refl d) v)
  have hv : z q=Labels.realBar (z p):= On.section_real _ _ h.symm
  simp; change _ • Bare.column T H c (z q)= _ • Bare.conjugate T G (Bare.column T H c (z p)); rw [Bare.column_real,hv]

private lemma sint (D:Initialize G) (g:Mesh) (d:Fin n→ℕ) (p q:∀ i,On.Grade G (d i)) (h:∀ i,(q i).val=mirror _ (p i).val) (t:Test n) (j:ℕ) :
    coeff j ((D.report g d t) q)=(-1:ℂ)^j * coeff j ((D.report g d t) p):=by
  have hu (x: Fin n→g.Sites) : D.atTuple g d x q=rescale (-1:ℂ) (D.atTuple g d x p):=by simp_rw [Initialize.atTuple_eq, fun i=> splinted (h i) g D (x i)]; rw [← map_prod,Bare.reverse_normalized]
  simp_rw [Initialize.report_formula,map_smul,map_sum,map_smul,hu, coeff_rescale, smul_eq_mul]; rw [mul_left_comm ((-1:ℂ)^j) ((g.spacing:ℂ)^(4*n)) _]; apply congr_arg; rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun v _=>?_); ring
lemma slot_arrays (D:Initialize G) (g:Mesh) (d j:ℕ): recruit (hinge d) (batch D g d j)=((-1:ℝ)^j) • batch D g d j:=by
  ext1 n; ext1 t; ext1 p; change batch D g d j n t ((hinge d) ∘ p) = ((-1:ℝ)^j) • batch D g d j n t p
  rw [batches,batches, Finset.smul_sum]; refine Finset.sum_congr rfl fun i _=> Eq.trans (sint D g _ (fun k=>part d (i k) (p k)) _ (fun k=> hinge_part (p k) (i k)) _ _) ?_; simp only [Complex.real_smul,Complex.ofReal_pow,Complex.ofReal_neg,Complex.ofReal_one]

def inverted (t:Test n) : Test n:= by
  let F:= (Complex.conjCLE : ℂ→L[ℝ] ℂ) ∘ t
  have hv : tsupport F=tsupport t:=by unfold tsupport; congr 1; ext x; change (star (t x) ≠ 0) ↔ t x≠0; simp
  exact ⟨F,(Complex.conjCLE : ℂ→L[ℝ] ℂ).contDiff.comp t.contDiff,(by unfold HasCompactSupport; rw [hv]; exact t.hasCompactSupport),hv.symm ▸ t.tsupport_subset⟩
lemma inverts (t:Test n) (x:Points n): inverted t x= star (t x):=rfl
lemma coil (g:Mesh) (t:Test n) (x: Fin n→ Cover): g.smear x (inverted t)= star (g.smear x t):=by
  rw [Mesh.smear]; simp only [star_smul, LinearMap.coe_mk,AddHom.coe_mk,star_trivial]; change _ • (∫ c in g.Box, star (t _))= _ • star (∫ c in g.Box,t _); exact congr_arg (_ • ·) integral_conj
private lemma recom (D:Initialize G) (g:Mesh) (d:Fin n→ℕ) (p q:∀ i,On.Grade G (d i)) (h:∀ i,(q i).val=realForm (p i).val) (t:Test n) (j:ℕ):
    coeff j ((D.report g d (inverted t)) q)= star (coeff j ((D.report g d t) p)):=by
  have hu (x: Fin n→g.Sites) : D.atTuple g d x q=map (starRingEnd ℂ) (D.atTuple g d x p):=by simp_rw [Initialize.atTuple_eq, fun i=> spoke (h i) g D (x i)]; rw [← map_prod,Bare.normalize_real]
  simp_rw [Initialize.report_formula,map_smul,map_sum,map_smul,coil, hu,coeff_map,star_smul,star_sum]; simp

def RealFields (P:Prediction G d): Prop:= ∀ (n:ℕ) (p:Fin n→Sec G d) t,P n (inverted t) (reel d ∘ p)= star (P n t p)
lemma reel_array (D:Initialize G) (g:Mesh) (d j:ℕ): RealFields (batch D g d j):=by
  intro n p t; rw [batches,batches,star_sum]; exact Finset.sum_congr rfl fun i _=> recom D g _ (fun k=>part d (i k) (p k)) _ (fun k=> part_reel _ (i k)) t j
end YM.XSpace.Normalize
