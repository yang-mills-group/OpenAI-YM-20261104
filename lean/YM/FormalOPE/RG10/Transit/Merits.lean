import YM.FormalOPE.RG10.Transit.Slab

/-!
# Common-order turn and engineering lifts

Scalar columns here `Series`; each through-order depends only on the inputs through that order.
Use in projecting *payload-preserving* cylinders, NOT substituting unrelated lookup labels. Covers
a slot replacement by a formal analytic-coefficient column before estimate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Route
open PowerSeries Finset MeasureTheory Function
open MvPolynomial (aeval)
open scoped Topology BigOperators Classical
variable {I B J : Type} [Fintype J]

lemma exposed (x:Series) : algebraMap Series (Channel I) x=PowerSeries.map MvPolynomial.C x:= rfl
lemma income_P (x : Series) (k) : coeff k (algebraMap Series (Channel I) x) = MvPolynomial.C (coeff k x) := coeff_map ..
lemma tower (x:ℂ) (p:Channel I) : (algebraMap ℂ Series x) • p=x • p := by
  rw [Algebra.smul_def,Algebra.smul_def]; congr! 1
-- avoid IsScalarTower instance adding

variable (q : I → Multi.Vacuum.Gauss.Row J) (y : B→ℂ)
lemma replot_series (f:I→Channel B) (a:Series) : replot f (algebraMap Series (Channel I) a)=algebraMap Series (Channel B) a := by
  apply PowerSeries.ext; intro k; rw [replot_coeff,income_P]; simp_rw [income_P,MvPolynomial.aeval_C]; rw [sum_eq_single (k,0)]
  · simp [PowerSeries.algebraMap_apply] -- inspect
  · intro b hb h; have he:= mem_antidiagonal.mp hb; have hu : b.2≠0:=by intro hp; apply h; exact Prod.ext (by omega) hp
    simp [Algebra.algebraMap_eq_smul_one,hu];
  simp

lemma replot_series_mul (f:I→Channel B) (a:Series) (P:Channel I) : replot f (a • P)= a • replot f P := by
  rw [Algebra.smul_def,map_mul,replot_series, Algebra.smul_def]
lemma run_salary (y : I → ℂ) (a:Series) (p:Channel I) : run y (a • p) = a * run y p := by rw [Algebra.smul_def,map_mul,exposed,run_const]
namespace Bulk
lemma moves (x:Channel (I⊕B)) (r:Series) : water q y (r • x) = outside r * water q y x := funext (fun _=>run_salary (Sum.elim _ y) r x)
lemma profits (p : Channel (I⊕B)) (c:Series) (V : Channel (I⊕B)) (h : coeff 0 V=0) : transfer q (c • p) V=c • transfer q p V := by
  apply runs_determine; intro y; rw [run_salary]; simp_rw [unfolds_step q y _ V h]; rw [moves,FlatFeed.step_external (paid_step q y p V h)]
end Bulk
namespace Episode
variable (e : Episode I B J)
lemma floats_smul (x:Series) (a:Channel I) : e.floats (x • a)=x • e.floats a := by
  unfold floats; dsimp only [AddMonoidHom.coe_mk,ZeroHom.coe_mk]; rw [replot_series_mul,Bulk.profits _ _ _ _ e.law] -- inspect
lemma floats_const (x:ℂ) (a:Channel I) : e.floats (x • a)=x • e.floats a:= by rw [← tower, ← tower, floats_smul] -- inspect

def linear : Channel I →ₗ[Series] Channel B where
  __:= e.floats
  map_smul' := e.floats_smul

def realLinear : Channel I →ₗ[ℂ] Channel B where
  __:= e.floats
  map_smul' := e.floats_const
end Episode

section receipt
variable {S : Type*} [CommRing S]
-- restrict through common multiplicative Taylor conventions. f changes separately by an equality
lemma restr (p q : Channel I) {r} (h : Through r p q) (T:I→Channel B) : Through r (replot T p) (replot T q) := mapCoeff.near_aux _ h
lemma moved (p r : Channel (I⊕B)) {k} (h : Through k p r) : Through k (Bulk.move q p) (Bulk.move q r) := by
  intro i hi; rw [Bulk.move, Bulk.move, coeff_mk,coeff_mk,h i hi]
lemma advances {k} {p q : Channel I} (h : Through k p q) : Through k (advance p) (advance q) := by
  intro i hi; rw [advance,advance,coeff_mk,coeff_mk]; exact sum_congr rfl fun j _=> by rw [Through.pow h _ i hi]
lemma transmitter (e e': Episode I B J) {v w : Channel I} {n} (h : Through n v w) (hr : e.joint=e'.joint) (hs : e.spur=e'.spur)
    (he:Through n e.vertices e'.vertices): Through n (e.floats v) (e'.floats w) := by
  unfold Episode.floats Bulk.transfer; dsimp only [AddMonoidHom.coe_mk,ZeroHom.coe_mk]; unfold Bulk.income; rw [hr,hs]
  apply Through.mul (moved e'.joint _ _ ((advances he).mul (restr _ _ h _))) (Through.invAlready (moved e'.joint _ _ (advances he)) ?_ ?_) <;>
    apply PowerSeries.mul_invOfUnit <;> rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply] <;> exact Bulk.accounting ..
end receipt
end YM.FormalOPE.RG10.Route
namespace YM.FormalOPE.RG10.Transit
open Route PowerSeries Function Finset
variable {U J : ℕ→Type} [∀ i,Fintype (J i)] (V : Voyage U J)
open Voyage
namespace Voyage
lemma pay {i j} (h:i ≤ j) (r: Series) (p:Channel (U j)) : V.yield i j (r • p) = r • V.yield i j p := by
  induction j,h using Nat.le_induction with
  | base => simp
  | succ j h ih => rw [V.send_next h,V.send_next h,(V.sail j).floats_smul,ih]
lemma currency {i j} (h:i ≤ j) (r: ℂ) (p:Channel (U j)) : V.yield i j (r • p) = r • V.yield i j p := by rw [← tower,← tower,pay V h]

def progress (i j : ℕ) (h : i ≤ j) : Channel (U j)→ₗ[Series]Channel (U i) where
  __:= V.yield i j
  map_smul':= pay V h

def constantProgress (i j : ℕ) (h : i ≤ j) : Channel (U j)→ₗ[ℂ]Channel (U i) where
  __:= V.yield i j
  map_smul':= currency V h
lemma worksAt {i j} (h:i ≤ j) (V' : Voyage U J) {r:ℕ} {p q:Channel (U j)}
    (hv : ∀ k∈Ico i j, (V.sail k).joint=(V'.sail k).joint ∧ (V.sail k).spur=(V'.sail k).spur ∧ Through r (V.sail k).vertices (V'.sail k).vertices) (ht : Through r p q): Through r (V.yield i j p) (V'.yield i j q) := by
  induction j,h using Nat.le_induction with
  | base=> simpa
  | succ j h ih =>
    rw [V.send_next h,V'.send_next h]; obtain ⟨h1,h2,h3⟩:= hv j (by simpa)
    exact ih (fun i hi=> hv i (Ico_subset_Ico le_rfl (Nat.le_succ _) hi)) (transmitter _ _ ht h1 h2 h3)
end Voyage
end YM.FormalOPE.RG10.Transit
