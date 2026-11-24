import YM.Comparison.RG02.Assembly.Vertices
import YM.Comparison.RG02.Order.Pay
/-!
# Mixed radial orders

Uniform (in the stipulated norm-ball of the direction) *analytic comparison for the
identification of coefficients*. No claim on region of usefulness in a changing volume.
Constants from baseline `Built`, may depend on all data, here on a single fixed space.
No mixing different physical protocols. These are not estimates on a sum over an advancing
window of regulators, or costs for analytic remainder under integration.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Assembly
open Function Finset Filter MeasureTheory
open YM.Marker YM.Multi
open YM.PertExtension.Series YM.Comparison.RG02.Order
open scoped Topology BigOperators Classical ContDiff
variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
    {U : Type*} (Z : Zone U) {W' W X : U→ℝ}

/-- Compatibility of analytic extraction to PowerSeries statements used throughout the
 formal step. (This is not saying that the series converges as any element of a normed ring.) -/
def rows (p : U → PTable R) (s : R.Mode) (t : ℕ) (u : U) :=
    ((PowerSeries.coeff t) (p u)).part s

def Zonal (W : U→ ℝ) (f : ℝ→U→Poly R) (p : U→PTable R) : Prop :=
    ∀ t:R.Mode,Z.Built W (fun x u=> (f x u).part t) (rows p t)

namespace Zonal
lemma zone_eval {p : U→PTable R} (s : R.Mode) (r : ℕ) (x:ℝ) (u:U) :
    (value (x:ℂ) (series R r (p u))).part s = Zone.eval (rows p s) r x u := by
  rw [vpart]; apply Finset.sum_congr rfl; intro i hi
  rw [observation _ _ (p u) (by simpa using hi), Complex.real_smul,Complex.ofReal_pow]; rfl
lemma remainder {f : ℝ→U→Poly R} {p : U→PTable R} (h : Zonal Z W f p) (s : R.Mode) (r : ℕ) :
    Z.Fits W (r+1) (fun x u=> (f x u).part s - (value (x:ℂ) (series R r (p u))).part s) := by
  simp_rw [zone_eval]; exact (h s).fits r

variable {Z} (hW : ∀ u,1≤ W u)
include hW in
omit [Fintype V] in
lemma const (a : Poly R) : Zonal Z W (fun _ _=> a) (fun _ => PowerSeries.C a) := by
  intro t
  convert Zone.Built.const (Z:=Z) (a.part t) hW using 1
  funext i x; simp only [rows, PowerSeries.coeff_C]; split <;> simp [*]

variable {p q : U→PTable R} {f g : ℝ→U→Poly R}
omit [Fintype V] in
lemma add (h : Zonal Z W f p) (he : Zonal Z W g q) : Zonal Z W (f+g) (p+q) := by
   intro s; convert (h s).add (he s) using 1
   · rfl
   funext i x; simp only [rows, Pi.add_apply, map_add, Poly.part_plus]
omit [Fintype V] in
lemma scale (z : ℂ) (h : Zonal Z W f p) : Zonal Z W (z•f) (z•p) := by
   intro s
   let L := (ContinuousLinearMap.id ℝ ℂ)
   have ht:=built_map _ _ (h s) (z • L)
   convert ht using 1
   · rfl
   funext i x; simp only [rows, Pi.smul_apply, PowerSeries.coeff_smul, Poly.part_smul]; rfl
include hW in
omit [Fintype V] in
lemma sum {ι:Type*} (s : Finset ι) {f : ι→ℝ→U→Poly R} {p:ι→U→PTable R} (h : ∀ i∈s,Zonal Z W (f i) (p i)) :
    Zonal Z W (∑ i∈s,f i) (∑ i∈s,p i) := by
  intro t; convert Zone.Built.fin_sum s (fun i hi=>h i hi t) hW using 1
  · funext i x; simp_rw [Finset.sum_apply, Poly.part_sum]
  funext i x; simp only [rows,Finset.sum_apply,map_sum,Poly.part_sum]

-- no termwise phase split or support selection.
private def single (f g : ℝ→U→Poly R) (x y z : R.Mode) : ℝ→U→ℂ :=
  if Poly.merges x y z then fun t u=> (f t u).part x * (g t u).part y else 0
private def singleJet (p q : U→PTable R) (x y z:R.Mode) := if Poly.merges x y z then Zone.mul (rows p x) (rows q y) else 0
omit [Fintype V] in
private lemma contributes (hf : Zonal Z W f p) (hg : Zonal Z W' g q) (x y z : R.Mode) :
    Z.Built (W*W') (single f g x y z) (singleJet p q x y z) := by
  unfold single singleJet; split
  next h => exact (hf x).prod (hg y)
  next h =>
    have H u:= (((hf x).prod (hg y)).fits 0).envelope u
    simpa using! (Zone.Built.const (Z:=Z) (0:ℂ) H)

omit [Fintype V] in
private lemma cash (s : R.Mode) : (fun r u=> (f r u * g r u).part s) = ∑ i, ∑ j, single f g i j s := by
  funext x u; simp only [Poly.part_mul,Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> ?_
  unfold single; split <;> rfl
omit [Fintype V] in
private lemma jetProd (z : R.Mode) : rows (p*q) z = ∑ i, ∑ j,singleJet p q i j z := by
  funext t u
  rw [rows, Pi.mul_apply,PowerSeries.coeff_mul,Poly.part_sum]; simp only [Poly.part_mul,Finset.sum_apply]
  rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _
  unfold singleJet; split
  next h=> rfl
  next h=> simp

omit [Fintype V] in
lemma mul (hf : Zonal Z W f p) (hg : Zonal Z W' g q) : Zonal Z (W*W') (f*g) (p*q) := by
  intro s; simp only [jetProd, Pi.mul_apply, cash s];
  have hw x:= (((hf s).prod (hg s)).fits 0).envelope x
  exact Zone.Built.fin_sum _ (fun _ _=> Zone.Built.fin_sum _ (fun _ _=> contributes hf hg _ _ s) hw) hw

omit [Fintype V] in
lemma pow1 (hf : Zonal Z 1 f p) (n : ℕ) : Zonal Z 1 (f^n) (p^n) := by
  induction n with
  | zero => rw [pow_zero,pow_zero]; simpa [Pi.one_def] using! (Zonal.const (fun _=>le_rfl) (1 : Poly R))
  | succ n ih=> rw [pow_succ,pow_succ]; simpa only [one_mul] using ih.mul hf

omit [Fintype V] in
lemma send (q : R.Mode) {f : ℝ→U→ℂ} {p : ℕ→U→ℂ} (hf : Z.Built W f p) :
    Zonal Z W (fun t u=> Poly.send q (f t u)) (fun u=> PowerSeries.mk fun i=>Poly.send q (p i u)) := by
  intro t; by_cases h:t=q
  · unfold rows; simpa only [PowerSeries.coeff_mk,Poly.part_send, if_pos h] using hf
  unfold rows; simp only [ PowerSeries.coeff_mk, Poly.part_send, if_neg h]; simpa using!
    Zone.Built.const (0:ℂ) (V:=W) (Z:=Z) (hf.fits 0).envelope
end Zonal
end YM.Comparison.RG02.Assembly
