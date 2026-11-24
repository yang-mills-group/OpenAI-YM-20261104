import YM.FormalOPE.RG10.Boardwalk.Pavilion
import YM.FormalOPE.RG10.Carryon.Flash
/-! # Coefficientwise orientation budget (formal regulators, only finite order!) -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalOPE.RG10.Boardwalk
open Filter Function Finset PowerSeries Clearing Ledger Rates InversionTop
open Carryon PertExtension Position Maxwell Labels Extraction Filter Extra.FD
open PertExtension MeasureTheory Topology Metric PertExtension.Position Triangle
open scoped Topology BigOperators Classical
variable {I E F G J : Type*}{l:Filter I}
-- stick to complex/real. Want comm ring as PowerSeries (might mul not comm)
variable {R :Type*}[NormedCommRing R]
variable (P: Path l) (r:ℕ)
variable {u v w x y : I→ PowerSeries R}
abbrev Cost (x : I→PowerSeries R) := ∀ i≤r,Sized P (fun k=> coeff i (x k))
abbrev Flat (x : I→PowerSeries R) := ∀ i≤r,Prize P (fun k=>coeff i (x k))
-- budget & accuracy in ONE vane with $M_δ,Z$, exponent may be chosen smaller per horizon

def Posi (x y :I→ PowerSeries R) := ∀ i≤r,Fair P (fun k=>coeff i (x k)) (fun k=>coeff i (y k))
variable {P r}
namespace Posi
variable (h:Posi P r x y)
include h
lemma income : Cost P r x:= fun _ hi=> (h _ hi).size
lemma rights : Cost P r y:= fun _ hi=> (h _ hi).rights
lemma pays : Flat P r (fun i=>x i-y i):= by intro i hi; simp_rw [_root_.map_sub]; exact (h i hi).shift
lemma transit (h' : Posi P r y u): Posi P r x u:= fun i hi=> (h i hi).transit (h' i hi)
lemma reverse : Posi P r y x:= fun _ hi=> (h _ hi).flip
lemma fit (hp:∀ᶠ i in l, Through r (x i) (u i))(ht:∀ᶠ i in l,Through r (y i) (v i)): Posi P r u v:= fun i hi=> (h i hi).fit (hp.mono fun _ hh=> hh i hi) (ht.mono fun _ hu=> hu i hi)
lemma fits (he:x=ᶠ[l] u)(ht:y=ᶠ[l] v):Posi P r u v:= h.fit (he.mono fun i hi=> hi ▸ Through.refl (x i)) (ht.mono fun i hi=> hi ▸ Through.refl (y i)) -- direction x used twice
omit h
lemma ofFlat (hu:Flat P r (fun i=>x i-y i))(hv:Cost P r x) : Posi P r x y:= by
 intro i hi; exact ⟨hv _ hi, by simpa only [_root_.map_sub] using! hu i hi⟩
lemma same (h:Cost P r x): Posi P r x x:= fun _ hi=> Fair.same (h _ hi)
lemma fixed (x : PowerSeries R) : Posi P r (fun _=>x) (fun _=>x):= fun _ _=> Fair.fixed _
include h
lemma neg : Posi P r (fun i=>-x i) (fun i=>-y i):= by intro i hi; simp_rw [_root_.map_neg]; exact (h i hi).neg
lemma join (hp:Posi P r u v): Posi P r (fun i=> x i+u i) (fun i=>y i+v i):= by
 intro i hi; simp_rw [_root_.map_add]; exact (h i hi).join (hp i hi)
lemma minus (hp:Posi P r u v): Posi P r (fun i=> x i-u i) (fun i=>y i-v i):= by simp_rw [sub_eq_add_neg]; exact h.join hp.neg
lemma mul [NormedAlgebra ℝ R] (hp:Posi P r u v): Posi P r (fun i=> x i*u i) (fun i=>y i*v i):= by
 intro i hi; simp_rw [coeff_mul]; apply Fair.sum; intro j hj; rw [Finset.HasAntidiagonal.mem_antidiagonal] at hj; exact (h j.1 (by omega)).mul (hp j.2 (by omega))
lemma pow [NormedAlgebra ℝ R] (n:ℕ) : Posi P r (fun i=>(x i)^n) (fun i=>(y i)^n):= by
 induction n with
 | zero => simp_rw [pow_zero]; exact fixed _
 | succ n ih=>simp_rw [pow_succ];exact ih.mul h
omit h
lemma sum (s:Finset J) {x y : J→ I → PowerSeries R}(hu:∀ i∈s,Posi P r (x i) (y i)): Posi P r (fun i=>∑ k∈s,x k i) (fun i=>∑ k∈s,y k i):= by intro i hi; simp_rw [_root_.map_sum]; exact Fair.sum _ fun _ hk=> hu _ hk i hi
lemma product [NormedAlgebra ℝ R] (s:Finset J) {x y:J→ I → PowerSeries R}(hu:∀ i∈s,Posi P r (x i) (y i)): Posi P r (fun k=> ∏ i∈s,x i k) (fun k=>∏ i∈s,y i k) := by
 induction s using Finset.induction_on with
 | empty=>simp_rw [prod_empty];exact fixed _
 | insert i s hi ih=>simp_rw [prod_insert hi];exact mul (hu i (mem_insert_self ..)) (ih (fun j hj => hu j (mem_insert_of_mem hj)))
lemma showC {x y:I→ R}(h:Fair P x y) : Posi P r (fun i=> PowerSeries.C (x i)) (fun i=> PowerSeries.C (y i)):= by
 intro i _; simp_rw [coeff_C]; split
 · exact h
 exact Fair.fixed _

variable {a b : I→fps}{p q : I→ Carryon.Warp}
-- all reexpression in same direction, proof priced with all terms in x,p up to demand r
lemma century (h:Posi P r a b)(hz:Posi P r (fun i=>(p i).x) (fun i=>(q i).x)) : Posi P r (fun i=> (p i).charge (a i)) (fun i=> (q i).charge (b i)):= by
 intro k hk; simp_rw [Carryon.Warp.turning, AlignSeries.subst_finite (p _).atOrigin,AlignSeries.subst_finite (q _).atOrigin]; apply Fair.sum; intro j hj; exact (h j ((by simpa only [mem_range,Nat.lt_succ_iff] using hj : j ≤ k).trans hk)).mul (hz.pow j k hk) -- syntax
end Posi
end YM.FormalOPE.RG10.Boardwalk
