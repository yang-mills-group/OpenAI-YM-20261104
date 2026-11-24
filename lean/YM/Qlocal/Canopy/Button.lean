import YM.Qlocal.Glyph
import YM.RGComparison01.Marks.Slate
/-!
 # Turn the ratio estimator into a log estimator
 Snapshot of all switch jets at ALL physical occupations for one PowerSeries.
 Includes the common conditional factor (not scaled separately). Tapes supported
 about the physical connected log (no vacuum terms). Remains valid for multiple
 (complex-priced) stamps even when there is interference after turning on all of
 them; then later use convergence only at each permissible interaction.
 Real here; no assertion yet of multilinearity over complex source probes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Canopy
open Function Finset Filter Marker Merge Switch
open Comparison.RG02.Order Comparison.RG02.Cumulants Comparison.RG02.Assembly
open PertExtension PertExtension.Series AllOrder.Laplace AllOrder.Laplace.SigmaP
open AllOrder.Response Extra.Trajectories Next.SectorChange
open scoped Topology ContDiff BigOperators Classical
variable {ι σ : Type} [Fintype ι]
variable {V:Type} [DecidableEq V] {R:Census V} (K:ι→Poly R)
namespace Button
open Bind
abbrev Book (ι:Type):= ℕ→Score ι
def scribe (K:ι→Poly R) (f:Book ι) : PTable R:= PowerSeries.mk (fun i=> mapScores R K (f i))
variable {K}
-- Needed both pointwise (for geometry) and graded. No dependency on Fintype V restriction.
abbrev plan (O:Score ι): Poly R:=mapScores R K O
-- autoImplicit false means {K}
theorem written (K:ι→Poly R) (f:Book ι)(i:ℕ): PowerSeries.coeff i (scribe K f)=mapScores R K (f i):= PowerSeries.coeff_mk ..
local notation "B"=> Book ι
variable {N m t r:ℕ} (O P: Book ι)
lemma plunge1 (K:ι→Poly R): scribe K (O+P)=scribe K O+scribe K P:=by ext1 i; simp only [map_add, written, Pi.add_apply]
lemma plunge2 (K:ι→Poly R): scribe K (O-P)=scribe K O-scribe K P:=by ext1 i; simp only [map_sub, written, Pi.sub_apply]
lemma binds (K:ι→Poly R) : scribe K (0:B)=0:= by ext1 i; rw [map_zero,written]; exact map_zero _
lemma plungec (K:ι→Poly R)(a:ℝ): scribe K (a•P)=(↑a:ℂ)•scribe K P:=by ext1 i; rw [PowerSeries.coeff_smul]; simp only [written,Pi.smul_apply,map_smul]; rfl
lemma binder {σ:Type*} (K:ι→Poly R)(s:Finset σ)(f:σ→B): scribe K (∑ i∈s,f i)=∑ i∈s,scribe K (f i):= by ext1 i; simp only [written,map_sum,Finset.sum_apply]
def neutral (ι:Type): Book ι:= fun i=> if i=0 then bench ∅ 1 else 0
lemma plunge_one (K:ι→Poly R) : scribe K (neutral ι)=1:= by
 ext1 i; rw [written,PowerSeries.coeff_one,neutral]; split_ifs; · rw [mapBench]; simp
 exact map_zero _
def pledge (O P:B): B:= fun i=> ∑ j∈(_root_.Finset.HasAntidiagonal.antidiagonal i : Finset (ℕ×ℕ)), comb 0 (O j.1) (P j.2)
variable (h:∀ i,K i*K i=0)
local notation "τ"=>scribe K
include h
lemma plunge_mul : τ (pledge O P)=τ O*τ P:= by ext1 i; rw [written,PowerSeries.coeff_mul, pledge,map_sum]; simp_rw [written,cap_combs K h]
def knot (f : B): ℕ→ B
 | 0=> neutral _
 | i+1=> pledge (knot f i) f
lemma plunger : τ (knot O m) = τ O ^m:= by induction m with
 | zero=>rw [knot,pow_zero]; exact plunge_one _
 | succ k ih=> rw [knot,pow_succ,plunge_mul _ _ h,ih]
omit h
def Grey (f:B) := ∀ i, f i ∅=0 -- real parser? Type
lemma stay (hV: Grey O) (i:Finset ι) (hp:i.card < m) j: knot O m j i=0:= by
 induction m generalizing i j with
 | zero=> omega
 | succ m ih=>
   rw [knot,pledge,Finset.sum_apply]; refine sum_eq_zero (fun k hk=> ?_); rw [RGComparison01.Slate.flesh]; refine sum_eq_zero fun ℓ hℓ=>?_; split
   next h=>
      by_cases h' : ℓ.2=∅; · rw [h',hV _,mul_zero]
      have hv:= Finset.card_pos.mpr (nonempty_iff_ne_empty.mpr h'); rw [h.1,card_union_of_disjoint h.2] at hp; rw [ih ℓ.1 (by omega),zero_mul]
   next h=> rfl
lemma perish (hV:Grey O)(hp:Fintype.card ι < m): knot O m=0:= funext fun i=> funext fun s=> stay O hV s (lt_of_le_of_lt (card_le_univ _) hp) i
abbrev tax (t:ℕ):= -((↑(t+1):ℝ))⁻¹
def connect (m:ℕ) (O:B) := ∑ i∈ range (m+1), tax i • knot (neutral ι - O) (i+1)
lemma agreed (i:ℕ): (↑(tax i):ℂ)= -((↑(i+1):ℂ))⁻¹ := by simp [tax]
lemma toll_free (hV:Grey (neutral ι - O))(hm:Fintype.card ι ≤ m)(hr:Fintype.card ι≤ r): connect m O=connect r O:= by
 let k:=Fintype.card ι; have he i (hi:k≤ i) : connect k O= connect i O:= by
   exact sum_subset (range_mono (by omega)) (fun t _ ht=> by rw [perish _ hV (lt_of_le_of_lt (show Fintype.card ι≤ t from by have hh:= not_lt.mp (mt Finset.mem_range.mpr ht); omega) (Nat.lt_succ_self _)), smul_zero]); -- syntax type.A
 exact (he m hm).symm.trans (he r hr)
variable [Fintype V]
include h
local notation "Φ"=>series R r (τ O)
lemma logarithm (hv: Grey (neutral ι - O)) (hp: UnitLeading (series R r (scribe K O))) (hm:Fintype.card ι ≤ m) : connected Φ=series R r (scribe K (connect m O)):= by
 let n:=Fintype.card (V⊕Fin r); let D:=Φ; let w (i:ℕ):= ((↑(tax i):ℂ)) • (1-D)^(i+1); let m':=m+n
 rw [toll_free O hv hm (show Fintype.card ι≤ m' from by omega), log_formula hp, connect, binder,map_sum]
 simp_rw [plungec, series_smul, plunger _ h, map_pow, plunge2, map_sub,plunge_one, map_one]; apply Eq.trans ?_ (b:=∑ i∈range (n+1),w i) ?_
 · simp_rw [w, agreed]; rfl
 exact sum_subset (range_mono (by omega)) (fun i hi hq=> by have hz:= not_lt.mp (mt mem_range.mpr hq); unfold w; rw [Poly.stops (1-D) (by rw [Extra.Trajectories.part_sub, show D.part _=1 from hp]; simp) _ (show n < i+1 from by omega), smul_zero])
end Button
end YM.Qlocal.Canopy
