import YM.GradedFar.Moving.Owner

/-!
# Moving prices at compact ratios
-/
namespace YM.FVA2.GradedFar.Moving
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Scale Dframe Jury Facets Growth
open MS.Book.Program
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n d e : ℕ} {I J : Type} {p : ℕ} (T : Filter I) (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G
local notation "ν"=> Teller.logNu 1
local notation "ψ"=> GroupS.ψ N.criterion M ν
local notation "K"=> Kseries N M
local notation "α"=> Measure.adjust N.scheme N.criterion
variable (r z : I→ℝ) (hr : Tendsto r T τ) (hz : ∀ᶠ i in T,z i∈Growth.Small) {simple : G.Simple}
    {A : Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
include H hr hz

omit hz H in
def timespan : Loft G I := -- not prop use def
    ⟨T,r,1,zero_lt_one,1,zero_lt_one,hr⟩
def resize (r z:ℝ) := r*exp z
lemma in_span : Loft.Mid (timespan (G:=G) T r hr) z := by
    cases H
    exact (hz.and ((Loft.climbs _ simple).eventually_ge_atTop doubling)).mono fun i ⟨hi,h⟩=>⟨hi.1,(show z i≤doubling from hi.2).trans h⟩
lemma span_nears : Tendsto (fun i=> resize (r i) (z i)) T τ := Loft.soon _ simple (in_span T N M r z hr hz H)
lemma scaled_g : Buys T (fun i=> g (resize (r i) (z i))) (g ∘ r) 1 := by
  apply budget_of T (C:=2) _ ((hr.eventually (positive_g simple)).mono fun i h=>h.le)
  filter_upwards [(Loft.gskin _ simple (in_span T N M r z hr hz H)).eventually_lt_const one_lt_two,hr.eventually (positive_g simple),
    (span_nears T N M r z hr hz H).eventually (positive_g simple)] with i h hq hp
  rw [pow_one, Real.norm_of_nonneg hp.le]; exact ((div_lt_iff₀ hq).mp h).le
variable (θ : ℝ→ℝ) (ht : Tendsto (fun r=> θ r/gYM G r) τ (𝓝 1))
include ht
omit hz in
lemma measuring : Buys T (fun i=>(θ (r i):ℂ)) (g ∘ r) 1 := by
    cases H
    exact budget_of T (C:=2) ((hr.eventually (paid_reading simple θ ht)).mono fun i h=>by rw [Complex.norm_real,Real.norm_eq_abs,pow_one]; exact h.2.2.2)
      ((hr.eventually (positive_g simple)).mono fun i h=> h.le)
lemma charged_theta : Buys T (fun i=> (θ (resize (r i) (z i)):ℂ)) (g ∘ r) 1 := by
    apply (measuring T N M _ (span_nears T N M r z hr hz H) H θ ht).trans
    have h:= scaled_g T N M r z hr hz H; unfold Buys at h; simp_rw [pow_one] at *; exact h

omit ht hr in
lemma term_fee {E : Type} [NormedAddCommGroup E] {x : ℝ→E}
    (hx : Continuous x) : Buys T (fun i=> x (z i)) (g ∘ r) 0 := by
  cases H
  obtain ⟨C,h⟩:= isCompact_Icc.exists_bound_of_continuousOn (s:=Growth.Small) hx.continuousOn
  exact budget _ (hz.mono fun i hi=> h _ hi)
omit ht hr in
lemma psi_lin : Till T (fun i=> tells (ψ (-z i))) (g ∘ r) p := fun j _=>
    term_fee T N M r z hz H (continuous_rhythm (psi_rhythm N M H j))
omit ht hr in
lemma K_lin : Till T (fun i=> names (K d (-z i))) (g ∘ r) p := fun j _=>
    term_fee T N M r z hz H (Kcontinuity N M H j d)
omit ht hr in
lemma train_lin : Till T (fun i=> names (train N M d (z i))) (g ∘ r) p := by
  simp_rw [train,revenue_names, composition_names]
  exact Till.revs T (Till.revs T (Till.const T _) (K_lin T N M r z hz H))
    (shifted T (psi_lin T N M r z hz H) (Till.const T _))

lemma shine (p d : ℕ) : Pays T (fun i=> chairs G d (Continuation.atColumn (train N M d (z i)) p (θ (r i))))
    (fun i=> names (train N M d (z i))) (g ∘ r) p (fun i=> (θ (r i):ℂ)) := ⟨train_lin T N M r z hz H,by
      simp_rw [column_by, sub_self]
      apply IsBigO.of_bound 0
      filter_upwards [hr.eventually (paid_reading simple θ ht)] with i hi
      simp⟩
lemma flux (p : ℕ) : Buys T (fun i=> bend N M (z i) p (θ (r i):ℂ)) (g ∘ r) 1 := by
  unfold bend blend; refine IsBigO.sum (fun j hj=> ?_); by_cases hi:j=0
  · subst j; simp_rw [tells,(tendsK N M H _).start,smul_zero]; exact isBigO_zero ..
  exact budget_times_smul T
    (budget_growth T (budget_pow T (measuring T N M r hr H θ ht) j) _ (show 1 ≤ j by omega) (jet_level _ ((shrink simple).comp hr)))
    (psi_lin T N M r z hz H j (Finset.mem_range_succ_iff.mp hj))

omit hz ht in
lemma collapses {E : Type} [NormedAddCommGroup E] {x : I→E} (hx : Buys T x (g ∘ r) p) (hp : 1 ≤ p) : Tendsto x T (𝓝 0) := by
    cases H
    refine hx.trans_tendsto ?_; have hh:= ((shrink simple).comp hr).pow p; rw [zero_pow (by omega : p≠0)] at hh; exact hh
-- total trial minus leading
lemma base_at (p d : ℕ) : Buys T (fun i=> chairs G d (Continuation.atColumn (train N M d (z i)) p (θ (r i))) - engine G d (z i)) (g ∘ r) 1 := by
    have he i : chairs G d (Continuation.atColumn (train N M d (z i)) p (θ (r i))) - engine G d (z i)=
        ∑ j∈(Finset.range (p+1)).erase 0, (θ (r i):ℂ)^j • names (train N M d (z i)) j := by
      rw [column_by, blend, ← Finset.add_sum_erase _ _ (Finset.mem_range.mpr (Nat.succ_pos p)),pow_zero,one_smul,names,train_dial N M H]; abel
    simp_rw [he]; apply IsBigO.sum; intro j hj; exact budget_times_smul T
      (budget_growth T (budget_pow T (measuring T N M r hr H θ ht) j) 1
        (show 1≤j by obtain ha:=Finset.ne_of_mem_erase hj; omega) (jet_level _ ((shrink simple).comp hr)))
      (train_lin T N M r z hz H j (Finset.mem_range_succ_iff.mp (Finset.mem_of_mem_erase hj)))
end
end YM.FVA2.GradedFar.Moving
