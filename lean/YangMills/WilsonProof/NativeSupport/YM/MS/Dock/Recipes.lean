import YM.MS.Dock.Recipes
import YM.MS.Dock.Dance
/-!
# Bulk and mark specifications for MS scheme.

Full coefficients, not evaluation after field change. Include spin/projection only when taking limits. `B`: input seed homogeneous (renormalized perturbative interaction polynomial part). More precision below. Normalization already feeD.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Dock
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine Hem Mell Logarithm Pearl Train
open Signal Book Convolve Garment.Wave Garment.Wick
open scoped Topology ContDiff Interval
variable {I A:Type}{G:Gauge}{X Y F:T (Flats G)}{b c:Bool}{t v r:ℤ}{n m h ℓ:ℕ}{i:ℂ}{a h' q p B:T (Coat G)}
-- pol actual from Hamilton law ℓ cost.
def program (G:Gauge) : Drive G:= fun k X=> (2:ℂ)⁻¹ • ∑ i∈ shortB k, drive0 G ( X i.1) ( X i.2)
def platform (F:T (Flats G)): Drive G:= fun k X=> ∑ i∈ shortM k,drive0 G ( F i.1) (X i.2)
lemma pb_u : lowD (program G) (program G):= by
    intro n F J h; apply pact_scaled; exact pact_sum _ (fun i hi=> pair_pact _ (h i.1 (Finset.mem_filter.mp hi|>.2.1)) ( h i.2 ( Finset.mem_filter.mp hi|>.2.2)))
lemma pm_u (hp:∀ i,Pact (F i) (X i)): lowD (platform F) (platform X):= by intro n F J h; exact pact_sum _ (fun i hi=> pair_pact _ (hp i.1) (h i.2 ( Finset.mem_filter.mp hi|>.2)))
lemma pb_coal (h:∀ i<n, Gang true 4 0 (X i)):∃ r,Coal true 4 0 r (program G n X) := by
    have hp := glow_sum ( shortB n) (fun i hi=> feed ( h _ ( Finset.mem_filter.mp hi|>.2.1)) (h _ (Finset.mem_filter.mp hi|>.2.2)) );
    obtain ⟨r,h⟩:=hp; exact ⟨_, glazer h _ (by simp) ⟩ -- int zero add
lemma pm_coal (he:∀ i<n, Gang false m t (X i))(ht: ∀ i,Gang true 4 0 (F i)):∃ r,Coal false m t r (platform F n X):= by
   apply glow_sum; intro i hi; obtain h:= feed (gangLo (b:=false) (ht i.1)) (he i.2 (Finset.mem_filter.mp hi|>.2)); simpa only [zero_add] using h
-- $ζ$ Full. name conflicts Bulk many. marks of weights from High.
abbrev Schema (b:Bool)(t:ℤ)(h:ℕ)(B:T (Coat G)) := ∀ n,Badge b (B n) h t
abbrev leader (G:Gauge)(X:T (Flats G))(B q:T (Coat G)):= LPT (program G) (fun i=>i=0) true 0 4 B X q
abbrev comet (h:ℕ)(g:ℤ)(B:T (Flats G))(a:T (Coat G))(X:T (Flats G))(q:T (Coat G)):= LPT (platform B) (fun _=>False) false g h a X q
lemma satisfy (hx:Schema true 0 4 B)(he:B 0=0): ∃ X q, leader G X B q:= by
    refine Ethics.pow ⟨ pb_u,fun n F q H=> ?_⟩; by_cases ht:n=0
    · subst n; rw [show program G 0 F=0 from ?_, he]; exact ⟨0,0, zero_sing _⟩; unfold program shortB; simp -- simp antidiag
    exact vocals ht (hx n) (pb_coal (fun i hi=> gang (H i hi)))
lemma satisfyY (hx:leader G X B q)(he:Schema false r h a):∃ Y s,comet h r X a Y s:= Ethics.pow ⟨ pm_u (fun _=>fun _=> EventuallyEq.rfl), fun n _ _ H=> vocals (fun h=>h) (he n) ( pm_coal (fun i hi=> gang (H i hi)) (fun i=>gang (hx i)))⟩
lemma pc_max (hp:X 0=0)(k:ℕ): program G k X= (2:ℂ)⁻¹ • pairW (drive0 G) X X k:= by
    unfold program; rw [paired]; refine congr_arg (( (2:ℂ)⁻¹ ) • ·) (Finset.sum_subset (Finset.filter_subset ..) (fun v hv ht=>?_)); obtain he:= Finset.mem_antidiagonal.mp hv; obtain h:v.1=0 ∨ v.2=0:= by simp only [shortB, Finset.mem_filter,hv,true_and] at ht; omega
    rcases h with h|h <;> first|simp [h,hp]
lemma pm_max (hp:F 0=0)(k:ℕ): platform F k X= pairW (drive0 G) F X k:= by
    unfold platform; rw [paired]; refine Finset.sum_subset (Finset.filter_subset ..) (fun i hi ht=>?_); obtain he:= Finset.mem_antidiagonal.mp hi; have hm:i.1=0:= by simp only [shortM,Finset.mem_filter,hi,true_and] at ht; omega
    simp [hm,hp]
lemma unique_B (h:leader G F B q)(he:leader G X B a): q=a∧∀ i,Pact (F i) ( X i):= LPT.unique h he pb_u
lemma unique_M {p' Y'}(ht:comet h r F a Y q)(he:comet h r X a Y' p')(hx:∀ i,Pact (F i) (X i)): q=p'∧∀ i,Pact (Y i) (Y' i):= LPT.unique ht he (pm_u hx)
end YM.MS.Dock
