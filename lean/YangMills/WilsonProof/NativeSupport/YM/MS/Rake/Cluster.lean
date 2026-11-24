import YM.MS.Rake.Cluster
import YM.MS.Rake.Hour
/-!
# Position clusters. Sector coefficient for each named subset. Multiplication convention no extra source signs when even all, or sole possible odd has smallest header. Normalized cumulants.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Rake
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Heat Tone Momentum Landau Detect Book High Frame Flux Osc Fiddle Snap City Wire Wind Signal Latch Job Belt
open Garment Outlook
open Book.Convolve Geo
open scoped Topology ContDiff Interval
variable {I W:Type}[LinearOrder W]{G:Gauge}
abbrev Site (G: Gauge) (I:Type):= Book.Convolve.T (Glade G I) -- actually T ns? check
abbrev Dance (G:Gauge)(I W:Type):= Finset W→ Site G I
-- prep positions.Booleans root.Sep.
def Mesh (P:Geo I)(x:Position W I): Prop:= ∀ i j:W,i≠j→ CoverSep P (x i - x j)
variable {x:Position W I}{P:Geo I}{K L:Planet G I}{X Y: Dance G I W}{F:Site G I}{s t:Finset W}{w:W}{G':W→ Site G I}{b:Bool}
lemma n_small (h:t∈picks s ): t ⊂ s∧t.Nonempty∧ (s\ t).Nonempty ∧ (s \ t)⊂ s:= by
   by_cases hx:s.Nonempty; swap; · simp [ picks,hx ] at h
   simp only [picks, mem_filter, Finset.mem_powerset,hx, ↓reduceDIte] at h; obtain ⟨h,h1,h2⟩:= h; have hu:=min'_mem s hx; refine ⟨ lt_of_le_of_ne h (fun hh=> h2 (hh.symm ▸ hu)), h1, ⟨ _, mem_sdiff.mpr ⟨ hu,h2 ⟩⟩,?_⟩; rw [Finset.ssubset_iff_subset_ne]; refine ⟨Finset.sdiff_subset,?_⟩; intro he; obtain ⟨i,hi⟩:=h1; exact (Finset.mem_sdiff.mp (he.symm ▸ h hi)).2 hi -- `hu` hh.symm ... potential rew
lemma clips (h:s.card=1)(ht:t∈picks s): False:= by obtain H:=n_small ht; have he:= Finset.card_lt_card H.1; obtain hv:=Finset.card_pos.mpr H.2.1; omega
lemma unfT (x:Position W I)(h:t∈picks s): rootX x s=rootX x (s\ t):= by
   obtain ⟨H,hx,hv,he⟩:=n_small h; have hK := hx.mono (H.le); rw [ rootX,dif_pos hK,rootX,dif_pos hv ]; refine congr_arg x ?_; have hu: s.min' hK ∈ s\ t:= by
      refine mem_sdiff.mpr ⟨ min'_mem s hK,?_ ⟩; obtain ⟨_,hy,h⟩:= Finset.mem_filter.mp h; simpa only [hK,↓reduceDIte] using h
   exact le_antisymm (Finset.min'_le _ _ ((subset_of_ssubset he) (min'_mem _ _))) (Finset.min'_le _ _ hu)
-- require all distinct. constant-anchor difference
lemma space (h:Mesh P x) (ht:t∈picks s): CoverSep P ( rootX x t-rootX x s ):= by obtain ⟨hh,hT,H⟩:= n_small ht; let p:=s\ t; have hx:= H.1; rw [unfT x ht,rootX, rootX,dif_pos hT,dif_pos hx]; refine h _ _ ?_; intro he; exact (( mem_sdiff.mp ( min'_mem p hx)).2) ( he ▸ min'_mem t hT )
-- source formulas. B bulk. helper Region. gauge closure later.
def expJ (K:Planet G I)(F H:Glade G I): Glade G I:= fun i t=> tree parity (K i t) ( F i t ) ( H i t )
def regionC (μ:I→Measure QP)(x:I→QP)(P:Planet G I)(F H:Glade G I): Glade G I:= fun i t=> Cabin ( x i ) (P i t) (μ i) ( F i t ) ( H i t )
def lonely (P:Planet G I)(F H:Site G I)(k:ℕ) : Glade G I:= ∑ i∈Domain.paths k 0, expJ P (F (k-i)) (H i)
def multi (μ:I→Measure QP)(x: Position W I)(K L: Planet G I)(F H: Site G I)(A: Dance G I W) (k:ℕ)(s:Finset W): Glade G I:= lonely K F H k + ∑ i∈ picks s,∑ j∈ antidiagonal k, regionC μ (rootX x i-rootX x s) L ( A i j.1 ) ( A (s\ i) j.2 )
-- need H in multi because recursion curr X self.Head.Next lower tuple order
abbrev Fields (x:Position W I)(μ:I→Measure QP)(K L:Planet G I)(F:Site G I)(m:W→ Site G I)(X:Dance G I W): Prop:= X ∅=0∧ (∀ i:W,X {i}=m i) ∧ ∀ s:Finset W,2≤s.card→∀ n:ℕ, Trip (sailP μ L) (X s n) (multi μ x K L F (X s) X n s )
lemma perfect {μ:I→ Measure QP} (hf₁: Fields x μ K L F G' X) (hf₂: Fields x μ K L F G' Y): X=Y:= by
   funext s; induction s using Finset.strongInductionOn
   
   rename_i s ih
   rcases lt_or_ge s.card 2 with he|he
   · obtain hx|hx:= ( by omega: s.card=0 ∨ s.card=1 ); · rw [Finset.card_eq_zero.mp hx, hf₁.1,hf₂.1]
     obtain ⟨v,h⟩:= Finset.card_eq_one.mp hx; rw [h, hf₁.2.1, hf₂.2.1]
   funext k; induction k using Nat.strong_induction_on with
   | h k hK=>
     obtain H:= hf₂.2.2 s he k; suffices hp: multi μ x K L F (Y s) Y k s=multi μ x K L F (X s) X k s from Duty.consistent ( retire L μ ) ( hf₁.2.2 s he k ) (hp ▸ H); unfold multi lonely; refine congr_arg₂ (· + ·) ( Finset.sum_congr rfl (fun i hi=>?_)) ( Finset.sum_congr rfl fun i hi=> Finset.sum_congr rfl fun j hj=>?_ ); · rw [hK i (( mem_Ico.mp hi ).2)]
     rw [ih i (n_small hi|>.1), ih _ (n_small hi|>.2.2.2)]
end YM.MS.Rake
