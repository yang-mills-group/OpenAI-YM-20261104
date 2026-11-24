import YM.OPE.Samples.Band
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Data.Fintype.Sort
/-!
# Choose layers of geometry (along any chosen minimal refinement)

Instead of estimating inter-group ratios by infinitesimal bookkeeping
with arbitrarily small projection exponents, we use actual size comparison.
A strict layer difference is *more* than any prescribed power of this
geometry's designated log accounting `T`. We can run it on the same `f`
for **every** needed sub-geometry and even for a newly dilated log
bookkeeping scale. No convergence hypothesis on those ratios of the offered
regions themselves. `Reward` means dominance in this layer sense, hence a
total preorder (over positive radii). Ultrafilters are used only inside the
proof of estimates, not to select an ope convention or limit.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Mountain
open Function Filter Finset Real Log
open scoped Classical Topology BigOperators -- avoid many macros
variable {I L X:Type*}{f:Ultrafilter L}{T x y z : L→ℝ}{i j k:I}
-- No intervals with empty layers. Prove by sorting strict ranks
-- (how many strictly below).
structure Ranking (s:Finset I)(R:I→I→Prop)(v:I→ℕ)(m:ℕ) : Prop where
    bounded (i:I): i∈s→ v i≤ m
    realizes (k:ℕ) : k ≤ m → ∃ i∈s, v i=k
    compares (i j:I) : i∈ s→ j∈ s→ (R i j ↔ v i ≤ v j)

lemma ranked {s: Finset I}{R:I→I→Prop} (hs:s.Nonempty)
    (hc:∀ i∈ s,∀ j∈s,R i j ∨ R j i)
    (ht:∀ i∈s,∀ j∈s,∀ k∈s,R i j → R j k → R i k):∃ v m, Ranking s R v m:=by
    let S (i:I):= s.filter fun j=>¬R i j; let K i:= (S i).card
    have he : ∀ i∈s,∀ j∈s,R i j ↔ K i ≤ K j:=by
       have hu : ∀ i∈ s,∀ j∈s,R i j→ S i ⊆ S j:= by
          intro i hi j hj hij x hx; obtain ⟨hx,he⟩:= mem_filter.mp hx; exact mem_filter.mpr ⟨hx,fun hp=> he (ht i hi j hj x hx hij hp)⟩
       intro i hi j hj; refine ⟨fun h=>card_le_card (hu i hi j hj h),fun h=>?_⟩; by_contra H; apply not_lt_of_ge h; refine card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hu j hj i hi ((hc i hi j hj).resolve_left H),fun h=>?_⟩); exact (mem_filter.mp (show j∈ S j from h.symm ▸ mem_filter.mpr ⟨hj,H⟩)).2 ((hc j hj j hj).elim id id)
    let C:= s.image K; let V i (hi:i∈s) : C:= ⟨K i, mem_image_of_mem K hi⟩; let ω:= C.orderIsoOfFin rfl;
    let v i:= if h:i∈s then (ω.symm (V i h)).val else 0; have hN: 0 < C.card:= card_pos.mpr (Nonempty.image hs _)
    refine ⟨v,C.card-1,?_⟩; constructor
    · intro i hi; unfold v; rw [dif_pos hi]; exact Nat.le_sub_one_of_lt (ω.symm (V i hi)).isLt
    · intro i hi; let q:Fin C.card:=⟨i,by omega⟩; obtain ⟨x,hx,hp⟩:= (mem_image.mp (show (ω q).val∈ s.image K from (ω q).property)); have he: V x hx=ω q:=Subtype.ext hp; refine ⟨x,hx,?_⟩; unfold v; rw [dif_pos hx,he, OrderIso.symm_apply_apply]
    · intro i j hi hj; unfold v; rw [dif_pos hi,dif_pos hj, ← Fin.le_def]; exact (he i hi j hj).trans ((show V i hi ≤ V j hj ↔ ω.symm (V i hi) ≤ ω.symm (V j hj) from (OrderIso.le_iff_le ..).symm)) -- order inspect

/-- Eventual upper cost from x (dominator) to y. -/
def Reward (f:Filter L) (T x y:L→ℝ): Prop:= Wallet f T (fun i=> y i/x i)
namespace Reward
variable (h:Tendsto T (f:Filter L) atTop)(hx:∀ᶠ i in f,0<x i)(hy:∀ᶠ i in f,0<y i)
include h hx hy
lemma credit (he:∀ᶠ i in f,y i ≤ x i):Reward f T x y:= (Wallet.const h (1:ℝ)).of_le' ((hx.and hy).mono (fun i hi=> div_pos hi.2 hi.1)) ((hx.and he).mono fun i hi => (div_le_one hi.1).mpr hi.2)
lemma bid : Reward f T x y ∨ Reward f T y x:= (Ultrafilter.eventually_or.mp (Eventually.of_forall fun i:L=>le_total (y i) (x i))).imp (credit h hx hy) (credit h hy hx)
omit h hx hy
lemma join (hy:∀ᶠ i in f,0< y i) (ha: Reward f T x y)(hb:Reward f T y z): Reward f T x z:= (ha.mul hb).congr (hy.mono fun i hi=> by
    simp only [div_eq_mul_inv]; ring_nf; field_simp) -- hb orientation? ring_nf/field_simp if x=0.L.
include h hx hy
lemma beats (he: ¬ Reward f T y x) (p:ℕ): Tendsto (fun i=> y i/x i*T i^p) (f:Filter L) (𝓝 0):=by
    refine tendsto_order.mpr ⟨fun a ha=>?_, fun a ha=> ?_⟩
    · filter_upwards [hx,hy,h.eventually_ge_atTop 0] with i hx hy h using ha.trans_le (mul_nonneg (div_pos hy hx|>.le) (pow_nonneg h _))
    apply Or.resolve_right (f.em (fun i=>y i/x i*T i^p< a)); intro H; apply he; apply ((Wallet.const h a⁻¹).mul ((Wallet.id h).pow h p)).of_le';
    · filter_upwards [hx,hy] with i hx hy using div_pos hx hy
    filter_upwards [hx,hy,H] with i hx hy hH
    rw [div_le_iff₀ hy]; rw [show a⁻¹*T i^p * y i= (y i * T i^p)/a by rw [div_eq_mul_inv]; ring]; rw [le_div_iff₀ ha]; rw [mul_comm (x i)]; refine (le_div_iff₀ hx).mp (le_of_not_gt ?_); convert hH using 1; ring_nf -- order not typo

-- two extremal representatives in each class
omit h hx hy
lemma minOffer {s: Finset I}(r:L→I→ℝ) (hs:s.Nonempty): ∃ i∈s,∀ᶠ j in f, ∀ x∈s,r j i ≤ r j x:=by
    classical
    by_contra! h
    have he := (eventually_all_finset (l:=(f:Filter L)) s).mpr (fun i hi=> h i hi)
    obtain ⟨j,hj⟩ := he.exists
    obtain ⟨i,hi,hx⟩:= exists_min_image s (r j) hs
    obtain ⟨u,hu,hv⟩:= hj i hi; exact hv.not_ge (hx u hu)
lemma maxOffer {s: Finset I}(r:L→I→ℝ)(hs:s.Nonempty): ∃ i∈s,∀ᶠ j in f,∀ x∈s,r j x ≤ r j i:=by
    simpa using (@minOffer I L f s (fun j i=> - r j i) hs) -- @ order
end Reward
end YM.OPE.Mountain
