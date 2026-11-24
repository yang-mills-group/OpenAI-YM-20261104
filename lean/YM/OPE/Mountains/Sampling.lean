import YM.OPE.Mountains.Ram
/-! # Uniform joint cost triggers under finite assumptions only.

Proof by counter-sequences on intervals like the utility in Log/Uniform,
with one further refinement to realize the new full-tree rate/accounting.
Also handle any additional qualifier tests about injectivity etc. as long
as they meet these same progression rules. No compactness of the full set
of configurations requested. Ratios hence in exact indicated range, none
bounded from below. Exact sum-of-powers at the requested horizons not only
when all ratios small. The exponent and thresholds can of course increase
over any finite list of requests.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Mountain
open Function Filter Finset Real OPE.Log
open scoped Classical Topology BigOperators ContDiff
set_option quotPrecheck false
local notation "ν"=> 𝓝[>] (0:ℝ)
private lemma every {V:Type*}{g:ℝ→V→Prop}{h: V→ℕ→ Prop} (hp:∀ (x:ℕ→V)(r:ℕ→ℝ)(χ:Ultrafilter ℕ), Tendsto r (χ: Filter ℕ) ν → (∀ᶠ i in χ,g (r i) (x i))→ ∃ p :ℕ,∀ᶠ i in χ,∀ k:ℕ,p≤k → h (x i) k) : ∃ p:ℕ, ∀ᶠ r:ℝ in ν,∀ x:V,g r x → ∀ k:ℕ,p≤k → h x k:=by
    by_contra! hf
    have he(i:ℕ):∃ r:ℝ,0<r∧r ≤ Real.exp (-(i:ℝ))∧ ∃ x:V,g r x ∧ ∃ k:ℕ,i≤k ∧ ¬ h x k:=by
       obtain ⟨r,hr,hR,hx⟩:= ((show ∃ᶠ r in ν,∃ x, g r x∧ ∃ k,i ≤ k∧ ¬ h x k from hf i).and_eventually ((show ∀ᶠ i in ν,0 < i from self_mem_nhdsWithin).and ((ge_mem_nhds (Real.exp_pos (- (i:ℝ)))).filter_mono nhdsWithin_le_nhds))).exists; exact ⟨r,hR,hx,hr⟩
    choose r hr hR x hX k hk hv using he
    have hT:Tendsto r atTop (𝓝 0):= squeeze_zero' (Eventually.of_forall fun i=> (hr i).le) (Eventually.of_forall hR) (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop))
    let Z:Ultrafilter ℕ:=Ultrafilter.of atTop; have he':(Z:Filter ℕ)≤ atTop:= Ultrafilter.of_le _
    obtain ⟨p,hp⟩:= hp x r Z (tendsto_nhdsWithin_iff.mpr ⟨hT.mono_left he',Eventually.of_forall hr⟩) (Eventually.of_forall hX); obtain ⟨i,hf,hh⟩:= (hp.and ((eventually_ge_atTop p).filter_mono he')).exists; exact (hv i) (hf _ (hh.trans (hk i)))

variable {G:Gauge}{C:Family G}{F: Extraction.Order}{S:Table C.book}(U:Spec.Final C F S)
    {P:Prescription U.sector.derivatives} (hP:P.Coherent)
variable (H:Services C F S) {φ:Filter (ℕ×ℕ)} [φ.NeBot] (hf:φ ≤ F.fuse)
    {W r d}(V:LogPackage C W r d) (hG:MatrixTicket (C:=C) S U.sector.derivatives φ)
variable {I J K:Type}[Fintype I][Fintype J] {s:Arboreal I} {χ:Ultrafilter K}
    {x:K→I→ E4}{R:K→I→ℝ}{u:K→ℝ}{M δ c:ℝ}
    (p:I→ C.book.Token) (q:J→ C.book.Token)(n:ℕ)(D:I→ℕ)(w:Mode U.sector.derivatives)
variable (hm:0≤M)(hd:0<δ)
include hm hd
private lemma transfer (hu: Tendsto u (χ:Filter K) ν)(hv:∀ᶠ j in χ, R j s.root=u j)(h:∀ᶠ j in χ,s.Convoy M δ (R j) (x j)): ∃ t,s.Coterie (χ:Filter K) t M δ x R:=by
    have he:= hu.congr' (hv.mono fun i hi=> hi.symm); obtain ⟨φ,hφ,h',t,ht⟩ := phase_rates (h.mono fun i hi=> hi.sizes) he; exact ⟨t,h,hm,hd,χ.unique hφ ▸ ht,he⟩
include H hf V hG hP
lemma pricing (s:Arboreal I): ∃ p':ℕ, ∀ᶠ r:ℝ in ν,∀ (x:I→ E4)(t:I→ℝ), t s.root=r→ s.Convoy M δ t x→ ∀ k:ℕ,p'≤k→ LogRate U s P w p D x t k:=by
    let Q (u:ℝ)(x:(I→ E4)×(I→ℝ)):= x.2 s.root=u∧ s.Convoy M δ x.2 x.1
    obtain ⟨k,hk⟩:= every (g:=Q) (h:=fun x i=> LogRate U s P w p D x.1 x.2 i) (fun x r χ hu h=> by obtain ⟨t,ht⟩:= transfer (R:=fun i=>(x i).2) hm hd hu (h.mono fun i hi=> hi.1) (h.mono fun i hi=> (show s.Convoy M δ ((x i).2) ((x i).1) from hi.2)); exact bill U hP H hf V hG p D w ht)
    exact ⟨k,hk.mono fun r hr x t h1 h2=> hr (x,t) ⟨h1,h2⟩⟩
lemma pricing_error (s:Arboreal I)(hc:0<c): ∃ p':ℕ, ∀ᶠ r:ℝ in ν,∀ (x:I→ E4)(t:I→ℝ)(y:J→E4), t s.root=r→ s.Convoy M δ t x → ClearOf (x s.root) y c→ ∀ k:ℕ,p'≤k → LogError U s P p q n x t y k:=by
    let Q (u:ℝ)(x:(I→ E4)×(I→ℝ)×(J→E4)):= x.2.1 s.root=u∧ s.Convoy M δ x.2.1 x.1∧ ClearOf (x.1 s.root) x.2.2 c
    obtain ⟨k,hk⟩:= every (g:=Q) (h:=fun x i=> LogError U s P p q n x.1 x.2.1 x.2.2 i) (fun x r χ hu h=> by obtain ⟨t,ht⟩:= transfer (R:=fun i=>(x i).2.1) hm hd hu (h.mono fun i hi=> hi.1) (h.mono fun i hi=> (show s.Convoy M δ ((x i).2.1) ((x i).1) from hi.2.1)); exact stage (Y:=fun i=>(x i).2.2) U hP H hf V hG p q n ht ⟨c,hc,h.mono (fun i hi=> hi.2.2)⟩)
    exact ⟨k,hk.mono fun r hr x t y h1 h2 h3=> hr (x,t,y) ⟨h1,h2,h3⟩⟩
end YM.OPE.Arboreal.Mountain
