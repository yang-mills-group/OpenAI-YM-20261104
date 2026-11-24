import YM.QuadraticLocal.Germ.Censor
import YM.QuadraticLocal.Shelter.Shadows
import YM.QuadraticLocal.Shelter.Pins
import YM.QuadraticLocal.Arrow
/-!
## Stable audit on wallet/loci. Witnesses across the exact mask change
 Allows using either Static (germs on allowed charts; sufficient before
 polishing) or the full representation after, Taut. Cost of moving actual
 masks at the full retained positions paid at Terrace. Programs over Wallet
 tests suffice *before* extending to complex talking. No inference from only
 pointwise amplitudes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Affinity.Polish
open Function Filter Finset MeasureTheory
open Marker Lattice Wilson RG
open PhysicalNext PhysicalNext.Repeat
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {θ I C ι μ : Type} [DecidableEq θ] {n c:Side}{G:Gauge}
variable {Φ:θ→Support n}{o:θ→ Site n}{Q:BudgetPoint}
variable {Y:θ→Type}[∀ i,AddCommGroup (Y i)]{𝕜:Type}[RCLike 𝕜][NormedAlgebra 𝕜 ℂ][∀ i,Module 𝕜 (Y i)]
variable {A:∀ i,Set (Y i)}{K:∀ i,Submodule 𝕜 (Y i)}
local notation "Z"=> Wallet A
variable {R:Census θ}{L:Lamps (Wallet A) I G Q o R} {M:Lamps (Wallet A) μ G Q o R}
lemma monomial {ι:Type*}{V:Type*}[NormedCommRing V][NormedAlgebra 𝕜 V] (s:Finset ι) (g:ι→ Finset θ) (v:ι→ Wallet A→ V)(h:∀ i∈s,Attn K A (g i) (v i))(ht:(s:Set ι).PairwiseDisjoint g): Attn K A (s.biUnion g) (fun u=> ∏ j∈s,v j u):=by
   induction s using Finset.induction with
   | empty=> simp only [biUnion_empty, prod_empty]; exact Attn.solid _
   | insert i s hi ih=> simp_rw [Finset.prod_insert hi,biUnion_insert]; refine (h i (mem_insert_self ..)).bind (ih (fun i hh=>h i (mem_insert_of_mem hh)) (ht.subset (Finset.coe_subset.mpr (Finset.subset_insert i s)))) ((disjoint_biUnion_right ..).mpr (fun j hj=> ht (mem_insert_self ..) (mem_insert_of_mem hj) (fun hv=>hi (hv.symm ▸ hj))))
lemma _root_.YM.QuadraticLocal.Affinity.Attn.neg {V:Type*}[NormedAddCommGroup V][NormedSpace 𝕜 V]{F:Wallet A→V}{s:Finset θ}(hf:Attn K A s F): Attn K A s (fun i=>-(F i)):= by simpa using hf.scale (-1:𝕜)
lemma _root_.YM.QuadraticLocal.Affinity.Attn.cs {F:Wallet A→ℂ}{s:Finset θ}(hf:Attn K A s F)(x:ℂ): Attn K A s (fun i=>x* F i):= hf.linear (Algebra.lmul 𝕜 ℂ x)
lemma _root_.YM.QuadraticLocal.Affinity.Attn.sc {F:Wallet A→ℂ}{s:Finset θ}(hf:Attn K A s F)(x:ℂ): Attn K A s (fun i=> F i*x):= by simp_rw [mul_comm _ x]; exact hf.cs _
-- helper for any affiliation audits and canopy.
namespace Static
lemma tutelage (h:Taut Φ A K L): Static A K L Φ:= ⟨fun i U _=> Eventually.of_forall fun x=> h.adv i x,fun i _ _ _=> h.house i⟩
lemma shadows (h:Static A K L Φ)(i:I)(U:Config G n): Attn K A (L.mode i).val fun t=> L.light t i U:=by
    unfold Lamps.light; split; next hv=> -- honor clear at one
       simp_rw [fun t=> L.pure t i U hv]; exact (h.honor i 1 (Next.Foundations.one_healthy _ _ Q.threshold_pos.le)).self_of_nhds
    next=>
      by_cases he:Healthy Q.threshold (L.ground i) U; · simp_rw [masked_eq _ _ _ _ he]; exact (h.honor i U he).self_of_nhds
      simp_rw [masked_ne _ _ _ _ he]; exact Attn.silent
lemma summon (h:Static A K L Φ)(f:ι→I):Static A K (L.summon f) Φ:=⟨fun i=> h.honor (f i),fun i=> h.fare (f i)⟩
lemma port (h:Static A K L Φ)(t:Static A K M Φ):Static A K (L.join M) Φ:=by
    refine ⟨?_,?_ ⟩ <;> rintro (i|i); exact h.honor i; exact t.honor i; exact h.fare i; exact t.fare i
lemma peer (h:Static A K (L.join M) Φ): Static A K L Φ ∧ Static A K M Φ:=⟨h.summon Sum.inl, h.summon Sum.inr⟩
lemma spawn (h:Taut Φ A K L)(h':Taut Φ A K M): Taut Φ A K (L.join M):=by refine ⟨?_,?_⟩ <;> rintro (i|i); exact h.house i; exact h'.house i; exact h.adv i; exact h'.adv i
lemma lunar (h:Taut Φ A K L): Taut Φ A K (L.shade):= ⟨h.house,fun i U=> (h.adv i U).neg⟩
lemma past (S:StepData c n)(h:Taut Φ A K L)(P:BudgetPoint): Taut (fun v=>(Φ v).image S.ratio.parent) A K (Spire.convertGlobal L S P):= ⟨fun i v h'=> image_subset_image (h.house i.val v h'), fun i U=>h.adv i.val 1⟩
-- Round and soap audit. Uphold at ALL configurations. Never infer from Healthy⊂boundary
open Shelter
variable {N:Lamps (Wallet A) ι G Q o R}{α β γ:C→Type}{H:ℕ}{D: Terrain C R}
variable [∀ i,Fintype (α i)][∀ i,Fintype (β i)][∀ i,Fintype (γ i)]
variable (d: Shelter.Deck L D H α)(d': Shelter.Deck M D H β)(d₀:Shelter.Deck N D H γ)
variable (hL:∀ (i:C)(t:Wallet A)(U:Config G n), Healthy Q.threshold (D.barrier o H i) U→ d.white i t U=d'.white i t U+d₀.white i t U)
include d
lemma spills (h:Static A K L Φ)(i:C)(U:Config G n) : Attn K A (D.mode i).val (fun t=> d.round i t U):= Attn.total _ _ (fun a _=> show Attn K A (D.mode i).val (fun t=> L.light t (d.enrol ⟨i,a⟩) U) from (d.calls ⟨i,a⟩ ▸ h.shadows (d.enrol ⟨i,a⟩) U)) -- parse
local notation "K₁"=> (Shelter.Deck.soap d d' d₀ hL)
lemma helm (h:Static A K L Φ)(h':Static A K M Φ)(hr: Static A K N Φ) (hp:∀ i v,v∈(D.mode i).val→ Φ v ⊆ D.barrier o H i)(i:C)(U:Config G n): Stencil Φ A K (D.barrier o H i) (fun t=> (K₁).soap t i U):=by
    refine ⟨fun j=>?_⟩; change Addressable _ _ _ _ _ (fun t=> (Poly.send (D.mode i) _).part j); simp_rw [Poly.part_send]; split; next ht=>
      subst j; simp_rw [sub_eq_add_neg]; exact ⟨((h.spills d i U).plus ((h'.spills d' i U).neg)).plus ((hr.spills d₀ i U).neg),fun b _ v hv=> hp i v hv⟩
    next=> exact Addressable.gone
end Static
end YM.QuadraticLocal.Affinity.Polish
