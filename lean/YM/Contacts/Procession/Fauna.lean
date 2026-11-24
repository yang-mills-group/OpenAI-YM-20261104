import YM.Contacts.Procession.Pillar
/-! # Mark Faa activation sectors. Passing gauge gradients under actual (native) travel. -/
noncomputable section
namespace YM.Contacts.Procession.Hinges
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Sun Xenon Kale Garf PertExtension.Series Radial Larch Ion Convoy Lumen Welcome Resetter Shuttle.Tide Barrage
open scoped Classical Topology BigOperators NNReal Matrix ContDiff Matrix.Norms.Frobenius
set_option autoImplicit false
variable {X Y A B ι κ α β: Type}{n m:Side} {k r:ℕ}{b c:ℝ}
variable {p:X→Y}{q:A→B}{a:X}{u:A}
section tuft
variable (q:κ→ι)(h:Surjective q)
private def thrust (h:Surjective q)(X:Type) : (ι→X) ↪ (κ→X):= ⟨(· ∘ q), fun _ _ H=> funext (h.forall.mpr fun i=> congr_fun H i)⟩
variable {F: Field ι X}{l:Pulse.Range X}{z:X}{m:Side}
include h
lemma puff_pack (p:X→Y)(F: Field ι X): packing p (fans q F)= fans q (packing p F):= by
    let u:=thrust q h X; let v:=thrust q h Y; have hx (x): hinge p (u x)= v (hinge p x):= rfl
    funext y; unfold packing; rw [expand_eq, ← u.injective.tsum_eq]; swap; · intro x hx; by_contra hv; apply hx; dsimp only; rw [show fans q F x=0 from dif_neg (show x∉ Set.range (fun x:ι→X=> x ∘ q) from hv),ite_self]
    simp_rw [hx, show ∀ x,fans q F (u x)=F x from fun x=> fans_read q h F x]; by_cases he:y∈Set.range v; · obtain ⟨i,rfl⟩:= he; simp_rw [v.injective.eq_iff]; exact ( (fans_read q h (packing p F) i).trans (expand_eq ..)).symm
    simp only [show fans q (cram (hinge p) F) y=0 from dif_neg (show y∉ Set.range (fun x:ι→Y=> x∘ q) from he),fun x=> ne_of_mem_of_not_mem (show v x∈ Set.range v from Set.mem_range_self _) he,↓reduceIte,tsum_zero]
lemma puff_price [Fintype ι][Fintype κ](ht:Rest l z F b): Rest l z (fans q F) b:= by
    let A:=thrust q h X; let G (x:κ→X):= ‖fans q F x‖*fee l z x; have hm (x)(hx:x∉ Set.range A): G x=0:= by unfold G; rw [show fans q F x=0 from dif_neg (show x∉ Set.range (fun x:ι→X=> x ∘ q) from hx)]; simp
    have hp:SumBudget (G ∘ A) b:= by rw [show G ∘ (⇑A)=_ from (show _=(fun x:ι→X=> ‖F x‖*fee l z x) from funext fun x=> by change ‖fans q F (x∘ q)‖ * _=_; rw [fans_read q h]; exact congr_arg _ (fans_fee q h x))]; exact ht
    refine ⟨fun _=>mul_nonneg (norm_nonneg _) (fee_plus _),?_⟩; have he:= (A.injective.hasSum_iff (a:=tsum (G∘A)) hm).1 hp.2.1.hasSum; exact ⟨he.summable,he.tsum_eq.le.trans hp.2.2⟩
end tuft
lemma zip_pack (F: Field ι (Node β))(W:Field ι β)(m:Side): packing (lower m) (faceCost Cover W F)= faceCost (Site m) W (packing (lower m) F):= by
    funext i; unfold packing faceCost cram; rw [←tsum_mul_left]; apply tsum_congr; intro w; change W (Prod.snd ∘ w.val)*_=_; congr! 2; exact congr_arg (Prod.snd ∘ ·) w.property
lemma zip_price [Fintype ι][Fintype β] (F:Field ι (Node β))(W:Field ι β){x:Node β}{t: Pulse.Range (Node β)}(h:Rest t x F b): Rest t x (faceCost Cover W F) ((∑ i:ι→β,‖W i‖)*b):= budget_mono (budget_scale (sum_nonneg (fun _ _=>norm_nonneg _)) h) (fun i=>mul_nonneg (norm_nonneg _) (fee_plus i)) (fun i=> by unfold faceCost; rw [norm_mul,mul_assoc]; exact mul_le_mul_of_nonneg_right (single_le_sum (fun i _=>norm_nonneg (W i)) (mem_univ _)) (h.1 i))
variable [Fintype ι][Fintype α][Fintype β]
variable (F:Barrage.Pattern ι α β)(p:OrderedFinpartition k)
variable {z: Field (Fin p.length) (Node β)}{σ η:ℝ≥0}{x:α}{y:β}
open Barrage.Pattern
private lemma throat (p:OrderedFinpartition k): Surjective (Sigma.fst:Graph p→ Fin p.length):= fun i=> ⟨⟨i,⟨0,p.partSize_pos i⟩⟩,rfl⟩
def site_price (s:ℝ≥0)(u: Pad (ι:=ι) p):= (∑ i:Fin p.length→β,‖F.patron p u i‖) * (Fintype.card α*F.sparksFee s)^Fintype.card (Graph p)
lemma pulse_price (u : Pad (ι:=ι) p)(x:α)(he:σ ≤ η)(h:Rest (terrain σ _) (0,y) z b): Rest (terrain σ α) (0,x) (layer (F.sparkPlug p u) (F.diagonalize p Cover u z)) (site_price F p η u*b) := by
   refine (light_cost (u:=( (0:Cover),x)) (t:= Milling.Steam.tunnel σ) fareFoot (puff_price Sigma.fst (throat p) (zip_price _ _ h)) (F.plumes p he u)).ist ?_; change tunnel σ ( ((0:Cover),y)) ( (0:Cover),x)* _ ≤ _; rw [show tunnel σ ( ((0:Cover),y)) ( (0:Cover),x)=1 from congr_arg (fun a:ℝ≥0=> (a:ℝ)) ((terrain σ Unit).flat ((0:Cover),()))]; simp only [one_mul,prod_const,Finset.card_univ]; apply le_of_eq; unfold site_price; rw [mul_right_comm _ b]; congr!
lemma blend_price (x:α)(he:σ≤η)(h:Rest (terrain σ _) (0,y) z b): Rest (terrain σ α) (0,x) (F.blend p z) ((∑ u,site_price F p η u)*b):= by rw [sum_mul]; exact print_fee (Rest.sum (fun i _=>reorder_fee _ (pulse_price F p i x he h)))
lemma pack_blend (x:α)(he:σ≤η)(h:Rest (terrain σ _) (0,y) z b)(m:Side): packing (lower m) (F.blend p z) = F.folded p (packing (lower m) z):= by
   have hc i:= pulse_price F p i x he h; unfold blend Pattern.folded; rw [pack_print (Rest.sum (u:=univ) (fun i (h':i∈(univ:Finset (Pad (ι:=ι) p)))=> reorder_fee p.equivSigma (hc i))),pack_sum (s:=univ) (lower m) (fun i _=>(reorder_fee p.equivSigma (hc i)).summ)]; simp_rw [reorder_pack,layer]; apply congr_arg; apply sum_congr rfl; intro i _; apply congr_arg
   have hh:= pack_hoist_aux fareFoot (puff_price Sigma.fst (throat p) (zip_price _ (F.patron p i) h)) (F.plumes p he i) (fun j=>row_ship _ m) ((0:Cover),x); unfold diagonalize; rw [hh,puff_pack Sigma.fst (throat p),zip_pack]
end YM.Contacts.Procession.Hinges
