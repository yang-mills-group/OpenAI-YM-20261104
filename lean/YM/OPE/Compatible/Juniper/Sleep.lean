import YM.OPE.Compatible.Spades.Tone
/-!
# Mark reduction. W budget compact.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Spells
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{E X F:Type}{n:Side}(o:Site n){b i k r m:ℕ}{K:KernelChoices}
open Finset
section
abbrev RootB (G:Gauge):= Cover × Shade G
def pealB (t:Fpaper G b):RootB G:=(t.1.val.1,t.1.val.2,t.2)
lemma pealBi : Injective (pealB (G:=G) (b:=b)):=by
      rintro ⟨⟨⟨p,i⟩,hh⟩,x⟩ ⟨⟨⟨q,j⟩,hz⟩,y⟩ h; simp only [pealB,Prod.mk.injEq] at h; obtain ⟨rfl,rfl,rfl⟩:=h; rfl
noncomputable abbrev Exposure (b:ℕ)(x:fieldX (Shade G)): Scoop G b:= strideG G b (InLine b x)
abbrev CageB (b k:ℕ)(i:Fin k→ Fpaper G b):Page (Shade G) k:= pealB ∘ i
lemma Cage_inj : Injective (CageB b k (G:=G)):=fun _ _ h=> funext fun t=> pealBi (congrFun h t)
def encircled (G:Gauge)(b k:ℕ): Finset (Page (Shade G) k):= univ.image (CageB b k (G:=G))
noncomputable def Honey (v:Pole (Scoop G b) k) : Script (Shade G) k:=fun i=> if h:∃ j,CageB b k j=i then v (fun z=> Pi.single (h.choose z) 1) else 0
lemma HoneyIn (v:Pole (Scoop G b) k)(j:Fin k→ Fpaper G b): Honey v (CageB b k j)=v (fun i=> Pi.single (j i) 1):=by
       unfold Honey; have h:∃ j', CageB b k j'= CageB b k j:=⟨j,rfl⟩; rw [dif_pos h, show h.choose= j from Cage_inj h.choose_spec]
lemma HoneyOut (v:Pole (Scoop G b) k)(j:Page (Shade G) k)(h:j∉encircled G b k): Honey v j=0:=by
       unfold Honey; apply dif_neg; rintro ⟨a,ha⟩; exact h (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,ha⟩)
lemma dropK (v:Pole (Scoop G b) k)(x: Fin k→ fieldX (Shade G)):wholeX (Honey v) x=v (Exposure b ∘ x):=by
       unfold wholeX; rw [tsum_eq_sum (s:=encircled G b k) (fun i hi=>by rw [HoneyOut v i hi,zero_mul]),encircled,sum_image (Cage_inj.injOn)]; have he:Exposure b ∘ x=fun i=>∑ j:Fpaper G b,x i (pealB j) • (Pi.single j 1:Scoop G b):=by funext i j; rw [Finset.sum_apply]; simp [Pi.single_apply]; rfl -- peal
       rw [he,v.map_sum_finset,Fintype.piFinset_univ]; refine sum_congr rfl fun i _=>?_ ; rw [HoneyIn,v.map_smul_univ]; exact mul_comm ..
lemma HoneyT {v:Pole (Scoop G b) k}(h:Sym v): sorted (Honey v):=by
       intro a; funext i; change Honey v (i ∘ a)=Honey v i; by_cases ht:i∈ encircled G b k; · obtain ⟨j,hj,rfl⟩:= Finset.mem_image.mp ht; rw [HoneyIn,show CageB b k j ∘ a=CageB b k (j ∘ a) from rfl,HoneyIn]; exact h (fun i=>Pi.single (j i) 1) a
       rw[HoneyOut _ _ ht, HoneyOut]; rintro hx; obtain ⟨j,hj,hh⟩:= Finset.mem_image.mp hx; let z:= j ∘ a.symm; apply ht; refine mem_image.mpr ⟨z,mem_univ _,?_⟩; funext k; change pealB (j (a.symm k))=_; have hv:=congrFun hh (a.symm k); change pealB (j _)=_ at hv; exact hv.trans (congr_arg i (a.apply_symm_apply _)) -- check rw unused
abbrev gumBill (G:Gauge)(b k m:ℕ):ℝ:= (Fintype.card (Fpaper G b):ℝ)^k * ((((1+k*(4*b)):ℕ):ℝ)^m)
lemma crownG (v:Pole (Scoop G b) k)(m:ℕ): soot m (Honey v) (gumBill G b k m *‖v‖):=by
      let f(i):=figure m i*‖Honey v i‖; have hp(i:Page (Shade G) k)(hh:i∉encircled G b k): f i=0:=by unfold f;rw [HoneyOut v i hh,norm_zero,mul_zero]
      refine ⟨fun i=>mul_nonneg (zero_le_one.trans (payer ..)) (norm_nonneg _),summable_of_ne_finset_zero hp,?_⟩; rw [tsum_eq_sum hp,encircled,sum_image Cage_inj.injOn] -- encircled def
      let C:=(↑(1+k*(4*b):ℕ):ℝ)^m; apply (Finset.sum_le_sum (g:=fun i=>C*‖v‖) (fun i _=>?_)).trans; swap
      · let x:=CageB b k i; have ht: stamp x ≤1+k*(4*b):=by rw[perimeter x]; exact Nat.add_le_add_left ((Finset.sum_le_sum (f:=fun j:Fin k=> Laurent.size (x j).1) (fun j _=> bounded (i j|>.1.property.1))).trans_eq (by simp)) _
        have hx : figure m x≤ C:=pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast ht) _
        unfold f; rw [HoneyIn]; refine mul_le_mul hx ((v.le_opNorm _).trans_eq ?_) (norm_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _); simp [Pi.norm_single]
      exact le_of_eq (by rw [sum_const,card_univ,Fintype.card_fun,nsmul_eq_mul,Fintype.card_fin,Nat.cast_pow]; exact mul_assoc ..|>.symm)
end
end YM.OPE.Spells
