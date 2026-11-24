import YM.QuadraticLocal.Germ.Stash
import YM.RG3.Held.Lives
/-!
# Letters in affordable tests and their slot read obligations

Each v: transpose required locus for tests (`D v`, at input and retained after
ancestor move) independent of test space. The algebra code `K v` is the
submodule of tests of this slot annihilating ALL address evaluations used by
this pairwise-alternative, so it can be `bot` if not placing constraints or
an explicit kernel ∩ on the retained location. Not mere witnesses on one tuple.
Actual geometric footprint will be tracked elsewhere.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Affinity
open Function Filter Finset MeasureTheory RemainderComparison RemainderComparison.Solos
open RemainderComparison.Collar
open scoped Topology BigOperators Classical
variable {ι θ:Type} [DecidableEq θ]
variable {α : Type*} {E:θ→Type*} [∀ i, AddCommGroup (E i)]
variable {𝕜:Type} [RCLike 𝕜] [∀ i, Module 𝕜 (E i)]
variable (K: ∀ i, Submodule 𝕜 (E i)) (A:∀ i,Set (E i))
-- uses explicit decidableEq θ for `Function.update`. Range arithmetic computed from adopted Fielding. No sharing across probes.
variable {Y:Type*} [NormedAddCommGroup Y][NormedSpace 𝕜 Y]
abbrev Wallet (A:∀ i,Set (E i)) := ∀ i,A i
def readBack (a: Wallet A):Π i, E i:= fun i=> (a i).val
omit [∀ i,AddCommGroup (E i)] in
lemma atCoord (a:Wallet A)(i:θ)(b:A i): readBack A (Function.update a i b)= Function.update (readBack A a) i b.val := by
   funext j; by_cases h:j=i; subst j; simp only [readBack,Function.update_self]; simp only [readBack,Function.update_of_ne h]
-- use same Wallet readings even in neighborhoods
structure Attn (s:Finset θ) (F:Wallet A→Y) :Prop where
    sit : ∀ t u,(∀ i∈s,t i=u i) → F t=F u
    turns i (hi:i∈s) (t:Wallet A)(x y z:A i)(a b:𝕜): z.val = a • x.val+b • y.val → F (Function.update t i z)=a • F (Function.update t i x)+b • F (Function.update t i y)
    idle i (hi:i∈s) (t:Wallet A): (t i).val ∈ K i → F t=0
namespace Attn
variable {s u : Finset θ} {A K}
variable {F G : Wallet A→Y}
lemma silent : Attn K A s fun _=> (0:Y) := by constructor <;> simp
lemma solid (c:Y) : Attn K A ∅ fun _ => c:= by constructor <;> simp
lemma outside (h:Attn K A s F) {i:θ} (hi:i∉s) (t:Wallet A)(b:A i): F (Function.update t i b)= F t:= h.sit _ _ fun j hj=> Function.update_of_ne (fun (e:j=i)=>hi (e ▸ hj)) ..
lemma plus (h:Attn K A s F) (hh:Attn K A s G) : Attn K A s (fun t=> F t+G t):=by
    refine ⟨fun t u he=> congr_arg₂ (·+·) (h.sit _ _ he) (hh.sit _ _ he), fun i hi t x y z a b ht=> ?_, fun i hi t ht=> ?_⟩
    · rw [h.turns i hi t x y z a b ht,hh.turns i hi t x y z a b ht,smul_add,smul_add]; abel
    rw [h.idle i hi t ht,hh.idle i hi t ht,add_zero]
lemma scale (c:𝕜) (h:Attn K A s F): Attn K A s (fun t=> c • F t) := by
    refine ⟨fun t u he=> congr_arg _ (h.sit _ _ he), fun i hi t x y z a b ht=> ?_, fun i hi t ht=> ?_⟩
    · rw [h.turns i hi t x y z a b ht,smul_add,smul_comm c a,smul_comm c b]
    rw [h.idle i hi t ht, smul_zero]
lemma linear {Z:Type*} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] (p:Y→ₗ[𝕜] Z)(h:Attn K A s F): Attn K A s fun t=>p (F t):= by
    refine ⟨fun t u he=> congr_arg p (h.sit _ _ he), fun i hi t x y z a b ht=>?_, fun i hi t ht=>?_⟩
    · rw [h.turns i hi t x y z a b ht,map_add,map_smul,map_smul]
    rw [h.idle i hi t ht,map_zero]
lemma total {ι:Type*}(p:Finset ι)(F:ι→Wallet A→Y)(hv:∀ i∈p,Attn K A s (F i)): Attn K A s (fun t=>∑ j∈p,F j t):= by
   induction p using Finset.induction with
   | empty=>simp_rw [sum_empty]; exact silent
   | insert i p hi ih=> simp_rw [sum_insert hi]; exact (hv i (mem_insert_self _ _)).plus (ih fun j hj=> hv j (mem_insert_of_mem hj))
lemma gather {ι:Type*}(F:ι→Wallet A→Y)(hf:∀ i,Attn K A s (F i)) (hp:∀ t, Summable (fun i=>F i t)): Attn K A s (fun t=>∑' i,F i t):= by
    refine ⟨fun t u he=> tsum_congr (fun j=> (hf j).sit _ _ he),fun i hi t x y z a b ht=>?_,fun i hi t ht=>?_⟩
    · simp_rw [fun j=> (hf j).turns i hi t x y z a b ht]; rw [Summable.tsum_add ((hp _).const_smul _) ((hp _).const_smul _),(hp _).tsum_const_smul,(hp _).tsum_const_smul]
    simp_rw [fun j=> (hf j).idle i hi t ht,tsum_zero]
lemma bind {Z:Type*}[NormedRing Z][NormedAlgebra 𝕜 Z] {F G:Wallet A→Z}(h:Attn K A s F)(hh:Attn K A u G)(hp:Disjoint s u): Attn K A (s∪u) fun t=>F t*G t:=by
   refine ⟨fun t y he=> congr_arg₂ _ (h.sit _ _ (fun i hi=> he i (mem_union_left _ hi))) (hh.sit _ _ (fun i hi=> he i (mem_union_right _ hi))), fun i hi t x y z a b ht=> ?_, fun i hi t ht=> ?_⟩
   · rcases mem_union.mp hi with hi|hi
     · simp_rw [hh.outside (Finset.disjoint_left.mp hp hi) t, h.turns i hi t x y z a b ht,add_mul,smul_mul_assoc]
     simp_rw [h.outside (Finset.disjoint_left.mp hp.symm hi) t, hh.turns i hi t x y z a b ht,mul_add,mul_smul_comm]
   rcases mem_union.mp hi with hi|hi
   · rw [h.idle i hi t ht,zero_mul]
   rw [hh.idle i hi t ht,mul_zero]
end Attn
section Real
variable [∀ i,Module ℝ (E i)] (J:∀ i,Submodule ℝ (E i))
local notation "Wallet'"=> Wallet A
variable (ζ :ι→Finset θ)
-- Universe-travel. Keep `q` nondup conditions only through actual paint.
local notation "Lt"=> mapWord ζ
def intends (J:∀ i,Submodule ℝ (E i))(A:∀ i,Set (E i))(ζ:ι→Finset θ) : Lesson ι (Wallet A) where
    Knows s f:= (mapWord ζ s).Nodup→ Attn J A (mapWord ζ s).toFinset f
    pitch a hf h:= (hf h).scale a
    constant c h:= by simp only [map_zero,Multiset.toFinset_zero]; exact Attn.solid c
    choir h g hp:= (h hp).plus (g hp)
    nil q _:= Attn.silent
    shares := by
       intro p q f g hf hg h; rw [map_add] at h ⊢; obtain ⟨h,hp,hd⟩:=Multiset.nodup_add.mp h; rw [Multiset.toFinset_add]; exact (hf h).bind (hg hp) (Finset.disjoint_left.mpr (fun i hi ht=> Multiset.disjoint_left.mp hd (Multiset.mem_toFinset.mp hi) (Multiset.mem_toFinset.mp ht)))
    meal hf hp h:= by
       refine ⟨fun t u he=> integral_congr_ae (ae_of_all _ fun i=> (hf i h).sit _ _ he),fun i hi t x y z a b ht=> ?_,fun i hi t ht=> ?_⟩
       · simp_rw [fun j=> (hf j h).turns i hi t x y z a b ht,smul_eq_mul]; rw [integral_add ((hp _).const_mul _) ((hp _).const_mul _),integral_const_mul,integral_const_mul]
       simp_rw [fun j=> (hf j h).idle i hi t ht,integral_zero]
lemma maps_one {p:Finset θ}(i:ι) (he:ζ i=p) {F:Wallet A→ℝ} (h:Attn J A p F): (intends J A ζ).Knows {i} F:=by
    have hh : mapWord ζ {i}=p.val := by simp [mapWord,he]
    intro h'; apply hh ▸ Finset.val_toFinset p ▸ h -- tactic orientation
end Real
-- ghost. property lives defined independently; existential invalid proof works BEFORE diagonal choices.
variable (Z : Set ι)
def witness (α:Type*) (Z:Set ι) : Lesson ι α where
  Knows s f:= ∀ i∈s,i∉Z→∀ a,f a=0
  constant _ i hi:= by simp at hi
  pitch _ hf i hi h a:= by dsimp only; rw [hf i hi h, mul_zero]
  nil _ _ _ _ _:= rfl
  shares hf hg i hi hx a:= by dsimp only; rcases Multiset.mem_add.mp hi with h|h; rw [hf i h hx,zero_mul]; rw [hg i h hx,mul_zero]
  choir hf hg i hi hx a:= by dsimp only; rw [hf i hi hx, hg i hi hx,add_zero]
  meal hf _ i hi hx a:= by dsimp only; simp_rw [fun p=>(hf p i hi hx a),integral_zero]
end YM.QuadraticLocal.Affinity
