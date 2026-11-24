import YM.MSbar.Recur.Stage
import YM.MSbar.Series.Pounds
/-! Film in s sectors, truncated by each ℏ degree and external order; price-compatible operations. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Play
open Dim Symbol Domain Diagram Scale Scale.Inertia Function Set Filter Category Counter Super Crest Deck
open scoped Classical Topology BigOperators
variable {C:Type}{W:Edition C}{c d e:Bit}{U:Set ℂ}{i k m n:ℕ}
-- honest meromorphic PS
abbrev Film (C:Type):= Form (Functionals C)
abbrev scope (i:ℕ):= Finset.range (i+1)
variable {F G:Film C}{z:ℂ}
-- shutter ζ only if merom available
def shutter(W:Edition C)(d:Bit)(F: Film C)(z:ℂ): Form (Deck W d) := fun i=>plug W d (F i z)
abbrev FitsIn (U:Set ℂ)(W:Edition C)(d:Bit)(F:Film C) := ∃ k, ∀ i:ℕ, Price k U W d (F i)
structure Ready (U:Set ℂ)(W:Edition C)(d:Bit)(m:ℕ)(F:Film C):Prop where
   cutoff : Cap m F
   room : FitsIn U W d F
   marks : Coherent U W d (scope m) F
lemma Need (hc:Cap m F){W:Edition C}{z:ℂ}: Cap m (shutter W d F z):= fun n hn=> by simp [shutter,hc _ hn]
lemma same (h:Cap m F)(hc:m≤n): scan i (scope m) F = scan i (scope n) F:=by
    unfold scan scope; refine Finset.sum_subset (Finset.range_mono (by omega)) ?_; intro j hj hh; funext z; have ht:m<j:= by simp at hh; omega
    simp [times,h j ht]
namespace Ready
variable (hf : Ready U W d m F) (hg:Ready U W d m G)
include hf
lemma lives (hz:z∈rim U)(n:ℕ): Live W d (F n z):= by obtain ⟨k,h⟩:=hf.room; exact (h n).alive hz
lemma shrinks {V:Set ℂ}(h:V⊆U): Ready V W d m F:= ⟨hf.cutoff,by obtain ⟨k,hk⟩:=hf.room; exact ⟨k,fun n =>(hk n).slim h⟩, fun i=> Price.slim (hf.marks i) h⟩
lemma scan_apply (hz:z∈rim U) (i:ℕ): scan i (scope m) F z=(Category.read (fun v=>Scale.slope v z) i m (shutter W d F z)).val:= by
    unfold scan; simp_rw [Category.novel, Submodule.coe_sum, Submodule.coe_smul_of_tower, shutter, plug_eq (lives hf hz _), Finset.sum_apply]; rfl
omit hf in
lemma zeroT : Ready U W d m 0 := ⟨fun _ _=>rfl, ⟨0,fun _=> Price.zero⟩, fun i=>by rw [show scan i _ 0=0 from ?_];exact Price.zero; unfold scan; exact Finset.sum_eq_zero fun i hi=>funext fun z=>by simp [times]⟩ -- omit h?
variable [Profit U]
lemma scale (b:ℂ): Ready U W d m (b • F):= by
    refine ⟨Cap.scale hf.cutoff _,?_,?_⟩; obtain ⟨k,h⟩:=hf.room; exact ⟨k,fun n=> (h n).scale b⟩
    intro i; refine Price.recognize (Price.scale (hf.marks i) b) ?_; intro x hx; simp only [scan,Finset.sum_apply,Pi.smul_apply,Finset.smul_sum, times]; exact Finset.sum_congr rfl fun n _=> smul_comm ..
include hg
lemma add : Ready U W d m (F+G):= by
    refine ⟨Cap.add hf.cutoff hg.cutoff,?_,?_⟩; obtain ⟨k,h⟩:= hf.room; obtain ⟨j,hV⟩:=hg.room; exact ⟨max k j,fun i=> ((h i).grow (le_max_left ..)).add ((hV i).grow (le_max_right ..))⟩
    intro i; refine Price.recognize (Price.add (hf.marks i) (hg.marks i)) ?_; intro x hx; simp only [scan, times,Finset.sum_apply,Finset.sum_add_distrib,Pi.add_apply,smul_add]
omit hf hg in
lemma sum {α:Type*} (I:Finset α){F:α→Film C}(H:∀ i∈I,Ready U W d m (F i)): Ready U W d m (∑ i∈I,F i):=by induction I using Finset.induction_on with | empty=>rw [Finset.sum_empty]; exact zeroT | insert i s he ih=> rw [Finset.sum_insert he]; exact (H i (Finset.mem_insert_self ..)).add (ih (fun j hj=>H _ (Finset.mem_insert_of_mem hj)))
end Ready
end YM.MSbar.Play
