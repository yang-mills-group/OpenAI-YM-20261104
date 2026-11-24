import YM.Frontier6.Multi.Gather.Remap
import YM.Frontier6.Pair.Halo
import YM.MergeProof.Paddle

/-! Free choice of leaders using copy aperture. No irregular predicates or
   trajectories encoded in the decimation; all centers at actual ancestor sites. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Canopies
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory Matrix
open Push Marker Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open scoped Topology BigOperators Classical
variable {n:Side}{G:Gauge}{V P C:Type}[Fintype V][DecidableEq V][Fintype P][DecidableEq P][Fintype C][DecidableEq C]

-- maximal separated subset with specified anchor
lemma chief (o:P→ Site n) (root:P)(k:ℕ) (h:¬ Pairwise (fun i j=> k ≤ separation (o i) (o j))) :
    ∃ (C':Type) (_:Fintype C') (_:DecidableEq C') (π:Concentrate P C'),
        Fintype.card C'<Fintype.card P ∧ Pairwise (fun i j : C' => k ≤ separation (o (π.seat i)) (o (π.seat j))) ∧
        root=π.seat (π.hit root) ∧ ∀ i,separation (o i) (o (π.seat (π.hit i))) ≤ k:=by
    let paid (i j:P):Prop:= k ≤ separation (o i) (o j)
    let safe (L:Finset P):Prop:= root∈L∧ Set.Pairwise ↑L paid; let t:=univ.filter safe
    have hm:t.Nonempty:=⟨{root}, mem_filter.mpr ⟨mem_univ _, Finset.mem_singleton_self _,by rw [coe_singleton]; exact Set.pairwise_singleton ..⟩⟩
    obtain ⟨S,hS,hF⟩:= exists_max_image t Finset.card hm
    let hc:= (mem_filter.mp hS).2
    have hl:S.card < Fintype.card P:=Finset.card_lt_card (Finset.ssubset_univ_iff.mpr (fun he=> h (by intro i j hij; exact hc.2 (show i∈S from he.symm ▸ mem_univ _) (show j ∈ S from he.symm ▸ mem_univ _) hij))) -- check
    have hx : ∀ i:P,i∉S→ ∃ j:S,separation (o i) (o j.val) ≤ k:=by
        intro i hi; by_contra hw; push_neg at hw; have hY:safe (insert i S):=by
           refine ⟨mem_insert_of_mem hc.1,fun a hb c hd ha=>?_⟩
           rcases mem_insert.mp hb with he|he <;> rcases mem_insert.mp hd with he'|he'
           · exact False.elim (ha (he.trans he'.symm))
           · subst a; exact (hw ⟨c,he'⟩).le
           · subst c; unfold paid; rw [separation_comm]; exact (hw ⟨a,he⟩).le
           exact hc.2 he he' ha
        have hW:= hF _ (mem_filter.mpr ⟨mem_univ _,hY⟩); rw [card_insert_of_notMem hi] at hW; omega
    let f(i:P):S:= if h:i∈S then ⟨i,h⟩ else (hx i h).choose
    let Q:Concentrate P S:=⟨f,Subtype.val,fun i=> by cases i; simp [f, *]⟩
    refine ⟨S,inferInstance,inferInstance,Q,(Fintype.card_coe S).trans_lt hl,(fun i j he=> hc.2 i.property j.property (Subtype.val_injective.ne he)),?_,fun i=>?_⟩
    · change _=(f root).val; simp [f,hc.1]
    change separation (o i) (o (f i).val) ≤ _; by_cases hi:i∈S; simp [f,hi];
    rw [show f i=_ from dif_neg hi]; exact (hx i hi).choose_spec

lemma stable_size (E:Concentrate P C): Fintype.card C ≤ Fintype.card P:=Fintype.card_le_of_injective _ E.parked.injective

variable (v:V)(o:Live V P→Site n)(a b:ℕ)
def Daylight (v:V)(o:Live V P→Site n)(a:ℕ):Prop:= Pairwise fun i j : P=>a^2 ≤ separation (o (v,i)) (o (v,j))
def Between (o:Live V P→Site n)(a:ℕ):Prop:= ∀ x y:Live V P, x.fst ≠ y.fst → a^2 ≤ separation (o x) (o y)
def Shaped (v:V)(S:V→Motion)(E:V→Site n)(o:Live V P→Site n):Prop:=∀ x,x≠v→∀ j:P,o (x,j)=affine (S x).1 (E x) (o (v,j))
lemma Shaped.right {S:V→Motion}{E:V→Site n}(h:Shaped v S E o)(i:V)(j k:P) : separation (o (i,j)) (o (i,k))=separation (o (v,j)) (o (v,k)):=by
   by_cases hi:i=v; subst i;rfl; rw [h i hi,h i hi]; simp [affine]
lemma Shaped.seats {S:V→Motion}{E:V→Site n}(h:Shaped v S E o) (π:Concentrate P C):Shaped v S E (o ∘ (batt π).seat):=fun i he j=> h _ he _
lemma Between.seats (h:Between o a)(π:Concentrate P C): Between (o ∘ (batt π).seat) a:=fun i j he=>h _ _ he
lemma Daylight.drake {S:V→Motion}{E:V→Site n}(h:Daylight v o a)(hr:Shaped v S E o)(he:Between o a) : Drake (Now V P) a o:=by
   refine ⟨fun _ _ x _ y _ hi=>?_⟩
   obtain ⟨x,i⟩:=x; obtain ⟨y,j⟩:=y; rcases eq_or_ne x y with rfl|hxy
   · rw [hr.right v o x i j]; exact h (fun (e:i=j)=> hi (e ▸ rfl))
   exact he _ _ hxy
lemma Between.sectors (h:Between o a)(hf:Fintype.card P≤b)(ha:0<a): Occupancy o b:=by
   intro x; let A:=univ.filter fun i=>o i=x
   have he: Set.InjOn Prod.snd (A : Set (Live V P)):=by
       intro i hi j hj hx; refine Prod.ext (Classical.byContradiction (fun e : i.1 ≠ j.1 =>?_)) hx
       have hz:=(h i j e); rw [(mem_filter.mp hi).2,(mem_filter.mp hj).2,separation_self] at hz; exact (Nat.not_lt_of_le hz) (pow_pos ha _)
   rw [← (card_image_of_injOn he)]; exact (Finset.card_le_univ _).trans hf

set_option quotPrecheck false
lemma Between.compacted (ha:Between o a)(hb:Fintype.card P ≤ b)(h:0<a)(π:Concentrate P C): Occupancy ((o ∘ (batt π).seat) ∘ (batt π).hit) b:=by
   apply Between.sectors _ a b _ hb h; exact fun i j hz=> ha ((batt π).seat ((batt π).hit i)) ((batt π).seat ((batt π).hit j)) hz -- inspect

-- scalar weight program on PER-COPY LABELS (not V)
lemma team {M:Type*}[CommMonoid M](π:Concentrate P C) (w:P→M)(i:V)(c:C): (∏ j∈(batt π).fiber (i,c), w j.2)=∏ j∈π.fiber c,w j:=by
   have hh:(batt π).fiber (i,c)=(π.fiber c).image (fun j=>(i,j)):=by ext ⟨p,x⟩; simp [Concentrate.fiber,batt,eq_comm,and_comm]
   rw [hh,prod_image]; exact fun _ _ _ _ h=>congr_arg Prod.snd h -- wrong

end YM.MergeProof.Canopies
