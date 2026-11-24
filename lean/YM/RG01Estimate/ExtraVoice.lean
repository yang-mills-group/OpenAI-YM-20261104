import YM.RG01Estimate.Stanchion
/-!
 # Index transferable stencils. Canonical E* receiving label can be ANY
 renumbering, but here the part surviving in the comparison is actually a
 library of short terms pushed from the parent books. Require type X coordinates
 on every such representation used (recovering all labels outside E_suspect).
 Supports project EXACTLY, including the entire mask check. Not assuming
 inherited/suspect components do this. Crucial: physical coarse domains may have
 no gauge-extension budget for these E*, so not asserting on all Formal models.
 Untransferable contributions (e.g. long E* paths) should stay set-aside and be
 charged through E/Flat ports.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Evoc
open Function Filter Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter PhysicalNext.Repeat Deck Mint Greenbelt
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {Γ : Type} {G : Gauge} {c f C F L₀:Side} {P : Patch} {M D' p : ℕ} {K : Teller G}
section classes
variable {S:StepData c f}{T:Tube G S}{N e j m : ℕ} {R : RG.Rep G f}

abbrev Header (Γ:Type)(c f:Side):= (Site f × Γ) ⊕ Deck.Mint.Music c f
abbrev Lex (Γ:Type)(f:Side):= Site f × Γ ↪ ℕ

def coins (S: StepData c f) (L:Lex Γ f): Header Γ c f→Head S:= Sum.elim (Opacity.key S ∘ L) (Mint.disc S)
lemma mintInj (S:StepData c f)(L:Lex Γ f): Injective (coins S L):= by
   rintro (i|i) (j|j) h
   · change (Sum.inr (Sum.inr (Sum.inl (Sum.inl (Sum.inl (L i))))):Head S)= Opacity.key S (L j) at h
     injection h with h; injection h with h; injection h with h; injection h with h; injection h with h
     rw [L.injective h]
   · change Opacity.key S (L i)=Mint.disc S j at h; rcases j with j|j|j|j <;> simp [Opacity.key,Mint.disc,Mint.note,Mint.album] at h
   · change Mint.disc S i=Opacity.key S (L j) at h; rcases i with i|i|i|i<;>simp [Opacity.key,Mint.disc,Mint.note,Mint.album] at h
   rw [(Mint.disc S).injective h]
def mint (S:StepData c f)(L:Lex Γ f):Header Γ c f ↪ Head S:= ⟨coins S L,mintInj S L⟩

def aisle (S:StepData c f): Header Γ c f→ Site c:= Sum.elim ((S.ratio.parent) ∘ Prod.fst) (Deck.Mint.pace S)
abbrev songs (H: Lex Γ f) (X:Finset (Header Γ c f)) := X.map (mint S H)
abbrev hall (Γ : Type)(c f : Side) := Finset (Header Γ c f)
abbrev Sons (Γ: Type)(c f: Side) := Ursell.Clusters (hall Γ c f)
variable {Y: ConnectedActivityE6.Target G K} {ρ a W U:ℝ} {o: ConnectedActivityE6.Target.Order G W}
    (H : Cash W ρ a L₀ Y o U T R)
-- patch param defeq may need arbitrary L not P.L
abbrev Record (Γ : Type) (_S: StepData c f) (_R: RG.Rep G f) (L:Lex Γ f) (E:Set ℕ) := ∀ i,i ∈ Set.range L ↔ i∉E

def fit (R : PathData G) (i:Header Γ c f) := Sum.elim (fun _=>0) (Mint.verse R) i
lemma contents (L:Lex Γ f) {E:Set ℕ} (he:Record Γ S R L E) (x) : (∃ y:Header Γ c f,mint S L y=x ∧ fit R.path y ≤ j) ↔ Fate.arc E H j x := by
   constructor
   · rintro ⟨z,rfl,h⟩; rcases z with z|z|z|z|z
     · exact (he (L z)).1 ⟨z,rfl⟩
     · exact h
     · exact h
     · exact h
     trivial -- likely patterns z last cost Miniature
   intro hp
   rcases x with x|x|x|x
   · exact False.elim hp
   · exact False.elim hp
   swap; · exact False.elim hp
   rcases x with x|x|x
   · rcases x with x|x|x|x|x
     · obtain ⟨i,hi⟩:= (he x).2 hp; subst x; exact ⟨.inl i,rfl,Nat.zero_le _⟩
     · exact ⟨.inr (.inl x),rfl,hp⟩
     · exact ⟨.inr (.inr (.inl x)),rfl,hp⟩
     · exact ⟨.inr (.inr (.inr (.inl x))),rfl,hp⟩
     exact False.elim hp
   · exact ⟨.inr (.inr (.inr (.inr x))),rfl,Nat.zero_le _⟩
   exact False.elim hp

-- transfer width in terms of parents of paid supports; applies to nonempty E* even on told masks
structure StageMask (R: RG.Rep G f) (S: StepData c f) (L:Lex Γ f) (d:ℕ) : Prop where
   center (x : Site f × Γ) : x.1∈(R.activities.reg (L x)).support
   roots (x : Site f × Γ) : ∀ z∈ (R.activities.reg (L x)).support,separation (S.ratio.parent x.1) (S.ratio.parent z) ≤ d
-- width z; d := #parent units at actual threshold
lemma stores_high (L:Lex Γ f){d B:ℕ}(A:StageMask R S L d) (hp:0 < B) (i: Site f× Γ)(m:ℕ):
    Raw.regularFoot S.ratio m B R (L i) ⊆ neighbors (Mint.width m B d) (S.ratio.parent i.1):= by
   intro x hx; obtain ⟨w,hw,hz⟩:= halo_spec.mp (inspected_price S.ratio m B (R.activities.reg (L i)).support hp hx)
   obtain ⟨y,hy,rfl⟩:= Finset.mem_image.mp hw
   apply (neighbors_mem ..).2; apply (separation_triangle _ (S.ratio.parent y) x).trans; unfold Mint.width
   have he:= A.roots i y hy; nlinarith only [he,hz]
lemma stores_anchor (L:Lex Γ f){d B:ℕ}(A:StageMask R S L d) (i:Site f× Γ)(m:ℕ) : S.ratio.parent i.1 ∈ Raw.regularFoot S.ratio m B R (L i):=
   halo_subset _ _ (mem_image_of_mem _ (show i.1∈ RG.inspected (R.activities.reg (L i)).support from (mem_union_left _ (A.center _))))
lemma location (L:Lex Γ f){d B m:ℕ}(A:StageMask R S L d) (T: Tube G S) (hp:0<B)(i:Header Γ c f)(hz:fit R.path i≤ B) :
    Evoc.aisle S i∈areas R T m B (mint S L i) ∧ areas R T m B (mint S L i) ⊆ neighbors (Mint.width m B (B+d)) (Evoc.aisle S i):= by
   have ht (X:Support c) (x:Site c) {u:ℕ}(h:u≤ B+d)(hp:x∈X ∧ X⊆ neighbors (Mint.width m B u) x):
          x∈X∧ X⊆neighbors (Mint.width m B (B+d)) x:= ⟨hp.1,fun i hi=> (neighbors_mem ..).mpr (((neighbors_mem ..).mp (hp.2 hi)).trans (by unfold Mint.width; omega))⟩
   rcases i with i|i
   · apply ht _ _ (Nat.le_add_left d B) -- args
     exact ⟨stores_anchor L A i m,stores_high L A hp i m⟩
   exact ht _ _ (Nat.le_add_right _ _) (Mint.centered m B B hp i S T R hz)

section batch
variable (R : RG.Rep G f)(L:Lex Γ f) (X: hall Γ c f)
lemma unheld (S:StepData c f) : (songs (S:=S) L X).toLeft=∅ ∧ Matter.own (songs (S:=S) L X)=∅ := by
   let f i:= mint S L i
   constructor<;> ext i
   · simp only [mem_toLeft,notMem_empty,iff_false]; intro h; obtain ⟨j,hj,hx⟩:= mem_map.mp h; rcases j with j|j<;> simp [mint,coins,Opacity.key,Mint.disc,Mint.album] at hx
   simp only [own,mem_toLeft,mem_toRight,notMem_empty,iff_false]; intro h; obtain ⟨j,hj,hx⟩:=mem_map.mp h; rcases j with j|j<;> simp [mint,coins,Opacity.key,Mint.disc,Mint.album] at hx
lemma white (S:StepData c f) : roster (songs (S:=S) L X)=⟨∅,∅,∅⟩:= by unfold roster; rw [(unheld L X S).1]; simp [Packets.store]; exact ⟨by ext; simp,by ext; simp,by ext; simp⟩
lemma cannery (T:Tube G S) (i j:ℕ): troupe T R i j (songs (S:=S) L X):= by
   unfold troupe; rw [white,(unheld L X S).1,(unheld L X S).2]; constructor
   · constructor <;> simp [Packets.seeds]
   constructor
   · intro _ h; exact False.elim (notMem_empty _ h)
   intro _ h; exact False.elim (notMem_empty _ h)
end batch
end classes
end YM.RG01Estimate.Evoc
