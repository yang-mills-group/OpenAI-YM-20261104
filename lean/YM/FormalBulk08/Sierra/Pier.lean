import YM.FormalBulk08.Sierra.Gleam
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Sierra
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Work.F03 Work.F05 Work.F08 PowerSeries
open Quire Sable Aster Dawn Wine Roof Orb Tundra Dove Spruce Elm
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{X I:Type} {K:KernelChoices}{ρ:ChartRatio G}{E R m r u e l:ℕ} {a:hue G}{W:Lab G K X}
structure Weather (W:Lab G K X)(u R E:ℕ) :Prop where
   sails:Soft (chron W.scrolls) (fun i=>(W.windowD i)⁻¹)
   salary:∃ C:Leaf W.scrolls→ℝ,Soft (chron W.scrolls) C ∧∀ x,Hearth K (W.pat x) (W.wood x.a x.b) u R E (W.upper x) (W.lower x) G (C x)
lemma stillW (h:Weather W u R E)(P:Pin W.scrolls)(M:X→ℕ)(he:e≤ E)(hr:1≤r)(hx:r≤ R+E)(hp:m≤R): Paper K (graded W.liftF (W.trail (C:=P) M)) W.liftU u m e r (Dove.tide P) G (Dove.Turn.rad (1/2)):= by
    obtain ⟨C,c,V⟩:=h.salary; refine ⟨_, c.reach (fun i:Turn P=> i.toLeaf),fun i=>(V _).nonneg,fun i=>?_⟩; have ht:=(V _).merrit _ hr hx m hp _ he (graded W.liftF (W.trail M) i) (W.liftU i) rfl rfl; change Perusal _ _ _ _ _ _ _ G (Mulct ((W.V _).S.block _)) _ at ht; rw [mulct_step] at ht; exact ht
structure Trail (W:Lab G K X)(C:Pin W.scrolls)(a:hue G) where
    root:Deck C→ edgeL G
    rate:Deck C→ℝ≥0
    cap:∀ i,rate i≤1
    link:∀ i:Turn C,root i.bed=chief (W.liftF i) (root i.ups) (Exterior.coord 0,a)
    anchor:∀ i:Turn C,rate i.bed≤(W.liftF i).L.val*rate i.ups
variable (T:X→Pot G) (a) (ρ) (C Q:Pin W.scrolls) (l)
def chainI (x:X) : ℕ →ℕ→ Pot G
   | 0,_=> T x
   | n+1,i=> enterStep (destination (W.V x) (Q.N x) i) (W.wood x i) (Lab.saga ρ a W x (Q.N x) (i+1)) a ρ (W.toEmpire.bill x i) l (chainI x n (i+1))
abbrev satCamp (i:Deck C): Pot G:=chainI ρ l a T Q i.a (C.N i.a-i.b) i.b
lemma score (i:Turn C): satCamp ρ l a T C Q i.bed = enterStep (graded W.liftF (W.trail Q.N) i) (W.liftU i) (Lab.instory ρ a W Q.N i.ups) a ρ (W.liftH i) l (satCamp ρ l a T C Q i.ups):= by
    unfold satCamp; rw [show C.N i.bed.a-i.bed.b=C.N i.ups.a-i.ups.b+1 from ?_, chainI]; rfl
    change C.N i.a-i.b=C.N i.a-(i.b+1)+1;have :=i.head; omega
lemma at_top (i:X): satCamp ρ l a T C Q (peak C i)=T i:=by unfold satCamp; rw [show C.N (peak C i).a - _ =0 from Nat.sub_self _, chainI]
lemma sandpiper (h:∀ i,C.N i≤ Q.N i)(hp:W.Use ρ E)(v:LocalRatio ρ)(ht: G.Simple)(hy:∀ x,Ritual (T x) l) (i:Deck C): Ritual (satCamp ρ l a T C Q i) l:= by
    let f:= satCamp ρ l a T C Q; have H x k (hv:W.neck x ≤ k)(hz:k≤C.N x):let i:Deck C:= ⟨⟨x,k,hv⟩,hz⟩; Ritual (f i) l:= by
       induction hz using Nat.decreasingInduction with
       | self=> intro i; rw [show f i=T x from at_top ..]; exact hy _
       | of_succ n he IH=>
          intro i; let j:Turn C:= ⟨⟨x,n,hv⟩,he⟩; obtain ht':= budge C Q Q h (fun _=>le_rfl) hp v a ht
          rw [show f i=_ from score ρ l a T C Q j]; exact ritScore (graded W.liftF (W.trail Q.N) j) (W.liftU j) (Lab.instory ρ a W Q.N j.ups) a ρ (T:=satCamp ρ l a T C Q j.ups) (W.liftH j) (ht'.aV j) v (ht'.church j) (IH (hv.trans (Nat.le_succ _)))
    exact H i.a i.b i.zone i.cap
end YM.FormalBulk08.Sierra
