import YM.MSbar.Diagram.Readers

/-!
Extensible linear atlas of neutral vertices. Fiber transforms in λ, ε, analytic contours, ...
preserve the tag multiset and vector/super symmetry. No reduction of evanescent structures via
projection on degree n. Use atlas instead of an inductive syntax of fields, saves quotienting.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Scale
open Dim Domain Diagram Super Loops Function Set Filter Symbol
open scoped BigOperators Topology ContDiff Classical
variable {C:Type} {m n j:ℕ} {W:Edition C}{d:Bit}{f g: Vertex C}

/-- Grade by labels independent of momentum and hat components / coordinates. -/
def skin (z:Words C m): Multiset C:= ↑(z.map label)
@[simp] lemma skin_cons (t: Letter C m)(v): skin (t::v)=t.1.1::ₘ(skin v):=rfl
@[simp] lemma skin_add (z v:Words C m): skin (z++v)=skin z+skin v:=by simp only [skin,List.map_append,Multiset.coe_add]
lemma skin_moves (t:Words C m) (L:Move m n): skin ((line C).move L t)=skin t:=by induction t with | nil=> simp [skin] | cons c t ih=> simp only [work,skin_cons,ih]
lemma Plot.skin_eq {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{g:E→Words C m} (h:Domain.Plot E C m g)(x y:E): skin (g x)=skin (g y):=by induction h with | empty=> rfl | cons c a b ha hb h ih=> simp [ih]
structure Cell (W: Edition C)(d:Bit)(f:Vertex C):Prop where
    nature : (line C).Natural f
    quiet : ∀ i, Quiet (f i)
    color : ∀ i,Domain.Polar W (f i)
    sign : ∀ i, Homogeneous (lift (W.binary i)) d (f i)
lemma full_cell {U:Set ℂ}{F:Functionals C}(hf:Full U j W d F){z:ℂ}(hz:z∈U): Cell W d (F z):= ⟨hf.licensed.natural z hz,hf.quiet z hz,hf.colors z hz,hf.span z hz⟩
lemma live_cell (hf: Live W d f) : Cell W d f:= full_cell hf (Set.mem_univ 0)
lemma using_cell {U:Set ℂ}{F:Functionals C} (hf:∀ z∈U, Cell W d (F z))
   (h:(E:Type)→ [NormedAddCommGroup E] → [NormedSpace ℝ E] → [FiniteDimensional ℝ E]→ {m:ℕ}→ (x:E→Words C m)→ (arena C).plot x → Bet U j (fun p:ℂ × E => F p.1 m (x p.2))): Full U j W d F:= ⟨⟨fun z hz=> (hf z hz).nature,h⟩,fun z hz=>(hf z hz).quiet, fun z hz=> (hf z hz).color, fun z hz=>(hf z hz).sign⟩
-- Transforms by any gauge in the direction of the multiset of labels.
structure Chart {X:Type*} (S:Filter X) (A:(X→ℂ)→ℂ) (Q:(X→ℂ)→Prop):Prop where
    zero {a} : Q a→ (a =ᶠ[S] 0) → A a=0
    agrees {a b}: Q a→Q b→ (a =ᶠ[S] b) → A a= A b
    plus {a b c} : Q a → Q b → Q c → (c =ᶠ[S] a+b) → A c=A a+A b
    scaled {a b} (c: ℂ): Q a→Q b→ (a =ᶠ[S] c • b) → A a=c*A b
namespace Chart
variable {X:Type*}{S:Filter X}{c:ℂ}{A:(X→ℂ)→ℂ}{Q:(X→ℂ)→Prop}
lemma one (h:Chart S A Q){Y:Type}[AddCommGroup Y][Module ℝ Y]{G:X→Y→ℂ}{t:Prop}(hg: ∀ᶠ x in S, One t (G x))(hu:∀ y, Q fun x=> G x y): One t (fun y=>A fun x=>G x y):=by
   unfold Dim.One at *; split_ifs at * with ht
   · refine ⟨{ toFun:=fun y=> A fun x=>G x y, map_add':=fun u v=>?_, map_smul':=fun b u=>?_ },fun x=>rfl⟩
     · apply h.plus (hu _) (hu _) (hu _); filter_upwards [hg] with x hx; obtain ⟨F,hF⟩:=hx; simp [hF]
     apply h.scaled b (hu _) (hu _); filter_upwards [hg] with x hx; obtain ⟨F,hF⟩:=hx; rw [hF,map_smul]; change _= (b:ℂ) * G x u;rw [hF]; rfl
   refine ⟨A (fun x=> G x 0),fun x=> h.agrees (hu _) (hu _) (?_)⟩; filter_upwards [hg] with t ht'; exact (ht'.choose_spec x).trans (ht'.choose_spec 0).symm
end Chart
namespace Cell
lemma reform {X:Type*}{S:Filter X}{A:Multiset C → (X→ℂ)→ ℂ}{Q: Multiset C→(X→ℂ)→Prop}
   (hA:∀ t,Chart S (A t) (Q t)) {F:X→Vertex C}(h:∀ᶠ x in S, Cell W d (F x))(hp:∀ i (x:Words C i), Q (skin x) (fun v=> F v i x)): Cell W d (fun i x=> A (skin x) fun v=> F v i x) := by
    refine ⟨fun ⦃i j⦄ L x=>?_,fun i x hx=>?_,fun i c p u v=>?_,fun i=>⟨fun u a b v=>?_,fun u hu =>?_⟩⟩
    · have := skin_moves x L; have hQ:= hp _ ((line C).move L x); rw [this] at hQ ⊢; exact (hA (skin x)).agrees hQ (hp ..) (h.mono fun x hx=> hx.nature L _)
    · exact (hA _).zero (hp ..) (h.mono fun x hr=> hr.quiet _ _ hx)
    · simp_rw [skin_add, skin_cons]; exact (hA _).one (G:=fun y t=>F y i (u++((c,t),p)::v)) (h.mono fun x hx=> hx.color i c p u v) (fun y=> by simpa using! hp i (u++((c,y),p)::v))
    · have e: skin (u++a::b::v)=skin (u++b::a::v):= by simp [Multiset.cons_swap a.1.1 b.1.1]
      have hQ:=hp _ (u++a::b::v); rw [e] at hQ ⊢; exact (hA _).scaled _ hQ (hp ..) (h.mono fun x hx=> (hx.sign i).commute ..)
    exact (hA _).zero (hp ..) (h.mono fun x hx=> (hx.sign i).shape _ hu)
end Cell
end YM.MSbar.Scale
