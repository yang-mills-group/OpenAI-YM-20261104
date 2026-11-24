import YM.RG02.Degree.Coefficient
import YM.RG02.Degree.Conn

/-!
Power budgets after contracting each Wick graph. Kept leg supports/ambient
sheet fields explicit. `tax` can vanish by no capacity; no vertex efficacy or
bounds on the canonical supported representation implied by this contraction.
All orders fixed arbitrary. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG02.Shear
open MvPolynomial Finset Next.Rank Next.Rank.Normal Function Wick Marker Marks Multi Extra.Trajectories
open scoped Classical BigOperators
variable {X E I : Type} [NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup E][NormedSpace ℝ E]
variable {A : Type}[DecidableEq I][Fintype I]{T : Census I}

private theorem pointed_power [Fintype A] [DecidableEq A](a:A→ℂ)(Q:Census A)(u:Poly Q)(h:u.part Q.quiet=1) :
    connected (Multi.dilation Q a u)= Multi.dilation Q a (connected u) := by
   have hf : ∀ z,(Multi.dilation Q a z).part Q.quiet=z.part Q.quiet := fun _ => by rw [Multi.dilation_part]; simp [Census.quiet]
   apply pass_inj (connected_quiet ((hf u).trans h)) ((hf _).trans (connected_quiet h))
   rw [pass_connected ((hf u).trans h), ← Multi.pass_map _ _ (connected_quiet h) ((hf _).trans (connected_quiet h)), pass_connected h]

omit [Fintype I] in
private lemma dot_charge (f : I→ℂ) [Fintype A][DecidableEq A](o : A→I)(ℓ:A→Module.Dual ℝ E)(q:Symmetric (Module.Dual ℝ E)) :
    Wick.terms (R:=T) o (fun i (_:Dot)=>f i) (edges (fun _=>q) (fun _=>ℓ)) dot =
      Multi.dilation _ (Sum.elim f (fun _=>1)) (Wick.terms o (fun _ (_:Dot)=>1) (edges (fun _=>q) (fun _=>ℓ)) dot) := by
   let H := together T (Lines A)
   let e (p) := edges (A:=A) (T:=Dot) (fun _=>q) (fun _=>ℓ) p
   ext s
   rw [Multi.dilation_part];
   change ite _ (dot ((∏ i∈(Pair.fst s).val,fun _:Dot=>f i) * ∏ i∈(Pair.snd s).val,e i)) _ = _ * (ite _ (dot ((∏ _∈(Pair.fst s).val,fun _:Dot=>1) * ∏ i∈(Pair.snd s).val,e i)) _)
   split; swap; · rw [mul_zero]
   have hh : ∏ i∈s.val,(Sum.elim f (fun _=>1)) i=∏ i∈(Pair.fst s).val,f i := by nth_rw 1 [← Pair.mk_read s]; simp [Pair.mk,prod_disjSum]
   rw [hh, ← smul_eq_mul (∏ i∈(Pair.fst s).val,f i),← map_smul]; congr 1; ext1 x; simp [Finset.prod_apply]

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
lemma overlaid (q:Symmetric (Module.Dual ℝ E)) [Fintype A][DecidableEq A](o:A→I)(ℓ:A→ Module.Dual ℝ E)
    (c:I→X→ℂ) (p:(Lines A).Mode)(s:T.Mode) : (fun x=> (connected (Wick.terms (R:=T) o (fun i (_ : Dot)=> c i x) (edges (fun _=>q) (fun _=>ℓ)) dot)).part (Pair.mk s p)) =
       ((connected (Wick.terms o (fun _ (_ : Dot)=>1) (edges (fun _=>q) (fun _=>ℓ)) dot)).part (Pair.mk s p)) • ∏ i∈s.val,c i := by
   ext1 x; rw [dot_charge (f:=fun i=>c i x),pointed_power _ _ _ (terms_quiet o _ _ choose_dot.1), Multi.dilation_part];
   dsimp only [Pair.mk]
   rw [Finset.prod_disjSum]; simp [Finset.prod_apply,mul_comm]

abbrev Peer (P : I → Vertex X E) := (i : I) × Fin (P i).n

def tax (s : T.Mode)(c:I→ℕ) := (∑ i∈s.val,c i)- (2:ℕ)*(s.val.card-1)

theorem contracted (q : Symmetric (Module.Dual ℝ E))(P : I→Vertex X E)(s : T.Mode)(k : I→ℕ)(H : ∀ i∈s.val,(P i).Counts (k i)) :
    Payment (tax s k) fun x => (connected (stellar dot (fun _=>q) (fun i _=> (P i).cost x))).part s := by
   classical
   let A:= Peer P
   let ℓ := fun a:A=>(P a.1).legs a.2; let o:=fun a : A=> a.1
   let C:= fun i=> (P i).c
   have he (t : Finset I) : arms o t = t.sigma (fun i => univ (α:= Fin (P i).n)) := by ext ⟨a,b⟩; exact arm_of.trans (Iff.intro (fun h => mem_sigma.mpr ⟨h,mem_univ _⟩) (fun h => (mem_sigma.mp h).1))
   have hc(i) : glyphs ℓ (arms o {i})=glyphs (P i).legs univ := by
      rw [he,glyphs]; rw [prod_sigma]; simp [glyphs, ℓ]
   let v (x : X) := Wick.terms (R:=T) o (fun i (_ : Dot)=> C i x) (edges (fun (_:Dot)=>q) (fun _=>ℓ)) dot
   let M (p : (Lines A).Mode) (x : X) := (connected (v x)).part (Pair.mk s p)
   have h (p:(Lines A).Mode) : Payment (tax s k) (M p) := by
      by_cases h : ∃ x, M p x≠0; swap
      · push Not at h; exact (funext h).symm ▸ Payment.const (0:ℂ) _
      obtain ⟨x,h⟩ := h
      obtain ⟨hS,hP⟩ := pins q ℓ o (fun i=>C i x) s p h
      have hz : ∑ i∈s.val, (P i).n=p.val.card * 2:= by rw [he, card_sigma] at hP; simpa only [card_univ,Fintype.card_fin] using hP
      have hm1 : Payment (∑ i∈s.val,(k i-(P i).n)) (∏ i∈s.val,C i):= Payment.product _ _ _ fun i hi => (H i hi).2
      have hp : ∑ i∈s.val,(k i-(P i).n) ≤ tax s k := by
         have he' (i : I) (h : i∈s.val) : k i= k i-(P i).n+(P i).n := (Nat.sub_add_cancel (H i h).1).symm
         have hg : ∑ i∈s.val,k i = (∑ i∈s.val,(k i-(P i).n)) + p.val.card * 2 := by rw [← hz,← sum_add_distrib]; exact sum_congr rfl he'
         unfold tax; rw [hg]; omega
      unfold M v; rw [overlaid]; apply Payment.scale (hm1.raise hp)
   let Q x := monomials (R:=T) o (fun i (_ : Dot)=>C i x) (fun _=>q) (fun _=>ℓ) dot
   have hh (x : X) : (connected (stellar (R:=T) dot (fun _=>q) (fun i _=>(P i).cost x))).part s=
         ∑ p:(Lines A).Mode,M p x := by
      refine (stellar_atoms dot (fun _=>q) o (fun i (_ : Dot)=>C i x) (fun _=>ℓ) _ s.val (fun i _ t => by rw [hc]; rfl)|>.conn s subset_rfl).trans ?_
      exact monomial_graph_sum o _ _ _ choose_dot.1 s
   simp_rw [hh]; exact Payment.plane univ M fun i _=>h i

/-- Already a sum on the stellar rays. -/
theorem others {n : I→ℕ}(q : Symmetric (Module.Dual ℝ E))(P : (i:I)→ Fin (n i)→ Vertex X E)(s : T.Mode)(k : I→ℕ)(H : ∀ i∈s.val,∀ j,(P i j).Counts (k i)) :
    Payment (tax s k) fun x=> (connected (stellar dot (fun _=>q) (fun i _=> ∑ j:Fin (n i),(P i j).cost x))).part s := by
   let f (x:X) (i) (j:Fin (n i)) (_:Dot):= (P i j).cost x
   let G (x:X)(i) (_:Dot):= ∑ j:Fin (n i),(P i j).cost x
   let v (z : ∀ i:(↑s.val),Fin (n i.1)) (i:I) : Vertex X E := if h:i∈s.val then P i (z ⟨i,h⟩) else ⟨0,(fun _=>0),fun _=>0⟩
   have he (x) : (connected (stellar dot (fun _=> q) (G x))).part s = ∑ z : ∀ i:(↑s.val),Fin (n i.1), (connected (stellar (R:=T) dot (fun _=>q) (fun i _=> (v z i).cost x))).part s := by
       have hi (i) (hi:i∈ s.val) : G x i=∑ j,f x i j := by funext; simp [G,f,Finset.sum_apply]
       rw [stellar_sum choose_dot.1 _ _ _ s hi]; apply sum_congr rfl; intro p _
       apply YM.Primitives.GCC.Anchor.UpTo.conn _ _ subset_rfl
       intro t ht; change jointly dot _ _=jointly dot _ _; congr 1; apply prod_congr rfl; intro i hv
       simp only [dif_pos (ht hv),v]; rfl
   change Payment _ (fun x=>(connected (stellar dot (fun _=>q) (G x))).part s)
   simp only [he]
   exact Payment.plane univ (fun z x=> _) (fun i _=>contracted q (v i) s k (fun b hb=>by dsimp only [v]; simp_rw [dif_pos hb]; exact H b hb _))
end YM.RG02.Shear
