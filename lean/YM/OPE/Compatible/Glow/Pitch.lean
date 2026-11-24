import YM.OPE.Compatible.Glow.Puff
/-! # Epic stencils on cover log inputs -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Work.F08 Matrix Bloch Precision Wilson
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J W E X:Type*}{i j n r d m:ℕ}{G:Gauge}
namespace Script
open Page
def indexS (p:Edge Cover): fieldX (Shade G)→ₗ[ℝ] G.Color:= LinearMap.proj (R:=ℝ) p.1 ∘ₗ heal G p.2
def lotU (v:fieldX (Shade G)):CoverConfig G:=fun p=> G.lieExp (indexS p v)
lemma matStep (s:Step)(p:Cover)(v:fieldX (Shade G))(t:ℝ): s.read (lotU (t • v)) p=G.lieExp (t • (if s.neg then -indexS (s.used p) v else indexS (s.used p) v)):=by unfold lotU Step.read; cases h:s.neg<;>simp [Work.F03.exp_neg_color]
def pieces (v:fieldX (Shade G))(p:Cover): Walk→ List G.Color
| []=>[]
| a::l=>(if a.neg then -indexS (a.used p) v else indexS (a.used p) v):: pieces v (p+a.vec) l
lemma syntaxU (v:fieldX (Shade G))(p:Cover)(w:Walk)(t:ℝ): G.mat (travel (lotU (t • v)) p w)= voyageX (pieces v p w) t:=by induction w generalizing p with
    | nil=>simp [travel,voyageX,pieces]
    | cons i w ih=> rw [travel,G.mat_mul, ih,matStep];rfl
def dirt (x:Cover) :Walk→ Finset (Edge Cover)
| []=>∅
| a::v=>insert (a.used x) (dirt (x+a.vec) v)
lemma ticket_pieces (h:fieldX (Shade G))(v:Walk)(x:Cover)(c:ℝ)(p:∀ i∈ dirt x v,‖indexS i h‖ ≤ c): ∀ i∈ pieces h x v,‖i‖≤ c:=by
    induction v generalizing x with
    | nil=> simp [pieces]
    | cons i v ih=>
       have he:=p _ (mem_insert_self ..); intro j hj; obtain h|h:= List.mem_cons.mp hj
       · rw [h]; split_ifs; rw [norm_neg]; exact he; exact he
       exact ih _ (fun i hi=> p _ (mem_insert_of_mem hi)) _ h
lemma linear_bill (G:Gauge) (d:ℕ)(s c:ℝ)(hs:0<s)(hp:0 ≤ c):∃ U:ℝ,0 ≤ U∧∀ (w:Walk)(p:Cover)(x:fieldX (Shade G)),(∀ i∈ dirt p w,‖indexS i x‖ ≤ c)→ ∀ t, ‖iteratedDeriv d (fun t:ℝ=>G.mat (travel (lotU (t • x)) p w)) t‖ ≤ U*Real.exp (s*w.length):=by
     obtain ⟨U,hU,H⟩:= stampRace G s _ hs hp _; refine ⟨U,hU,fun w p x h t=>?_⟩; have hl: (pieces x p w).length=w.length:=by
        clear h; induction w generalizing p with | nil=>rfl| cons i w ih=>simp [pieces,ih]
     simp_rw [syntaxU]; rw [← (show (pieces x p w).length= _ from hl)]; exact H _ _ (ticket_pieces _ _ _ _ h) --
lemma fluted (w:Walk)(p:Cover)(x:fieldX (Shade G)): ContDiff ℝ ⊤ (fun t:ℝ=> G.mat (travel (lotU (t • x)) p w)):=by simp_rw [syntaxU]; exact voyageS _
lemma dirt_shape (v:Walk)(x:Cover): (dirt x v).card≤ v.length:=by induction v generalizing x with
    | nil=>simp [dirt]
    | cons i v ih=> rw [dirt]; exact card_insert_le .. |>.trans (Nat.add_le_add_right (ih _) _)
lemma dirt_uses (v:Walk)(x:Cover)(p q: CoverConfig G)(h:Set.EqOn p q (dirt x v)): travel p x v=travel q x v:=by
    induction v generalizing x with
    | nil=>rfl
    | cons i v ih=>rw [travel,travel,ih _ (h.mono (fun j (hj:j∈dirt (x+i.vec) v)=>show j∈dirt x (i::v) from mem_insert_of_mem hj))]; unfold Step.read; rw [h (mem_insert_self .. : i.used x ∈ dirt x (i::v))]
lemma dirtRange (v:Walk)(x:Cover){i:Edge Cover}(h:i∈dirt x v):Laurent.size i.1 ≤ size x+v.length:=by
    have he(i:Axis): size (step i:Cover)=1:=by simp [step,size,Pi.single_apply, apply_ite (fun j:ℤ=>j.natAbs),eq_comm]
    induction v generalizing x with
    | nil=> simp [dirt] at h
    | cons a w ih=>
       have hu:size (x+a.vec) ≤ size x+1:= by apply (size_add ..).trans_eq; unfold Step.vec; split; rw [size_neg,he]; rw [he]
       simp only [dirt, mem_insert] at h; rcases h with h|h
       · rw [h]; unfold Step.used; cases hh:a.neg
         · simp only [List.length_cons,Bool.false_eq_true,↓reduceIte]; omega
         simp only [List.length_cons, if_true]; have hg : x-step a.dir=x+a.vec:=by simp [Step.vec,hh,sub_eq_add_neg]
         rw [hg];omega
       have ht:= ih (x+a.vec) h; rw [List.length_cons]; omega
end Script
end YM.OPE.Flume
