import YM.WilsonCoeffUV.Marked.Bounds.Truth
/-!
# Orbit from independent top, every field's own height. Not asserting Gram
coherence by choosing anything in physical hierarchy.
 -/
set_option autoImplicit false
set_option maxHeartbeats 550000
noncomputable section
namespace YM.WilsonCoeffUV.Wheel.Mark
open Function PowerSeries Blue Mer Lattice RG Embroider Embroider.Canvas Soil Bank Laurent Cosmos Filter Gauge Power Matrix Precision Wilson Tree Exterior AnalyticNext.QuarticMatch.Sheets Bloch FreeResolvent Work.F08 Metric Shard Realm PathCost
open Fountain Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb
open scoped Matrix.Norms.Frobenius
open scoped Topology BigOperators
variable {c f:Side}{ι α U V t:Type}{J K I T:Finset ι}{D k K':ι→ℕ}{i j i' j' a e r h N n m b l:ℕ}{G:Gauge}{σ τ u g B C z ρ:ℝ}
variable [DecidableEq ι]
omit [DecidableEq ι] in
lemma abreast (X: Ten V (Cloth α) i)[NormedAddCommGroup V](p:ι→ Cover)(j:ι)(h:Cork Bank.terrain (p j) σ B X)(v:0≤σ): Wig Bank.terrain p σ B {j} X:=by
   refine ⟨h.1,fun x=>(h.2 x).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (Nat.cast_le.mpr (show Syn Bank.terrain p {j} x ≤ tread Bank.terrain (p j) x from ?_)) (neg_nonpos.mpr v))) h.1)⟩
   let X:=foyer p {j} x; let T:=stud (p j) x; have hp i:∃ j,X i= T j:=by cases i with
                                                                             | inl i=> exact ⟨0,congr_arg p (Finset.mem_singleton.mp i.property)⟩
                                                                             | inr i=>exact ⟨i.succ,rfl⟩
   apply league_le Bank.terrain X; intro i j; obtain ⟨a,ha⟩:= hp i; obtain ⟨b,hb⟩:= hp j; rw [ha,hb]; exact leg_le ..
lemma Budges (D:ι→ℕ)(s:ι)(X:TowerS G (D s))(v:0≤σ)(p:ι→ Cover)(h:Cork Bank.terrain 0 σ B (X.2 i j)): Wig Bank.terrain p σ B {s} ((cn D s X (p s)).2 i j):=
    abreast _ p s (Cork.turn _ ((h.touch (petal D s)).cost (mul_le_of_le_one_left h.1 (petal_bound ..)))) v

lemma inkAr {D F:ℕ}{X:Labels.Frame G F}(Y:Verse X) (P:Island X D) (_u:0≤σ)(v:∀ i≤ j,∀ x:Alma X,‖coeff i (Y x)‖≤B)(t:∀ i≤j,∀ x:Alma X,Cork Bank.terrain 0 σ C (P.2 x i r))(z:0≤C):
    Cork Bank.terrain 0 σ ((Fintype.card (Alma X)*(j+1):ℕ)*(B*C)) ((Shrine P Y).2 j r):=by
   simp_rw [Shrine, Prod.snd_sum,Finset.sum_apply,Stem,affix,Finset.sum_apply]; have h (x:Alma X)(i:ℕ×ℕ)(h:i∈Finset.antidiagonal j): Cork Bank.terrain 0 σ (B*C) (coeff i.1 (Y x) • P.2 x i.2 r):=by
        have he:= Finset.mem_antidiagonal.mp h; exact ((t i.2 (by omega) x).μ _).cost (mul_le_mul_of_nonneg_right (v i.1 (by omega) x) z)
   rw [show ((Fintype.card (Alma X)*(j+1) : ℕ):ℝ)*(B*C)=∑ _ : Alma X,∑ _∈ Finset.antidiagonal j, B*C by simp; ring]; exact Cork.sum fun i _=>Cork.sum (h i)

lemma polarExp {h' D':ℕ}{F:Labels.Frame G h'}(H:Hol G)(T:SectionData F)(p:h'<D')(e:ℕ)(E W U:Credit): ∃ V:Credit,∀ L:ChorusLine H T p e E W U,∀ (m i N:ℕ)(X: Verse F)(x z:ℝ) (u:L.arch.V.anchor≤m)(v:m≤ i)(_g:i≤ N), Compar L.arch.V.draws.S L.arch.V.y m i ≤ z → 0≤ x → (∀ j≤e,∀ t:Alma F, ‖coeff j (X t)‖≤x)→
   ∀ j≤e,∀ r,let R:=L.arch.V
   Cork Bank.terrain 0 (L.arch.angle i (u.trans v)).lamp.exitS (V.buy z*x) ((polarP R.draws R.paid T p N m i X).2 j r):=by
    obtain ⟨V,hV⟩:= agesQuote H T p e E W U; obtain ⟨C,hC⟩:=allPlays H T p e E W
    let L:ℕ:= Fintype.card (Alma F)*(e+1)
    refine ⟨(pur L).prodC (V.prodC C),?_⟩; intro A m i N X x z u v g w y t j a r R
    let Q: CourseS H T p e E W U:= ⟨A,⟨R,m,i-m,N,N,i,u,(by omega),g,g⟩,rfl⟩; have hp: Q.Age≤ z:=by unfold CourseS.Age WindowS.Age Q; dsimp; rwa [Nat.add_sub_of_le v];
    have he:1≤z:= Q.I.warm.trans hp; have hv: R.y i≤z:=by apply le_trans _ hp; have hx:= Q.I.covers (le_refl Q.I.span); change R.y (m+(i-m))≤ Q.Age at hx; rwa [Nat.add_sub_of_le v] at hx
    let δ:=Q.cab; have hδ:0≤δ:=(trail_pos ..).le; let s:= A.arch.angle i (u.trans v); let F':=steep R.draws R.paid T p N m (i-m) X; let Y':= A.arch.lore N i
    have hX t0 (b:t0≤e) y' :‖coeff t0 (F' y')‖ ≤ V.buy z*x:=
       (((hV Q X X x δ y le_rfl (fun x g f=>twain.one _ _ hδ (t x g f)) t0 b y')).main).trans (mul_le_mul_of_nonneg_right (V.elder Q.I.warm hp) y)
    have hT j (q:j≤ e) y': Cork Bank.terrain 0 s.lamp.exitS (C.buy z) (Y'.2 y' j r):= ((cheers A.arch (hC j (valence F y') r q) (u.trans v) g (le_refl N) _ rfl).wax).cost (C.elder (R.depth _ (u.trans v)) hv)
    have hf:= zero_le_one.trans (C.purchase he); apply (inkAr F' Y' s.lamp.positive.le (fun i h v=> hX i (h.trans a) v) (fun i h v=>hT i (h.trans a) v) hf).cost; rw [Credit.products,Credit.products]
    let g:= V.buy z; have hx':0≤g:= zero_le_one.trans (V.purchase he); refine le_trans (mul_le_mul_of_nonneg_right ((Nat.cast_le.mpr (Nat.mul_le_mul_left _ (show j+1≤ e+1 by omega))).trans (pure_goal L z)) (mul_nonneg (mul_nonneg hx' y) hf)) ?_; exact le_of_eq (by ring)
end YM.WilsonCoeffUV.Wheel.Mark
