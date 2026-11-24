import YM.SchemeConversionRG11.Maxwell.Temple

/-! # Closing a bilocal color-metric probe (including internal pair at one input)

Triple prepend precision: three squares per completed contraction. Includes explicit threaded
extra index at each use. -/

set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.Corona
open Function Filter Maxwell Maxwell.Free Wick Tensor Set MvPolynomial
open scoped BigOperators ComplexOrder

variable {G : Gauge} {n m k l : ℕ} {ι : Type*} [Fintype ι] {X : Points n} {a c : Fin n}

abbrev Panel (ι : Type*) (n : ℕ) (G : Gauge) := ι → Fin n → WickPol G

def gate (r : Flavor 0) (W : Panel (ι×G.ColorIndex) n G) : Panel (ι×G.ColorIndex) (n+1) G := fun j ↦ Fin.cons (bit r j.2) (W j)
def backload (p : ι × G.ColorIndex → ℂ) (W : Panel (ι×G.ColorIndex) n G) (X : Points n) (a : Fin n) (D : Echo k) :=
    ∑ i:ι×G.ColorIndex,p i * moment G X (hit D i.2 a (W i))
lemma hit_prepend (p : WickPol G) (W : Fin n → WickPol G) (a : Fin n) (D : Echo k) (j : G.ColorIndex) :
    hit D j a.succ (Fin.cons p W)=Fin.cons p (hit D j a W) := (Fin.cons_update ..).symm
lemma invoice (p : ι × G.ColorIndex → ℂ) (W : Panel (ι×G.ColorIndex) n G) (hx : X ∈ conf _) (a : Fin n) (y : E4) (r : Flavor 0) (D : Echo k) (E : Echo 0) :
    payable (Points.cons y X) p (gate r W) a.succ 0 D E=E r * backload p W X a D := by
  simp_rw [payable,pay_hits,gate,hit_prepend]
  unfold backload; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_eq_single_of_mem i.2 (Finset.mem_univ _)]
  · rw [hit]; simp only [Fin.cons_zero]; rw [rip_letter,if_pos rfl,← show E r • (1:WickPol G)=MvPolynomial.C (E r) by simp [← C_mul'], MultilinearMap.map_update_smul,Fin.update_cons_zero, ← adjoin hx, smul_eq_mul,mul_left_comm]
  intro j _ hj; rw [hit]; simp only [Fin.cons_zero]; rw [rip_letter,if_neg hj,MultilinearMap.map_coord_zero _ 0 (update_self ..),mul_zero]
lemma owes {p : ι × G.ColorIndex → ℂ} {W : Panel (ι×G.ColorIndex) n G} (hx : X ∈ conf _) {a : Fin n} {y : E4} {D : Echo k} {E : Echo 0} (H : E≠0)
    (h : ∀ r, payable (Points.cons y X) p (gate r W) a.succ 0 D E=0) : backload p W X a D=0 := by
  choose u hu using (show ∃ r, E r≠0 by by_contra! ht; exact H (LinearMap.ext ht))
  exact (mul_eq_zero.mp ((invoice p W hx a y u D E).symm.trans (h u))).resolve_left hu
lemma rebate (C₀ : G.ColorIndex) (p : ι×G.ColorIndex → ℂ) (W : Panel (ι×G.ColorIndex) n G) (hx : X∈conf _) {y : E4} (hy : Points.cons y X∈conf _) (a : Fin n)
    (h : ∀ r, assayed p (gate r W) (Points.cons y X)) (D : Echo k) : backload p W X a D=0 := by
  classical
  obtain ⟨v,hv⟩ := shelf_frame W
  let N : Fin (n+1) → ℕ := Fin.cons 0 fun _ ↦ v
  obtain ⟨E,hE⟩ := track_live
  refine owes hx hE (fun r ↦ propel C₀ p (fun r ↦ gate r W) hy (Fin.succ_ne_zero _) N rfl ?_ h ?_ D E r)
  · intro r j i; exact Fin.cases (symbol_shelf (flavor 0 j.2 r) le_rfl) (fun i ↦ hv j i) i
  intro l D E H ih r Z
  rw [invoice p W hx,owes hx H ih,mul_zero]

def stackAux (r : Flavor 0) (W : Panel ι n G) : Panel ι (n+1) G := fun i ↦ Fin.cons (team G r r) (W i)

def thrice (p : ι→ℂ) (W : Panel ι n G) :=
    ∀ (X : Points (n+3)), X∈conf _ → ∀ (r s t : Flavor 0), ∑ i:ι,p i*moment G X (stackAux t (stackAux s (stackAux r W)) i)=0

/-- For a given pair of color slots using independent spacetime polarizations, cost
three additional quadratic vertices. The statement also holds if a=c (internal pair). -/
lemma triple_assay (C₀ : G.ColorIndex) (p : ι→ℂ) (W : Panel ι n G) (h : thrice p W) (hx : X∈conf _)
    (a c : Fin n) (D : Echo k) (E : Echo l) : payable X p W a c D E=0 := by
  classical
  obtain ⟨y,hy⟩ := avoided X
  have he : Points.cons y X∈conf _ := by
    intro i j; refine Fin.cases ?_ (fun i ↦ ?_) i
    · exact Fin.cases (fun _ ↦ rfl) (fun j h ↦ (hy j h).elim) j
    exact Fin.cases (fun h ↦ (hy i h.symm).elim) (fun j h ↦ congr_arg Fin.succ (hx h)) j
  let s := fun i : ι×G.ColorIndex ↦ p i.1
  let U : Panel (ι×G.ColorIndex) n G := fun i ↦ hit D i.2 a (W i.1)
  suffices hh : ∀ r, assayed s (gate r U) (Points.cons y X) by
    rw [payable]; simp only [pay_hits]; have hg := rebate C₀ s U hx he c hh E
    unfold backload at hg; rw [Fintype.sum_prod_type] at hg; exact hg
  intro r q b hb
  let K : Panel ι (n+1+1) G := stackAux q (stackAux q W)
  let T := Points.cons b (Points.cons y X)
  have h1 : a.succ.succ≠Fin.succ (0:Fin (n+1)) := (Fin.succ_injective _).ne a.succ_ne_zero
  have hA u i : update (K i) (Fin.succ (0:Fin (n+1))) (team G u u)=stackAux q (stackAux (G:=G) u W) i := by
    unfold K stackAux; rw [← Fin.cons_update _ _ _ _, Fin.update_cons_zero]
  have H := invite C₀ p K hb h1 (fun u v t ht ↦ ?_) D r
  · rw [Fintype.sum_prod_type]; simp only [book_eval]
    unfold welcome at H; rw [← H]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
    unfold s; congr 2
    unfold U gate K stackAux; rw [hit_prepend,hit_prepend, ← Fin.cons_update,Fin.update_cons_zero]
  simp_rw [hA u,book_eval]; exact h _ ht u q v

end YM.SchemeConversionRG11.Corona
