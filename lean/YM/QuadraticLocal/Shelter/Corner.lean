import YM.QuadraticLocal.Shelter.Picnic
/-! # price conversion for qlocal masks. Normalize by EVERY paid slot radius.

Every spoke stable, locality meet includes anchor. Doesn't allege decay
beyond the given cover/ball cost; the height ledger needs to purchase this!
No power loss from number of stencil roots or entropy bound in the merger
geometry. Additional mask shape fee paid here and reduced temporary radii allowed
later, even when the height changes. Use B = output display B.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Shelter
open Function Filter Finset Lattice Wilson RG Ac Marker Push Push.Local Push.Corrected Push.AbsoluteSums MeasureTheory
open Animals Next.Foundations Extra.Trajectories
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge}{n:Side}{V T ι μ C : Type}[DecidableEq V]{o:V→Site n}{R:Census V}{P:BudgetPoint} {B H:ℕ}
variable {L:Lamps T ι G P o R}(w:V→ℝ)(hw:∀ i,0<w i)
variable {D:Terrain C R}
variable {a b r t τ ε δ:ℝ} {α:C→Type} [∀ i, Fintype (α i)]
namespace Deck
variable (d:Deck L D H α) (i:C) (x:T) (U:Config G n)
variable (f:ι→ℝ)(hf:∀ i,0≤f i)
local notation "z_"=>d.enrol
noncomputable def amount : ℝ:= ∑ v:α i,f (d.enrol ⟨i,v⟩)
local notation "Y"=> fun i=> d.amount i f
local notation "A"=> Poly.toll w
omit [∀ i,Fintype (α i)] in
lemma member (j:Σ i:C,α i): D.center o j.fst∈ L.ground (d.enrol j):= L.roots _ _ (d.calls j|>.symm ▸ D.at_anchor j.fst)
include hf
lemma bien : 0 ≤ d.amount i f:= Finset.sum_nonneg (fun _ _=>hf _)
omit hf in
lemma ticket (hu:∀ i x, P.supBounds (L.address i).site (L.ground i) (L.nominal x i) (f i)): ‖d.round i x U‖ ≤ d.amount i f:= (norm_sum_le ..).trans (Finset.sum_le_sum fun _ _=> L.light_size _ _ _ (hu _ _))
noncomputable def crewCost (H:ℕ)(a v:ℝ):= Real.exp (a*v)*(Animals.ballCost H:ℝ)
variable (hH: Hit L.ground B (fun i=>Poly.toll w (L.mode i)*f i) t b) (ht:0≤t) (ha:0≤a) (hτ:∀ i,(Lattice.coverNumber B (D.barrier o H i):ℝ)≤τ)
include hw hH ht
-- all at root
lemma bankers (x:Site n) : SumBudget (fun i=>if D.center o i=x then Poly.toll w (D.mode i)*d.amount i f else 0) b:=by
    let g (z:Site n)(i:Σ j:C,α j):= if z∈ L.ground (d.enrol i) then Poly.toll w (L.mode (d.enrol i))*f (d.enrol i)*Real.exp (t*(Lattice.coverNumber B (L.ground (d.enrol i)):ℝ)) else 0; have he (z:Site n) : SumBudget (g z) b:= budget_pull d.enrol d.enrol.injective (hH z); have hx (i:C):0≤ Poly.toll w (D.mode i)*d.amount i f:= mul_nonneg (Poly.worth hw _).le (d.bien _ f hf);
    refine budget_of_sum (fun i=>by split; exact hx i; rfl) fun s=> le_trans ?_ (budget_sum (he x) (s.sigma fun _=>Finset.univ))
    rw [Finset.sum_sigma]; apply Finset.sum_le_sum; intro i _
    split_ifs with hv; swap; · exact Finset.sum_nonneg (fun _ _=>(he _).1 _)
    rw [Deck.amount,Finset.mul_sum]; apply Finset.sum_le_sum; intro j _
    unfold g; let k:Σ i:C, α i:=⟨i,j⟩; rw [if_pos (hv ▸ (show D.center o i∈ L.ground (d.enrol k) from d.member _)), d.calls]; exact le_mul_of_one_le_right (mul_nonneg (Poly.worth hw _).le (hf _)) (Real.one_le_exp (mul_nonneg ht (Nat.cast_nonneg _)))
include ha hτ
lemma wages : Hit (D.barrier o H) B (fun i=> Poly.toll w (D.mode i)*d.amount i f) a (crewCost H a τ*b):=by
    intro x; let s:= neighbors H x; let Q (x:Site n) (i:C):= if D.center o i=x then Poly.toll w (D.mode i)*d.amount i f else 0; have hF(z:Site n): SumBudget (Q z) b:= d.bankers w hw f hf hH ht z; let Ω:= Real.exp (a*τ); have hr:0<Ω:=Real.exp_pos _; let r':= ∑ _∈s,b; refine budget_loosen (budget_mono (budget_scale hr.le (budget_over s Q (fun _=>b) (fun x hx=> hF _))) ?_ (fun i=>?_)) ?_
    · intro i; split; exact mul_nonneg (mul_nonneg (Poly.worth hw _).le (d.bien i f hf)) (Real.exp_nonneg _); exact le_rfl
    · split_ifs with h; swap; · exact mul_nonneg hr.le (sum_nonneg (fun _ _=>(hF _).1 _))
      have hp:= Finset.single_le_sum (f:=fun z=>Q z i) (s:=s) (a:=D.center o i) (fun z _=>(hF z).1 i) (Animals.neighbors_back _ h); rw [show Q (D.center o i) i=_ from if_pos (c:=D.center o i=D.center o i) rfl] at hp; rw [mul_comm Ω]; apply mul_le_mul hp _ (Real.exp_pos _).le (sum_nonneg (fun _ _=> (hF _).1 _))
      exact Real.exp_monotone (mul_le_mul_of_nonneg_left (hτ _) ha)
    have hp: ((Animals.ballCost H):ℝ)* b ≥ r':= by unfold r'; simp only [Finset.sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Animals.neighbors_card ..)) (budget_nonneg (hH x));
    refine le_trans (mul_le_mul_of_nonneg_left hp hr.le) (le_of_eq (mul_assoc Ω _ _).symm)
end Deck
end YM.QuadraticLocal.Shelter
