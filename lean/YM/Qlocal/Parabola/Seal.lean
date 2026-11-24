import YM.Qlocal.Parabola.Branch
import YM.Extra.ITERATION_NO_LOSS.Sums
import YM.Qlocal.Parabola.Grain
import YM.Qlocal.Parabola.Stars
import YM.Progress.DIRECTED_RECIPE.Tender
/-!
 # ℂ POLY post closure for PURELY marked attachments
  Uniform costs at the scheduler's true exponent, chosen BEFORE all tests.
  Because choosing input κ-margin.T.Counter.Shape.W Degree tree, need numerical
  criterion for `ρ v+r` with `corr h` relative sizes.Be.Act. Deliver at no assumption
  of finitely many marks/associated terms. Also pointwise identity in `Branch.lean`.
  Need h causes onto masks.Fixed geometry.Beach.K.Filename.I. Session μ. E spills later.
  Uses every K (no free attachment with no K). Old marked K includes unmarked Real.C.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Parabola
open Function RG Lattice Wilson Pert.Attach MeasureTheory Filter Progress.DirectedRecipe Finset
open Marker RG03.Gather Bank Push.AbsoluteSums
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{n:Side}{P:BudgetPoint}{δ κ κ' t v c d e ε μ z b:ℝ}
  {A: Activities G n} {X:Corrections G n}{V Ω:Type} [DecidableEq V] {R:Census V}
  {q : Ray R}
-- Additional reserve exponents. Numeric.Se.
abbrev Force (G:Gauge)(V:Type)(n:Side):= Config G n→V
def Haze {α:Type} (s:α→Support n)(j:ℕ)(t:ℝ)(f:α→Ray R)(q:Ray R)(v:ℝ):= (∀ i,0 ≤ f i) ∧ Ac.Hit s j (fun i=>Parabola.bill q (f i)) t v
namespace Haze
variable (p:Rental q) {j:ℕ}{c':ℝ}{α:Type} {Y:α→ Support n} {f g:α→ Ray R}
include p
lemma NN (h: Haze Y j t f q v):0 ≤ v:=budget_nonneg (h.2 0)
omit p
lemma add (h0:Haze Y j t f q v)(h1:Haze Y j t g q c): Haze Y j t (f+g) q (v+c) := by
 refine ⟨fun i k=>add_nonneg (h0.1 i k) (h1.1 i k),fun i=>?_⟩
 convert budget_plus (h0.2 i) (h1.2 i) using 2 with k; split <;> simp [*, Haze,bill_add, add_mul]
include p
lemma fades (h : Haze Y j t f q v)(ht:δ ≤ t) : Haze Y j δ f q v:= by
 refine ⟨h.1, fun i=>budget_mono (h.2 i) ?_ ?_⟩
 · intro i; split; exact mul_nonneg (bill_nn (h.1 _) p.oneSize) (Real.exp_nonneg _); rfl
 intro k; split; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right ht (by positivity))) (bill_nn (h.1 _) p.oneSize); rfl
variable (C:Bank A ε)
end Haze
variable (C:Bank A ε) (P) (X)
variable {I K: Ω→ℕ→Config G n→Poly R} {j:ℕ}{J L: ℕ→Ray R}
set_option quotPrecheck false
local notation "T"=> X.region
local notation "At"=> (fun i=> (A.forced i).support)
noncomputable abbrev aura (i:ℕ) := grit (parts A X i) (Sum.elim L J) -- no Arguments 
local notation "Y'"=> fun i=> aura X (L:=L) (J:=J) (A:=A) i
local notation "U'"=> (Sum.elim L J)
variable (p:Rental q)
variable (Z: Haze (fun i=>(A.forced i).support) j (t+δ) L q v) (Z': Haze X.region j (t+δ) J q b)
local notation "A'"=> U'
include Z Z' p
lemma tower (hk:1≤κ) (hv:StellarTree.sites j * (κ*v+b) ≤ δ)(ht:0≤t) : Haze (fun i=>(page A X i).support) j t (fun i=> aura X (A:=A) (L:=L) (J:=J) i) q (κ⁻¹*(Real.exp (κ*v+b)-1)):= by
 let f:Old→ℝ:= Sum.elim (fun i=>κ*Parabola.bill q (L i)) (fun i=> Parabola.bill q (J i)); let g:Old→ℝ:= fun i=> Parabola.bill q ((A') i); have hf(i):0 ≤ U' i:= Sum.rec (motive:=fun z=>0≤U' z) Z.1 Z'.1 i
 have hq:0<κ:=zero_lt_one.trans_le hk; have hp i :0≤g i:=bill_nn (hf i) p.oneSize
 have hl(i): g i ≤ f i:= by cases i with | inl i=> exact le_mul_of_one_le_left (hp (Sum.inl i)) hk | inr i=>rfl
 have ht'(z):0≤ f z:=(hp z).trans (hl z)
 have hG:Ac.Hit (X.area A) j f (t+δ) (κ*v+b):= by
    intro x; apply Extra.Iteration.Cost.sum
    · convert budget_scale hq.le (Z.2 x) using 2 with i; simp only [Pert.Attach.Corrections.area,f,Sum.elim_inl]; split <;> simp [mul_assoc]
    exact Z'.2 x
 have hh:0≤ κ*v+b:= budget_nonneg (hG 0)
 refine ⟨fun i=> grit_pos (parts A X i) (fun i _=> hf i),fun x=> ?_⟩
 have hω := budget_scale (inv_pos.mpr hq).le (budget_pull (parts A X) (parts_inj A X) (StellarTree.against _ j ht ht' hG hv hh x)); refine budget_mono hω (fun i=>?_) (fun i=> ?_)
 · split; exact mul_nonneg (bill_nn (grit_pos _ (fun i _=> hf i)) p.oneSize) (Real.exp_nonneg _); rfl
 split
 next hi=>
   let U:=parts A X i; have hX : Ac.Spark (X.area A) U∧x∈ U.biUnion (X.area A):= ⟨(decoding A X i).2.1, hi⟩
   unfold Ac.roots; rw [if_pos hX]
   change Parabola.bill q (aura X (L:=L) (J:=J) (A:=A) i) * Real.exp _ ≤ κ⁻¹*(_*_); rw [le_inv_mul_iff₀ hq, mul_comm κ, mul_right_comm, mul_comm (Real.exp _)]; apply mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
   rw [mul_comm _ κ]; refine ((mul_le_mul_of_nonneg_left (grit_fee U p (fun i _=>hf i)) hq.le).trans ?_); obtain ⟨a,ha⟩:= (decoding A X i).2.2.1; have he:.inl a∈U:= mem_toLeft.mp ha; change κ*(∏ i∈U,g i) ≤ ∏ i∈U,f i; rw [← mul_prod_erase U g he,← mul_prod_erase U f he,← mul_assoc]; exact mul_le_mul_of_nonneg_left (prod_le_prod (fun i _=> hp i) (fun i _=>hl i)) (ht' (Sum.inl a)) -- implicit elaboration
 next=>exact hω.1 _
omit Z Z' p
variable (K I)
set_option quotPrecheck false
local notation "F"=> Bank.fresh C X
local notation "δ!"=> Ovens.folio
noncomputable def correctionIndex : ℕ ↪ ℕ := ⟨C.reticket X,C.reticket_injective X⟩
noncomputable abbrev dawn (C:Bank A ε)(X:Corrections G n)(L J:ℕ→Ray R):= stuff (correctionIndex X C) (aura X (A:=A) (L:=L) (J:=J)) -- implicit inference A
local notation "D"=> dawn C X L J
lemma carry_fog (h: Haze (fun i=>(page A X i).support) j t (fun i=>aura X (A:=A) (L:=L) (J:=J) i) q e): Haze (At) j t (dawn C X L J) q e:= by
 refine ⟨fun i=>?_,fun x=>transfer_budget (correctionIndex X C) ?_ ?_ (h.2 x)⟩
 · by_cases hv:i∈Set.range (correctionIndex X C); · obtain ⟨v,rfl⟩:=hv; rw [dawn, stuffed]; exact h.1 v
   rw [dawn, blank _ _ hv]
 · intro i; have hc: (A.forced (correctionIndex X C i)).support=(page A X i).support:= C.reticket_area X i; dsimp only; simp only [dawn,stuffed,hc]
 intro i hi; dsimp only; split; rw [dawn,blank _ _ hi,bill]; simp; rfl
variable (hL:∀ x i U,CoverP (L i) (K x i U))(hJ:∀ x i U,CoverP (J i) (I x i U))
local notation "e0"=> (κ⁻¹*(Real.exp (κ*v+b)-1))
local notation "r"=> C.store
include hL hJ
lemma moment (x:Ω)(k:ℕ) (U:Config G n): CoverP (aura X (A:=A) (J:=J) (L:=L) k) (Bank.lifted (A:=A) X P (K x) (I x) k U):= by
 unfold Bank.lifted outKey; let q (i:Old):=Sum.elim (fun i=> K x i U) (fun i=> I x i U) i; let V i:=(U') i; have h(i:Old):CoverP (V i) (q i):=by rcases i with i|i; exact hL x i U; exact hJ x i U
 let hz:=grit_S (parts A X k) q (fun i _=> h i); split; exact hz; exact alto (meets hz)
include Z Z' p
-- don't need V above
lemma broadcast [Fintype V] (hk:1≤κ) (hv:StellarTree.sites j * (κ*v+b) ≤ δ)(ht:0≤t) (hd:0≤δ):
    Haze (fun i=>(A.forced i).support) j t (L + dawn C X L J) q (v+e0) ∧ ∀ (x:Ω)(i:ℕ)(U:Config G n),CoverP (L i + dawn C X L J i) ((C.store X P (K x) (I x)) i U):=by
 let h:= carry_fog X C (tower X p Z Z' hk hv ht);
 refine ⟨Haze.add (Haze.fades p Z (le_add_of_nonneg_right hd)) h,fun x i U=> merges_add (hL x i U) (?_:CoverP (D i) (Bank.fresh C X (Bank.lifted (A:=A) X P (K x) (I x)) i U))⟩
 by_cases he:∃ j, opened (A:=A) X j∧ C.reticket X j=i
 · obtain ⟨j,hj,rfl⟩:=he; rw [Bank.valid C X _ hj, show C.reticket X j=(correctionIndex X C) j from rfl,dawn,stuffed]; exact moment P X I K hL hJ x j U -- order check
 rw [invalid C X _ he, Pi.zero_apply]; exact alto (h.1 i)
end YM.Qlocal.Parabola
