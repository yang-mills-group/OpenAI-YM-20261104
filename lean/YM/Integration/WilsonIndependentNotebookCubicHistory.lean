import YM.Integration.WilsonIndependentNotebookCubicLedger

/-! Chronological cut by the first genuine cross-source conditional. Each
such deposit is transported once to the given older physical receiver. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentNotebookCubicHistory
open Lattice RG Precision WilsonCoeffUV WilsonCoeffUV.Mer
open WilsonIndependentNotebookCubicField (issue)
open WilsonIndependentNotebookCubicLedger (deposit)
open scoped BigOperators Classical
variable {G:Gauge}

theorem original (A:Levels G){Ñ:ChartRatio G}(simple:G.Simple)(ratio:LocalRatio Ñ)
    (m N i j k n:ℕ)(span:m+n ≤ N)(X Y D:ℕ→Era G ℝ)
    (x:∀t ≤ n,Auth i (X t))(y:∀t ≤ n,Auth j (Y t))(d:∀t ≤ n,Auth k (D t))
    (left:∀t<n,verseI A Ñ (m+t) N i (X (t+1))=X t)
    (right:∀t<n,verseI A Ñ (m+t) N j (Y (t+1))=Y t)
    (changed:∀t<n,verseI A Ñ (m+t) N k (D (t+1))=D t):
    cruises A Ñ N (i+j+k) (m+n) m (agateV (agateV (X n) (Y n)) (D n))=
      agateV (agateV (X 0) (Y 0)) (D 0)+∑t∈Finset.range n,
        deposit A Ñ N (i+j+k) (m+t) m (issue A Ñ (m+t) N i j k (X (t+1)) (Y (t+1)) (D (t+1))):=by
  induction n with
  | zero => simp [cruises_top]
  | succ n ih =>
    have previous:=ih (by omega) (fun t ht=>x t (by omega)) (fun t ht=>y t (by omega))
      (fun t ht=>d t (by omega)) (fun t ht=>left t (by omega)) (fun t ht=>right t (by omega))
      (fun t ht=>changed t (by omega))
    rw [Finset.sum_range_succ,←add_assoc (agateV (agateV (X 0) (Y 0)) (D 0)) _ _,←previous]
    have bank:=WilsonIndependentNotebookCubicLedger.filed A simple ratio (Nat.le_add_right m n)
      (by omega : m+n<N) (x _ le_rfl) (y _ le_rfl) (d _ le_rfl)
    change _=cruises A Ñ N (i+j+k) (m+n) m
      (agateV (agateV (verseI A Ñ (m+n) N i (X (n+1))) (verseI A Ñ (m+n) N j (Y (n+1))))
        (verseI A Ñ (m+n) N k (D (n+1))))+_ at bank
    rw [left n (Nat.lt_succ_self _),right n (Nat.lt_succ_self _),changed n (Nat.lt_succ_self _)] at bank
    exact bank

/-- Signed one-arm substitution. Every unaffected ordinary appointment and
both complete C histories are on the same original vacuum. -/
theorem difference (A:Levels G){Ñ:ChartRatio G}(simple:G.Simple)(ratio:LocalRatio Ñ)
    (m N i j k n:ℕ)(span:m+n ≤ N)(X Y C V:ℕ→Era G ℝ)
    (x:∀t ≤ n,Auth i (X t))(y:∀t ≤ n,Auth j (Y t))
    (c:∀t ≤ n,Auth k (C t))(v:∀t ≤ n,Auth k (V t))
    (left:∀t<n,verseI A Ñ (m+t) N i (X (t+1))=X t)
    (right:∀t<n,verseI A Ñ (m+t) N j (Y (t+1))=Y t)
    (actual:∀t<n,verseI A Ñ (m+t) N k (C (t+1))=C t)
    (fitted:∀t<n,verseI A Ñ (m+t) N k (V (t+1))=V t):
    let D:=fun t=>C t-V t;let J:=cruises (V:=ℝ) A Ñ N (i+j+k) (m+n) m
    J (agateV (agateV (X n) (Y n)) (C n))-J (agateV (agateV (X n) (Y n)) (V n))=
      agateV (agateV (X 0) (Y 0)) (D 0)+∑t∈Finset.range n,
        deposit A Ñ N (i+j+k) (m+t) m (issue A Ñ (m+t) N i j k (X (t+1)) (Y (t+1)) (D (t+1))):=by
  intro D J
  have diff t (ht:t<n):verseI A Ñ (m+t) N k (D (t+1))=D t:=by
    dsimp only [D]
    rw [verse_lin A simple (by omega) ratio (c _ (by omega)) (v _ (by omega)),actual t ht,fitted t ht]
  have result:=original A simple ratio m N i j k n span X Y D x y (fun t ht=>(c t ht).sub (v t ht))
    left right diff
  dsimp only [D] at result ⊢
  rw [pairingP,cruisePlus A (Nat.le_add_right m n) simple ratio span
    (((x n le_rfl).manor (y n le_rfl)).manor (c n le_rfl))
    (((x n le_rfl).manor (y n le_rfl)).manor (v n le_rfl))] at result
  exact result

end YM.Integration.WilsonIndependentNotebookCubicHistory
