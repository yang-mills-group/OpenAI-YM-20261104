import YM.Integration.WilsonIndependentNotebookCubicHistory

/-! Instantiate the cubic ledger with the four actual K-born fields and
the entire N-born quiet. Their dated singleton inputs are calculated by
the normalized transfer itself. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentNotebookCubicSeeds
open Lattice RG Precision WilsonCoeffUV WilsonCoeffUV.Mer
open WilsonIndependentNotebookCubicField (issue)
open WilsonIndependentNotebookCubicLedger (deposit)
open scoped BigOperators Classical
variable {G:Gauge}

def ray (A:Levels G)(Ñ:ChartRatio G)(N h m n:ℕ)(P:Era G ℝ)(t:ℕ):Era G ℝ:=
  cruises A Ñ N h (m+n) (m+t) P

def bill (A:Levels G)(Ñ:ChartRatio G)(m N i j k n:ℕ)(X Y U V:Era G ℝ):Era G ℝ:=
  let x:=ray A Ñ N i m n X;let y:=ray A Ñ N j m n Y
  let d:=fun t=>ray A Ñ N k m n U t-ray A Ñ N k m n V t
  agateV (agateV (x 0) (y 0)) (d 0)+∑t∈Finset.range n,
    deposit A Ñ N (i+j+k) (m+t) m (issue A Ñ (m+t) N i j k (x (t+1)) (y (t+1)) (d (t+1)))

theorem original (A:Levels G){Ñ:ChartRatio G}(simple:G.Simple)(ratio:LocalRatio Ñ)
    {m N i j k n:ℕ}(span:m+n ≤ N){X Y U V:Era G ℝ}
    (x:Auth i X)(y:Auth j Y)(u:Auth k U)(v:Auth k V):
    let J:=cruises (V:=ℝ) A Ñ N (i+j+k) (m+n) m
    J (agateV (agateV X Y) U)-J (agateV (agateV X Y) V)=bill A Ñ m N i j k n X Y U V:=by
  intro J
  have book {h:ℕ}{P:Era G ℝ}(paid:Auth h P)(t:ℕ)(ht:t ≤ n):
      Auth h (ray A Ñ N h m n P t):=cruising A simple ratio (by omega) span paid
  have step (h:ℕ)(P:Era G ℝ)(t:ℕ)(ht:t<n):
      verseI A Ñ (m+t) N h (ray A Ñ N h m n P (t+1))=ray A Ñ N h m n P t:=
    (cruises_sub A Ñ N h P (by omega : m + t < m + n)).symm
  have row:=WilsonIndependentNotebookCubicHistory.difference A simple ratio m N i j k n span
    (ray A Ñ N i m n X) (ray A Ñ N j m n Y) (ray A Ñ N k m n U) (ray A Ñ N k m n V)
    (book x) (book y) (book u) (book v) (step i X) (step j Y) (step k U) (step k V)
  dsimp only at row
  simp only [ray,cruises_top] at row
  exact row

end YM.Integration.WilsonIndependentNotebookCubicSeeds
