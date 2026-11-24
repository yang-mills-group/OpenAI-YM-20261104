import YM.FVAAlt2.Turn.Linear
import YM.FVAAlt2.Plus.High -- inspect plus.
/-! Finite assemblies of ACT menus. Coefficientwise operations, preserving explicit
 dollar/product parametrization. Important: `U j` may have ANY height, but all
 uses in rentPl depend only on THEIR height for bare part. -/
noncomputable section
set_option autoImplicit false
namespace YM.MS.FVA.Town
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color Book _root_.YM.MS.Shine Hem Mell Logarithm Pearl Train Dock Emit
open Signal Book Convolve High Detect Domain Tone Tone.Frame Momentum Outlook Motif Literal Mach
open _root_.YM.MS.Wind _root_.YM.MS.City Native Native.Wilsonian Native.Orient
open Motions FVA.City Leading Knobs Menus Program Lifting Local.Physical Cylinder Cylinder.Taylor Cylinder.Lab Paint Lattice
open scoped Topology BigOperators ContDiff Interval
set_option linter.unusedSectionVars false
variable {G:Gauge}{I:Type}{B:Deck G}{d n k:ℕ}{x:ℝ}(V:RichBook B)(t:Team)
-- sum with REAL finance. if votes sizes differ also preserve via outside fit
variable (u:Finset I) (f:I→ℝ) (p:I→ Acts B d)
-- no pos_
def kitty (r:ℕ)(x:ℝ): Dot G Cover:= ∑ i∈u,(f i:ℂ) • ((p i r).proof.input x)
def labor (n:ℕ): Power G where
   allowance:= u.sup fun i=> (p i n).proof.allowance
   input:= kitty u f p n
   polyn:= value_sum _ (fun j _=> Ready.scale_p ((p j n).proof.polyn) (f j))
   actual i:= Tune.sum _ (fun j _=> ((p j n).proof.actual i).cash _ (by simp))
   calm i:= Colorless.csum _ (fun j _=> ((p j n).proof.calm i).smul _)
   ranks i:= by rw [ kitty,sum_stack]; apply Limit.sum _; intro j hj; exact (((p j n).proof.ranks i).smul _ ).up (Nat.cast_le.mpr (Finset.le_sup (f:=fun i=>(p i n).proof.allowance) hj))

def venture : Acts B d:= fun r=> ⟨ fun j=>∑ i∈u,Polynomial.C (f i)*(p i r).register j,labor u f p r⟩
lemma paysV (r:ℕ)(j:Glyph B d)(x:ℝ) : oil (venture u f p) j r x =∑ i∈u,(f i:ℂ) * oil (p i) j r x:= by simp_rw [ oil, venture, Polynomial.eval_finsetSum, Polynomial.eval_mul,Polynomial.eval_C, Complex.ofReal_sum,Complex.ofReal_mul ]
lemma whirlW (x:ℝ)(r:ℕ): motto t (venture u f p) x r=∑ i∈u,(f i:ℂ) • motto t (p i) x r:=by
 simp_rw [ sky ]; unfold venture labor kitty; simp_rw [map_sum,map_smul,smul_add, Finset.smul_sum,Finset.sum_add_distrib]; rw [Finset.sum_comm (s:=antidiagonal r) (t:=u)]
lemma venture_tV (r:ℕ)(x:ℝ): Menus.rentPl V t (venture u f p) x r=∑ i∈u, (f i:ℂ) • Menus.rentPl V t (p i) x r := by
  unfold Menus.rentPl; simp_rw [paysV,Finset.sum_smul, Finset.smul_sum, mul_smul]; simp_rw [sum_comm (t:=u) (s:=antidiagonal r)]; rw [Finset.sum_comm]
lemma incomeV : scorePl V t ( venture u f p )=∑ i∈u,(f i:ℂ) • scorePl V t (p i) := by
   funext x r; simp only [scorePl,Pi.add_apply, Finset.sum_apply, Pi.smul_apply, venture_tV, whirlW, smul_add, Finset.sum_add_distrib ]

-- Actual rotated Actor.One stanza
variable {W:Type} (s:Signed) (R: Matrix (Glyph B d) (Glyph B d) ℝ)(A:Acts B d)
open Matrix
local notation "φ"=> Orient.pose s
-- no billing change.phase
private def costMove (M:Power G): Power G where
   allowance:= M.allowance
   input:= (φ) ∘ M.input
   actual i:= tune_H s ( M.actual i )
   calm i:= pose_color s (M.calm i)
   polyn:= Ready.linear M.polyn ((φ).restrictScalars ℝ)
   ranks i:= poses_limit s ( M.ranks i )
def drives (n:ℕ): Tact B d:= ⟨ fun j=>∑ i:Glyph B d,(A n).register i * Polynomial.C (R i j), costMove s ( A n ).proof ⟩
lemma drivesOil (i:Glyph B d)(n:ℕ)(x:ℝ): oil (drives s R A) i n x=∑ j:Glyph B d,oil A j n x * (R j i:ℂ):=by simp_rw [ oil, drives, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Complex.ofReal_sum, Complex.ofReal_mul ]
lemma drive_msg (x:ℝ)(n:ℕ): motto t (drives s R A) x n = φ (motto t A x n):=by
 rw [sky, sky ,map_add,reflect_Lcover,map_sum]; simp_rw [reflect_style]; rfl
abbrev formsH: Prop:=∀ (i:Glyph B d)(x:ℝ)(n:ℕ), φ (Glyph.preamblePl V t i x n) = ∑ j:Glyph B d,(R i j:ℂ) • Glyph.preamblePl V t j x n -- shadow s bug remove
lemma turn_rents (x:ℝ)(n:ℕ)(hr:formsH V t s R): Menus.rentPl V t (drives s R A) x n= φ (Menus.rentPl V t A x n):=by
 unfold Menus.rentPl; simp only [map_sum,map_smul,drivesOil, Finset.sum_smul, smul_smul, hr, Finset.smul_sum]; simp_rw [Finset.sum_comm (t:=antidiagonal n) (s:=univ)]; exact sum_congr rfl (fun _ _=> Finset.sum_comm); -- reorder.Signed
lemma turn_score (hr:formsH V t s R): scorePl V t (drives s R A) = promoteT s G (scorePl V t A):= by funext i j; change Menus.rentPl _ _ _ i j+ _= φ (_+_); rw [ turn_rents V t s R A _ _ hr, map_add,drive_msg]

-- after motion + finances. Exact `mark births` estimates then ∴ unique.
lemma bill_move (h:formsH V t s R): horizonPl V t (drives s R A) = trailer s (horizonPl V t A):= Lobby.unique (turn_score V t s R A h ▸ foyer ( aquaPl V t (drives s R A))) ( burning_sat s t ( skyPC G t ) (foyer (aquaPl V t A)) ) -- direction of replacement
lemma bill_total : horizonPl V t (venture u f p) = ∑ i∈u, (f i:ℂ) • horizonPl V t ( p i ):= Lobby.unique (incomeV V t u f p ▸ foyer (aquaPl V t (venture u f p))) ( Lobby.fin _ (fun i _=> (foyer (aquaPl V t (p i))).static (f i:ℂ)) )
end YM.MS.FVA.Town
