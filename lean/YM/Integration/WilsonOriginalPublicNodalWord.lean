import YM.Integration.WilsonOriginalPublicNodalBirth
import YM.Integration.WilsonOriginalPublicTrialNormalization
import YM.Comparison.Density.Render.Valence

/-! Independent finite-volume normalization of the original, individually
located Wilson words on the independently prescribed inversion tree. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 1300000
namespace YM.Integration.WilsonOriginalPublicNodalWord
open Function Finset Lattice Wilson RG Labels Source Pert.Asymptotics Laurent
open XSpace PertExtension PertExtension.Orb
open ActualRunPhysicalPages PhysicalNext.Repeat.Legato RegulatorIR.FVAAlt2
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider
open WilsonThermometerDeclaredSeeds (Choice entry)
open WilsonThermometerPositionTunedSlope (Columns)
open WilsonOriginalStarSceneWords (raw)
open WilsonReceivedCanonicalVersePortfolio (Selection weight)
open WilsonReceivedCanonicalVersePosterior (word)
open WilsonReceivedCanonicalVerseBasis (restored)
open WilsonOriginalPublicNodalFibre (change complete)
open WilsonOriginalPublicNodalCanonical (request)
open private combine from YM.Integration.WilsonOriginalPublicTrialNormalization
open scoped Classical BigOperators ContDiff
variable {G:Gauge}(R:Run G){I:Type}[LinearOrder I](d:I→ℕ){h:I→ℕ}
    (κ:(j:I)→Knob (h j))(pt:I→Chamber)

private theorem regular {r:ℕ}(A:Atom G r){P:Period}(T:P.Tree)(z:Site P.side):
    ContDiffAt ℝ ∞ (fun Y:T.Field G=>A.unmasked (T.links Y) z) 0:=by
  let L:T.Field G→L[ℝ]Directions G P.side:=T.covering.toContinuousLinearMap
  let f (y:Directions G P.side):ℝ:=A.unmasked (increment 1 y) z
  have full:ContDiffAt ℝ ∞ f 0:=contDiffAt_infty.mpr fun n=>
    (Comparison.Density.Render.reserved (k:=n) A z (by simp:‖(0:Directions G P.side)‖≤1)).smooth
  have tree:∀x:T.Field G,increment 1 (L x)=T.links x:=by
    intro x;funext e
    simp [increment,Period.Tree.links_apply,L]
  have at_zero:ContDiffAt ℝ ∞ f (L 0):=by simpa using full
  simpa only [Function.comp_def,f,tree] using at_zero.comp 0 L.contDiff.contDiffAt

theorem smooth (S:Finset I)(z:I→ Cover)(t:ℝ)(c:Selection R d S)(P:Period)(T:P.Tree):
    ContDiffAt ℝ ∞ (fun X:T.Field G=>word R d κ pt t (fun j=>wrap P.side (z j)) S c (T.links X)) 0:=by
  let f (j:S)(X:T.Field G):=restored R d κ pt t j (c j) (wrap P.side (z j)) (T.links X)
  have each (j:S):ContDiffAt ℝ ∞ (f j) 0:=by
    simp only [f,restored,WilsonReceivedCanonicalVerseBasis.field]
    exact contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp _
      (regular (raw R d (entry R d j (c j))) T (wrap P.side (z j))))
  have sum (a:Finset S):ContDiffAt ℝ ∞ (fun X:T.Field G=>∏j∈a,f j X) 0:=by
    induction a using Finset.induction_on with
    | empty => simpa using (contDiffAt_const (c:=(1:ℂ)) (x:=(0:T.Field G)) (n:=∞) (𝕜:=ℝ))
    | insert j a hj ih => simpa only [Finset.prod_insert hj] using (each j).mul ih
  exact sum univ

/-- The same real marked word is integrated against the chosen inversion
vacuum, with all powers and the vacuum divisor supplied by that tree. -/
def sheet (S:Finset I)(z:I→ Cover)(t:ℝ)(c:Selection R d S)(P:Period)(T:P.Tree):PowerSeries ℂ:=
  Bare.normalized T G (Taylor.expandTaylor (T.basis G) (fun X=>
    word R d κ pt t (fun j=>wrap P.side (z j)) S c (T.links X)))

variable {N p K:ℕ}(live:K≤N)
local notation "g" => regulatorRun R.family N p K
include live in
theorem filed (S:Finset I)(b:Columns R (fun j:S=>d j))(z:I→ Cover)(t:ℝ)(ht:t≠0)(P:Period)(T:P.Tree):
    WilsonPositionProgramCopyTop.normalized R P (fun j:S=>d j) (fun j:S=>z j) b T=
      ∑c:Selection R d S,(weight R d N p K (request R d (complete R d S b) (N:=N) (p:=p) (K:=K)) S c*
        change R d (N:=N) (p:=p) (K:=K) t S c) • sheet R d κ pt S z t c P T:=by
  let cash(c:Selection R d S):=weight R d N p K (request R d (complete R d S b) (N:=N) (p:=p) (K:=K)) S c*
        change R d (N:=N) (p:=p) (K:=K) t S c
  let test(c:Selection R d S)(X:T.Field G):=word R d κ pt t (fun j=>wrap P.side (z j)) S c (T.links X)
  have basis:(fun j:S=>complete R d S b j.val)=b:=by funext j;simp [complete]
  have offered: (fun X:T.Field G=>((WilsonPositionProgramCopyTop.planted R P (fun j:S=>d j) (fun j:S=>z j) b
      (T.links X):ℝ):ℂ))=fun X=>∑c:Selection R d S,cash c*test c X:=by
    funext X
    have opened:=WilsonOriginalPublicNodalFibre.sliced R d (p:=p) live κ pt (complete R d S b) z S t ht (T.links X)
    rw [basis] at opened
    exact opened
  change Bare.normalized T G (Taylor.expandTaylor (T.basis G) (fun X:T.Field G=>
    ((WilsonPositionProgramCopyTop.planted R P (fun j:S=>d j) (fun j:S=>z j) b (T.links X):ℝ):ℂ)))=_
  rw [offered,combine (T.basis G) cash test (fun c=>smooth R d κ pt S z t c P T),map_sum]
  apply sum_congr rfl
  intro c _
  rw [map_smul]
  rfl

end YM.Integration.WilsonOriginalPublicNodalWord
end
