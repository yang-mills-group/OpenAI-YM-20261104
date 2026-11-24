import YM.FormalOPE.RG10.Boardwalk.Lawn
/-! # Staircase through finite orientation orders
 Up to $r$, irrespective of higher terms in Laurent weights etc. Does not use
 power-loss nonlinear match assumptions. Same regular baseline on ANY shape Test.
 Later need moving Mark orientations arity fixed; Thorax handles that. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalOPE.RG10.Boardwalk.Gliss
open Filter Function Finset PowerSeries Clearing Ledger Rates InversionTop
open Carryon PertExtension Position Maxwell Labels Extraction Filter Extra.FD
open PertExtension MeasureTheory Topology Metric PertExtension.Position Triangle Lawn
open scoped Topology BigOperators Classical ContDiff
variable {I T J : Type*}{l:Filter I}{r n :ℕ}
variable {P:Path l}
variable [Fintype J]{a:T→ℕ}{D:TestSystem J T a}
local notation "Φ"=>Mark J a
local notation "σ"=>D.Z
local notation "Π'"=>D.Parameter
variable {w: Mark J a→ℝ}{x y : I→ Mark J a→fps}{L M : I → FrameAt J fps}
local notation "U" i =>scale (D:=D) w (x i)
local notation "V" i =>scale (D:=D) w (y i)
variable (hP : D.Regular w)
variable (he:Tendsto (fun i=> dial D (x i)) l (𝓝 (w ∘ markIn D.tests)))

-- fixed scheme tests, but ANY field positions, budget on evaluating that full tensor.
-- Need use after correlation comparison on precisely the array x and y; incl when centers &
-- arities shifted, authenticate to supplying one actual geometry at each epoch.
def Answers (P:Path l) (r:ℕ)(x y:I→ Mark J a→ fps)(v:T):= ∀ p : Fin (a v) → J,Posi P r (fun i=> x i ⟨v,p⟩) (fun i=> y i ⟨v,p⟩)

lemma Answers.seen {t} (h:Answers P r x y t)(hz:∀ j k, Posi P r (fun i=>L i j k) (fun i=> M i j k)): Answers P r (fun i=> PertExtension.Position.insert J a (x i) (L i)) (fun i=>PertExtension.Position.insert J a (y i) (M i)) t := fun v=>
 Posi.sum _ fun p _=> (h p).mul (Posi.product _ (fun i _=> hz (v i) (p i)))

variable (hx:∀ j∈D.tests, Answers P r x y j)
include hx
lemma testVector : Fair P (fun i=> dial D (x i)) (fun i=>dial D (y i)):= by
 apply Fair.questionnaire; intro j; rcases j with ⟨v,p⟩; unfold Lawn.dial; simp_rw [← coeff_zero_eq_constantCoeff_apply]; exact hx v.val v.property p 0 (Nat.zero_le _)

section response
def response (D:TestSystem J T a)(w : Mark J a→ℝ)(x : Mark J a→fps)(L:FrameAt J fps)(k:ℕ) : D.Z:=(scale (D:=D) w x).response x L k

lemma folder {k:ℕ} (hk:k≤r)(hp:∀ i j,Posi P r (fun t=>L t i j) (fun t=>M t i j)) : Fair P (fun i=> response D w (x i) (L i) k) (fun i => response D w (y i) (M i) k):= by
 let F (i) (x:I→Mark J a→fps) (L:I→ FrameAt J fps) := (fun j=>coeff k (PertExtension.Position.insert J a (x i) (L i) (markIn D.tests j)))
 apply (Fair.questionnaire (show ∀ j, Fair P (fun i=> (F i x L) j) (fun i=> F i y M j) from ?_)).map D.select.toContinuousLinearMap; intro x; rcases x with ⟨j,p⟩; exact (hx j.val j.property |>.seen hp) p k hk
end response

include hP he
lemma stack (hn:n≤r) (i j:J): Posi P r (fun k=>(scale (D:=D) w (x k)).stack (x k) n i j) (fun k=>(scale (D:=D) w (y k)).stack (y k) n i j):= by
 induction n generalizing i j with
 | zero => simp_rw [TestSystem.stack]; exact Posi.showC (((baseline hP he (testVector hx)).map (ContinuousLinearMap.proj i)).map (ContinuousLinearMap.proj j))
 | succ n ih=>
   let hc : n ≤ r:=by omega
   let L'(w) (x:I→ Mark J a→fps)(i):= (Lawn.scale (D:=D) w (x i)).stack (x i) n
   let B (x:I→ Mark J a→fps)(w)(k:I): σ:=Rfix D w (x k) (-(response D w (x k) (L' w x k) (n+1)))
   have H: Fair P (B x w) (B y w):= Lawn.repair hP he (testVector hx) (folder hx hn (ih hc)).neg
   exact (ih hc i j).join (((Posi.showC (r:=r) ((((H.map D.Z.subtypeL).map (ContinuousLinearMap.proj i)).map (ContinuousLinearMap.proj j)))).mul (Posi.fixed (PowerSeries.X^ (n+1):fps)))) -- definitional reduction

lemma posture (i j : J): Posi P r (fun k=>(scale (D:=D) w (x k)).position (x k) i j) (fun k=>(scale (D:=D) w (y k)).position (y k) i j):= by
 intro k hk; simp_rw [TestSystem.position, coeff_mk]; exact stack hP he hx hk i j k hk

theorem relocated {u:T}(hu:Answers P r x y u): Answers P r (fun i=> (scale (D:=D) w (x i)).positioned (x i)) (fun i=>(scale (D:=D) w (y i)).positioned (y i)) u:= hu.seen (posture hP he hx)
-- varying SHAPES test x(U): arity EXACT n fixed

end YM.FormalOPE.RG10.Boardwalk.Gliss
