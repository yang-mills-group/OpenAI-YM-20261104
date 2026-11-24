import YangMills.WilsonProof.NativeSupport.YM.MS.Shine.Purity
/-!
# Pole continuation of time Euler resolvent on smooth forms

Momentum coefficients $Taylor η$. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Hem
open Set Filter Function Finset MeasureTheory Metric Arc
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine
open scoped Topology ContDiff
variable {I:Type}{G:Gauge}{j m n k:ℕ}{x:ℂ}{R:ℝ}
variable {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
  [NormedAddCommGroup F][NormedSpace ℝ F]
open ContinuousLinearMap Tensor
lemma consPrice {g:I→ E→ Tensor.T E F j}(h:veg 0 g 1): veg 0 (fun i p=> Tensor.diagonal (g i p) p) 1:= by
    induction j with
    | zero=> -- constant vec
       let A:Tensor.T E F 0→L[ℝ] F := (continuousMultilinearCurryFin0 ℝ E F).toContinuousLinearEquiv.toContinuousLinearMap; convert! h.L A using 1; funext i p; exact congr_arg (g i p) (Subsingleton.elim ..)
    | succ k ih=>
       let L := Tensor.T E F k; let S := continuousMultilinearCurryLeftEquiv ℝ (fun _:Fin (k+1)=> E) F; let T : Tensor.T E F (k+1) →L[ℝ] (E→L[ℝ] Tensor.T E F k):= S.toContinuousLinearEquiv.toContinuousLinearMap; let V(i:I)(x:E) : Tensor.T E F k:= T (g i x) x
       have hp:veg 0 V 1:= by convert Costs.bilinear (ContinuousLinearMap.apply ℝ (Tensor.T E F k)) (uGrab (Alps.Bench.Forest.at_id (E:=E)) (fun _:I=>())) (Costs.L (G:=(E→L[ℝ] Tensor.T E F k)) T h) using 1; rfl; ext; simp
       have hu {i:I}{p:E}: Tensor.diagonal (g i p) p= Tensor.diagonal (V i p) p := by
           unfold Tensor.diagonal V; exact congr_arg (g i p) (funext fun w=>Fin.cases rfl (fun _=>by simp) w)
       simp_rw [hu]; exact ih hp
lemma merch {f:I→E→ℂ}(h:veg 0 f 1)(j:ℕ): veg 0 (fun i=> stage j (f i)) 1:= by
   obtain ⟨C,hC,b,hb⟩:= ride h j; have hp : scaleC 0 1 fun i=> ‖iteratedFDeriv ℝ j (f i) 0‖ := by
       refine ⟨C,hC,0,fun i p hp=>?_⟩; simpa using hb i 0 -- Unit coercion
   apply consPrice (g:=fun i x=>Tensor.coeff (f i) j 0); exact (at_rate (w:=fun i=>iteratedFDeriv ℝ j (f i) 0) (E:=E) hp).L ((Nat.factorial j :ℝ)⁻¹ • ContinuousLinearMap.id ℝ (Tensor.T E ℂ j)) -- hp orient
-- complex derivative lift
variable [FiniteDimensional ℝ E][NormedSpace ℂ F][IsScalarTower ℝ ℂ F][CompleteSpace F]
private def ble (v:E): (E→L[ℝ] F)→L[ℂ] F where
   toFun:= ContinuousLinearMap.apply ℝ F v
   map_add':= map_add _
   map_smul' t x:= by rfl
lemma billJet {f:ℂ→ E→ F}(h:Plots (disc R) f)(p:E)(s:Fin j→ E) : Forest (disc R) fun x=> iteratedFDeriv ℝ j (f x) p s:= by
    induction j generalizing F with
    | zero=> simp only [iteratedFDeriv_zero_apply]; exact h.root p
    | succ j ih=>
       have hp:= ih (h.tell isOpen_ball) (Fin.init s); intro i hi; simp_rw [iteratedFDeriv_succ_apply_right]; exact (ble (F:=F) (s (Fin.last j))).differentiableAt.comp i (hp i hi) -- parse
lemma jet {f:ℂ→ E→ℂ}(h:Plots (disc R) f)(j:ℕ): Plots (disc R) (fun i=>stage j (f i)) where
    span:= fun c R hr hp=> merch (h.span c R hr hp) j
    root p z hp:= DifferentiableAt.const_smul (billJet (j:=j) h 0 (fun _=> p) z hp) _
lemma key_fall {f:ℂ→Mob G}(h: Hol (disc R) f)(w:Touch G m E) : Plots (disc R) (fun z=>fieldVal (f z m) w) := ⟨fun c R hc hp=> h.price c R hc hp m E w, fun _=> h.top m _⟩
end YM.MS.Hem
