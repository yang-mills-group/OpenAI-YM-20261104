import YM.Comparison.RG02.Thermal.Wick
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Thermal
open Function Filter Finset MeasureTheory
open YM.Marker YM.Multi Order Assembly Actual YM.Lattice YM.Tree
open YM.Precision YM.Next.SectorChange
open Matrix
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff ENNReal
variable {G : Gauge} {V : Type} [DecidableEq V] {R : Census V}
variable {I : Type} [Fintype I] [DecidableEq I]
local notation "Λ" => I→ℝ

open Affinity Gaussian Bulk RG Wilson Exterior YM.Work.F05
open PertExtension.Series
-- wake-up at origin under analytic clock ONLY. Extends to derivative value radial hull.
theorem re_jet {X:Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] {g:X→ℝ} (hg:ContDiffAt ℝ ω g 0) (n m:ℕ) :
    iteratedFDeriv ℝ n (Assembly.jet g m) 0= if n=m then iteratedFDeriv ℝ n g 0 else 0 := by
   have ht : ContDiff ℝ ω (Assembly.jet g m):= Tensor.diag_smooth (Tensor.coeff g m 0) _
   have hm(x:X)(n:ℕ): Assembly.jet (Assembly.jet g m) n x=if n=m then Assembly.jet g m x else 0:= by
       have hu:= Tested.directions (f:=Assembly.jet g m) (ht.contDiffAt.of_le le_top) x
       simp_rw [Clipper.weight] at hu
       exact congr_fun (hu.unique (Tested.Aspiration.single (Assembly.jet g m x) _)) n
   split_ifs with h
   · subst n; refine Tensor.ext_diag _ _ (YM.Analysis.sym_Jet (ht.contDiffAt.of_le le_top)) (YM.Analysis.sym_Jet (hg.of_le le_top)) (funext fun x=>?_)
     have hp := Nat.factorial_pos m; exact mul_left_cancel₀ (a:=((↑(Nat.factorial m):ℝ)⁻¹)) (by positivity) ((hm x m).trans (if_pos rfl))
   refine Tensor.ext_diag _ _ (YM.Analysis.sym_Jet (ht.contDiffAt.of_le le_top)) (fun _ _=>rfl) (funext fun x=>?_)
   have hp:=Nat.factorial_pos n; change _= (0:ℝ);
   exact mul_left_cancel₀ (a:=((↑(Nat.factorial n):ℝ)⁻¹)) (by positivity) (((hm x n).trans (if_neg h)).trans (mul_zero _).symm)

variable {C : RG.History G} (L : Chain C) (N m q : ℕ) (hm : m<N)
local notation "S"=> C.levels.clock.op m q
local notation "c"=> C.S.side m q
local notation "f"=> C.S.side (m+1) q
local notation "R'"=> C.rep N q (m+1)
local notation "P'"=> C.rep N q m
local notation "J"=> C.levels.clock.J (m+1)
-- Lean binder aliases may drop.
variable (F : Forest (C.levels.clock.op m q).ratio) (t:(C.levels.clock.op m q).Choices)
variable [Fintype V]
local notation "α"=> L.kin.alpha N m
local notation "X"=> fieldDir G (C.S.side m q) 1
local notation "K"=> L.step N m q hm
local notation "C'"=> thermal F t (Rep.clip R') (Rep.path R') (Kernel.b K F) L.O

include L hm
variable {F} in
lemma retained : FiniteBound F (R').path (P').path (R').clip (P').clip (α) L.O ((L.step N m q hm).b F) (L.post.Γ J) (L.post.c J) (C.levels.clock.loopCap (m+1)) := by
   rw [show (K).b F=L.kin.stationary N m q F from rfl, L.selected N q _ hm,L.selected N q _ hm.le,L.clips N q _ hm,L.clips N q _ hm.le]; exact L.planned.retains N m q hm F

local notation "Ų"=> (fun u:X=> mainTerm (Rep.clip P') (Rep.path P') (represent u))
-- Local formal vacuum grade zero evaluated at coarse u. No assertion on older inputs.
theorem keeps_class (j : ℕ)(hj : j≤4) : Assembly.jet (Layers.base K F t) j = Assembly.jet Ų j:= by
   funext x
   exact (show _ from (by unfold Assembly.jet Layers.base; rw [((L.keeps N m q hm F) j hj t).2.2]))

-- compare Leading coarse scalar infrared also
theorem maps (x : X) : Bulk.infrared S (R').clip (R').path F t ((K).b F) x=Assembly.jet Ų 2 x := by
   rw [← keeps_class L N m q hm F t 2 (by decide)]
   let b:= (K).b F
   let f0:= Surface S (R').clip (R').path F t
   obtain ⟨a, B₀,u,h₀⟩:= (K).bounds
   have hs:= Bulk.surface_first S (R').clip (R').path F t h₀ (K).branches b ((K).critical F)
   let r:=fun y:X=> (y,b y)
   have h: r 0=0:= Prod.ext rfl ((K).critical F).1
   have hrb:= ((K).critical F).2.1
   have hr : ContDiffAt ℝ ω r 0:= contDiffAt_id.prodMk hrb
   have hp : Layers.base K F t=f0 ∘ r := rfl
   let w:= classical S F b x
   have hv : fderiv ℝ r 0 x=w:= by
      rw [show fderiv ℝ r 0=_ from ((ContinuousLinearMap.id ℝ X).hasFDerivAt.prodMk ((hrb.differentiableAt (by simp)).hasFDerivAt) : HasFDerivAt r _ 0).fderiv]; rfl
   have hg : bend (Layers.base K F t) 0 x x=bend f0 0 w w := by
      rw [hp,bend_comp_stationary (h.symm ▸ ((K).critical F).2.2 t |>.1) hr (h.symm ▸ hs),LinearMap.compl₁₂_apply,h]
      change bend f0 _ (fderiv ℝ r 0 x) (fderiv ℝ r 0 x)=_; rw [hv]
   unfold infrared Assembly.jet; change _ • iteratedFDeriv ℝ 2 f0 0 (fun _ => w)= _
   rw [show (fun _:Fin 2=> x)=![x,x] by funext i; fin_cases i <;> rfl, show (fun _:Fin 2=>w)=![w,w] by funext i; fin_cases i <;> rfl, ← bend_apply, ← bend_apply, hg]

variable (W : Colors R G (C.S.side (m+1) q)) (hW : W.Standard) (r : ℕ) (hr : 2≤ r)
local notation "Ψ"=>Fk K F t W

def actionResponse (x : fieldDir G (C.S.side m q) 1) : ℝ:= - (Order.Second.lit 2 (logVac (Ψ x r))).re - Assembly.jet (fun x:X=> mainTerm (P').clip (P').path (represent x)) 4 x
include hr hW
lemma slope (n : ℕ) (hn:n≠0): iteratedFDeriv ℝ n (actionResponse L N m q hm F t W r) 0 = if n=2 then iteratedFDeriv ℝ n C' 0 else 0 := by
   let B:= (Order.Second.lit 2 (logVac (Ψ 0 r))).re
   have hu (x:X) := Wick.sq K F t W hW x hr
   have he : actionResponse L N m q hm F t W r = (Assembly.jet C' 2) - fun _=> B:= by
       funext x; unfold actionResponse; rw [hu x]; unfold Layers.forecast; rw [keeps_class L N m q hm F t (2+2) (by omega), Complex.add_re,Complex.neg_re, Complex.ofReal_re]
       change -( - (Assembly.jet Ų 4 x+_)+B)-_= _-_; ring
   have hc:ContDiff ℝ ω (Assembly.jet C' 2) := Tensor.diag_smooth (Tensor.coeff C' 2 0) _
   rw [he,iteratedFDeriv_sub_apply (hc.contDiffAt.of_le le_top) contDiffAt_const, iteratedFDeriv_const_of_ne hn,Pi.zero_apply,sub_zero]; exact re_jet ((retained L N m q hm).born t) n 2

/-- E's wave test on *this same torus*. After subtracting the stationary classical part entirely,
    its measured (pre-reset, order-two logVac) curvature transmits with stated scalar tolerance.
    This does **not** authorize equality on the cover, or payment of any F06/E2 cut cost. -/
theorem sample_kin (i j : Site (C.S.side m q)) (σ τ : TypeFace 1 → G.ColorIndex → ℂ)
      (Hσ : ∀ x y, ‖σ x y‖≤1) (Hτ : ∀ x y, ‖τ x y‖≤1) :
      let Y:= ![Precision.wave i σ, Precision.wave j τ];
       |iteratedFDeriv ℝ 2 (actionResponse L N m q hm F t W r) 0 Y - iteratedFDeriv ℝ 2 (draft α (P').path (P').clip) 0 Y| ≤ (Fintype.card (Site c):ℝ)*L.post.Γ J*C.levels.clock.loopCap (m+1)*Real.exp (-(L.post.c J)*(c).val) := by
   intro w; rw [slope L N m q hm F t W hW r hr 2 (by decide), if_pos rfl]; exact (retained L N m q hm).wave_price t i j σ τ Hσ Hτ
end YM.Comparison.RG02.Thermal
