import YM.UVExt.CommonRates

/-! At a fixed cutoff-independent side pair, comparison of normalized derivatives (positive orders) of the stationary determinant and chart correction. No assertion on field-independent free energy, changing slice dimension, complex determinant zeros, or thermodynamic uniformity of these germs. The branch must come from the same stationary test. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths
open Function RG Precision Wilson Lattice Bid Exterior Laurent Filter Set Matrix Tree Tensor
open Work.F03 Work.F04
open scoped Topology ContDiff Classical BigOperators
set_option linter.unusedSectionVars false
variable {ι : Type*} {E B : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B]

def reach [Fintype ι] (e : ι→B) : Prop := Function.Injective (fun x : ι→ℝ => ∑ i:ι,x i • e i)
variable (e : ι→B)

lemma slices_snoc {f : E × B → ℝ} (j : E×B) (h : ContDiffAt ℝ ω f j) (v w : B) :
    (iteratedFDeriv ℝ 2 (fun a=>f (j.1,a)) j.2) ![v,w] = iteratedFDeriv ℝ 2 f j ![(0,v),(0,w)] := by
 let F (y : E×B) := f (j+y)
 let W (y : B) := (ContinuousLinearMap.inr ℝ E B) y
 have hf' : ContDiffAt ℝ 2 F 0 := by
    exact ContDiffAt.comp (f:=fun y=>j+y) 0 (show ContDiffAt ℝ 2 f (j+0) by rw [add_zero]; exact h.of_le (by simp : ↑(2:ℕ) ≤ (ω:ℕ∞ω))) (contDiffAt_const.add contDiffAt_id)
 have ht : iteratedFDeriv ℝ 2 (F ∘ W) (0:B) = iteratedFDeriv ℝ 2 (fun b:B=>f (j.1,b)) j.2 := by
    change iteratedFDeriv ℝ 2 (fun b=>f (j.1+0,j.2+b)) 0 = _
    rw [add_zero,iteratedFDeriv_comp_add_left (f:=fun b=>f (j.1,b)) 2 j.2 0, add_zero]
 have hv' : iteratedFDeriv ℝ 2 F 0 = iteratedFDeriv ℝ 2 f j := by unfold F; rw [iteratedFDeriv_comp_add_left,add_zero]
 calc
   _ = (iteratedFDeriv ℝ 2 (F ∘ W) 0) ![v,w] := by rw [ht]
   _ = _ := by
      rw [show iteratedFDeriv ℝ 2 (F ∘ W) 0 = _ from Next.Foundations.jets_linear _ hf']
      rw [hv']; exact congr_arg (iteratedFDeriv ℝ 2 f j) (show (fun i=>(ContinuousLinearMap.inr ℝ E B) (![v,w] i))= _ from funext (fun i=>by fin_cases i <;> rfl))
private def nearCharge (f : E×B→ℝ) (c t : ι) (p : E×B) := (Analysis.D (0,e c) (Analysis.D (0,e t) f)) p
lemma charged (f : E×B→ℝ) (c t : ι) (p : E×B) (h : ContDiffAt ℝ ω f p) : nearCharge e f c t p=iteratedFDeriv ℝ 2 (fun b:B=>f (p.1,b)) p.2 ![e c,e t] := by
   have he := Analysis.snoc_jet (show ContDiffAt ℝ (↑(1+1:ℕ)) f p from h.of_le (by simp)) (0,e t) (![⟨0,e c⟩] : Fin 1→E×B)
   rw [slices_snoc p h]
   rw [← snoc_one ((0:E),e c) ((0:E),e t), he,iteratedFDeriv_one_apply]; rfl

def shiftedHess (f : E×B→ℝ) (ρ : ℝ→B) (x : E) (z : ℝ) : Matrix ι ι ℝ := Matrix.of fun c d=> iteratedFDeriv ℝ 2 (fun b=> f (z • x,b)) (ρ z) ![e c,e d]
def movingCharge (f : E×B→ℝ) (ρ : ℝ→B) (x : E) (z : ℝ) := Matrix.of fun c d=> nearCharge e f c d (paired x ρ z)
private lemma ready {f : E×B→ℝ} {ρ : ℝ→B} {x : E} (h : Optimizes f x ρ) : movingCharge e f ρ x=ᶠ[𝓝 0] shiftedHess e f ρ x := by
   have he := (pairSmooth x h.analytic_pay).continuousAt.tendsto
   rw [pairAnchored _ _ h.anchor] at he
   exact (he.eventually (h.smooth.eventually (by simp))).mono fun z hz=> funext fun i=>funext fun j=>charged e f i j _ hz

omit e in
lemma Joint.det [Fintype ι] [DecidableEq ι] {f g : ℕ→ℝ→Matrix ι ι ℝ} (h : ∀ i j,Joint 2 (fun n z=> f n z i j) (fun n z=>g n z i j)) : Joint 2 (fun d : ℕ=>Matrix.det ∘ f d) (fun d=> Matrix.det ∘ g d) := by
  classical
  let V (j : ℕ→ℝ→ Matrix ι ι ℝ) (w : Equiv.Perm ι) := ∏ k:ι, (fun n p=>j n p (w k) k)
  let S (w:Equiv.Perm ι) (n:ℕ) (p:ℝ) := ((↑(w.sign):ℤ):ℝ) -- cast units?
  let T₀ j := ∑ w : Equiv.Perm ι, S w * V j w
  have he j : T₀ j = fun d : ℕ=>Matrix.det ∘ j d := by
     funext d p; unfold T₀ V S; dsimp only [Function.comp_apply]
     simp only [Finset.sum_apply, Finset.prod_apply, Pi.mul_apply, Matrix.det_apply']
     -- first maybe closes
  have hS : Joint 2 (T₀ f) (T₀ g) := (Joint.sum _ _ _ fun w _=> (joint_refl (fun _=> ((↑(w.sign):ℤ):ℝ)) contDiffAt_const).mul (Joint.prod Finset.univ (fun k:ι=> (f · · (w k) k)) (fun k=>fun d x=>g d x (w k) k) fun k _=>h (w k) k)) -- expressions f · · elaborates wrong
  rw [←he,←he]; exact hS

section limiting
variable [FiniteDimensional ℝ E] [CompleteSpace E] [FiniteDimensional ℝ B] [CompleteSpace B]
variable {f f' : ℕ→E×B→ℝ} {ρ ρ' : ℕ→ℝ→B} {x : E} (h : ∀ᶠ i in atTop, Optimizes (f i) x (ρ i)) (h' : ∀ᶠ i in atTop, Optimizes (f' i) x (ρ' i))
        (H : Junction f f' 4)

include h h' H
omit H in
lemma responses_joint {c c' : ℝ} (hm : Junction f f' 3) (he : 0<c) (he' : 0 < c') (hl : clampedGap f c) (hl' : clampedGap f' c') :
    ∃ X : ℕ→E×B,∀ j≤2,Tendsto (fun i : ℕ=>fish j (paired x (ρ i))) atTop (𝓝 (X j)) ∧ Tendsto (fun i=>fish j (paired x (ρ' i))) atTop (𝓝 (X j)) := by
   obtain ⟨X,hX,-⟩ := critical_transfer (k:=4) h h' (Or.inr rfl) hm hl he hl' he'
   exact ⟨X,hX⟩

lemma charge_entries {c c' : ℝ} (he : 0<c) (he' : 0 < c') (hl : clampedGap f c) (hl' : clampedGap f' c') (k l : ι) : Joint 2 (fun n p=> movingCharge e (f n) (ρ n) x p k l) (fun n p=> movingCharge e (f' n) (ρ' n) x p k l) := by
   obtain ⟨X,hX⟩ := responses_joint h h' (H.mono (by omega)) he he' hl hl'
   let f0 := (fun n=>nearCharge e (f n) k l); let f1 := fun n=> nearCharge e (f' n) k l
   have H0 : lucid (fun i=> Analysis.D (0,e l) (f i)) := h.mono fun i hi=> (Analysis.dSmooth hi.smooth _ le_top)
   have H0' : lucid (fun i=> Analysis.D (0,e l) (f' i)) := h'.mono fun i hi=> (Analysis.dSmooth hi.smooth _ le_top)
   have ht : lucid f0 := H0.mono fun i h=>Analysis.dSmooth h _ (by simp); have ht' : lucid f1 := H0'.mono fun i h=>Analysis.dSmooth h _ (by simp)
   have hz := (H.direction (q:=3) (0,e l) (h.mono fun i hi=>hi.smooth.of_le le_top) (h'.mono fun i hi=>hi.smooth.of_le le_top)).direction (q:=2) (0,e k) H0 H0'
   let t i := paired x (ρ i); let t' i := paired x (ρ' i)
   have ha : lucid t := h.mono fun i hi=>(pairSmooth x hi.analytic_pay).of_le le_top; have hb : lucid t' := h'.mono fun i hi=>(pairSmooth x hi.analytic_pay).of_le le_top
   have hp : Pinned t := h.mono fun i hi=> pairAnchored _ _ hi.anchor; have hp' : Pinned t' := h'.mono fun i hi=>pairAnchored _ _ hi.anchor
   change Joint 2 (fun i=>f0 i ∘ t i) (fun i=>f1 i ∘ t' i)
   exact ⟨lucid_comp ht ha hp,lucid_comp ht' hb hp',fun i h=>(Junction.track (hz.mono h) ht ht' ha hb hp hp' (fun j hj=>hX j (hj.trans h)))⟩
lemma gram_entry {c c' : ℝ} (he : 0<c) (he' : 0 < c') (hl : clampedGap f c) (hl' : clampedGap f' c') (k l : ι) : Joint 2 (fun n p=> shiftedHess e (f n) (ρ n) x p k l) (fun n p=> shiftedHess e (f' n) (ρ' n) x p k l) :=
    (charge_entries e h h' H he he' hl hl' k l).agrees (h.mono fun u hu=>(ready e hu).mono fun s hs=>by exact congr_arg (fun a=> a k l) hs) (h'.mono fun u hu=>(ready e hu).mono fun s hs=>by exact congr_arg (fun a=>a k l) hs)
variable [Fintype ι] [DecidableEq ι]
omit H h h'
include h h' H
lemma det_rates {c c' : ℝ} (he : 0<c) (he' : 0 < c') (hl : clampedGap f c) (hl' : clampedGap f' c') : Joint 2 (fun i=> Matrix.det ∘ shiftedHess e (f i) (ρ i) x) (fun i=> Matrix.det ∘ shiftedHess e (f' i) (ρ' i) x) := Joint.det (gram_entry e h h' H he he' hl hl')
end limiting
end YM.UVExt.Paths
