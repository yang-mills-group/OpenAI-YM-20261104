import YM.LocalLTE.Tol.Violet
/-!
# Real calibrated cylinder supplies. Hold section stencils including cover placement. All LABEL directions in calibrated canonical finite requests.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Port.Sect
open Filter Function Set Lattice Wilson Labels Overlay Marker Source RG Finset Pressure MeasureTheory Push.AbsoluteSums
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Animals FrameBox Grove Cabana
open Work.H03 Next.Foundations ConnectedActivityE6 Blaze Brush
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{d k:ℕ}
set_option quotPrecheck false
local notation "L"=> localSection G d
local notation "F"=> ((Labels.frames G).level d)
variable (G d k) {n:Side} (x:Site n)(A:Grove x) (b:ℕ)(κ:ℝ) (f:((Labels.frames G).level d).Coeff)
open Extra.Histories
local notation "X"=> (F).Index
local notation "wℓ"=> (L).places f x
local notation "rℓ" i=> (L).places (Size.axis F i) x
local notation "T"=> yews G d k x b κ
abbrev argL := ∑ i:X,f i • T i A
local notation "u"=> (argL G d k x A b κ f)
local notation "S"=> (neighbors (b+1) x)
variable {r h:ℝ}
open AnalyticBridge.VerifiedReset.Collection.Price
-- use for projection.P.token.All χ. effective C.Div.Work.
lemma goods (p:Bool)(z:ℕ)(hz:k≤z+1) : Replicated A b κ (z+1) (Port.scaleQ p ∘ u):=by
    have ht (s:Finset X): Replicated A b κ (z+1) (Port.scaleQ p ∘ ∑ i∈s,f i • T i A):=by
       induction s using Finset.induction_on with
       | empty=> simp only [Finset.sum_empty]; rw [show scaleQ p ∘ (0:Config G n→ℂ)= (0: Config G n→ℝ) from funext fun i=>map_zero (scaleQ p)]; exact rp_zero _
       | insert i s hi ih=>
          rw [sum_insert hi]; change Replicated _ _ _ _ (Port.scaleQ p ∘ (_ +_ : Config G n→ℂ))
          rw [show Port.scaleQ p ∘ (f i • T i A+ ∑ j∈s, f j • T j A)=(scaleQ p ∘ (f i • T i A))+(scaleQ p ∘ ∑ j∈s, f j • T j A) from ?_]
          · exact rp_add _ (huesMoved _ _ _ _ _ _ _ _ _ _ _ hz) ih
          exact funext fun j=>map_add (Port.scaleQ p) (f i*T i A j) ((∑ j∈s,f j • T j A) j) -- π.L.Sides
    exact ht Finset.univ
variable (P:BudgetPoint) (e y:ℝ)
lemma sway(h:∀ i:X,P.Regular S (rℓ i) ∧ P.supBounds x S (rℓ i) e ∧ P.Regular S (T i A) ∧ P.supBounds x S (T i A) (e+y)∧ P.Regular S ((rℓ i)-T i A) ∧ P.supBounds x S ((rℓ i)-T i A) y) : P.Regular S wℓ ∧ P.supBounds x S wℓ ((F).coeffSize f* e) ∧ P.Regular S u ∧ P.supBounds x S u ((F).coeffSize f*(e+y))∧ P.Regular S (wℓ-u) ∧ P.supBounds x S (wℓ-u) ((F).coeffSize f*y) :=by
    let m:= (F).coeffSize f; let Φ(v: X→ Config G n →ℂ): Config G n→ℂ:=∑ i,f i • v i
    have hv(v: X→ Config G n →ℂ)(g:ℝ) (h:∀ i:X, P.Regular S (v i) ∧ P.supBounds x S (v i) g): P.Regular S (Φ v)∧ P.supBounds x S (Φ v) (m*g):=by
         have hf:= regular_bound_sum Finset.univ (fun i=> f i • v i) (fun i=> ‖f i‖ *g) (fun i _ => ⟨regular_smul _ (h i).1,bound_smul _ (h i).2⟩)
         unfold Φ m Labels.Frame.coeffSize; rw [sum_mul]; exact hf
    let F0(i:X):=rℓ i; let f' i:=T i A; have h0:wℓ=Φ F0:= YM.Multi.Maquette.portions ..
    obtain ⟨ha,hD⟩:= hv F0 e (fun i=> ⟨(h i).1,(h i).2.1⟩)
    obtain ⟨hu,hE⟩:= hv f' (e+y) (fun i=>⟨(h i).2.2.1,(h i).2.2.2.1⟩)
    rw [h0]; refine ⟨ha,hD,hu,hE,?_⟩
    change P.Regular S (Φ F0-Φ f') ∧ P.supBounds x S (Φ F0-Φ f') (m*y); rw [show Φ F0 - Φ f'= Φ (F0-f') from (by unfold Φ; rw [← Finset.sum_sub_distrib]; simp only [Pi.sub_apply,smul_sub])]
    exact hv (F0-f') y (fun i=> (h i).2.2.2.2)
lemma heft(q:ℝ)(h:(F).coeffSize f≤q)(hp:∀ i:X,∀ V,‖(rℓ i) V‖ ≤ e) : ∀ V,‖wℓ V‖ ≤ q*e:=by
    intro V; rw [Multi.Maquette.portions,Finset.sum_apply]; refine (norm_sum_le ..).trans (le_trans ?_ (mul_le_mul_of_nonneg_right h (show 0 ≤ e from ((norm_nonneg _).trans (hp 0 V)))))
    unfold Frame.coeffSize; rw [sum_mul]; refine sum_le_sum fun i _=>?_; rw [Pi.smul_apply,norm_smul]; exact mul_le_mul_of_nonneg_left (hp _ V) (norm_nonneg _)
end YM.LocalLTE.Port.Sect
