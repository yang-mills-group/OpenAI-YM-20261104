import YM.LocalLTE.Tol.Dove
import YM.Planned.PRIMARY_INTEGRAL_295.Stain
/-!
# Canonical stencil applied in the spoke engine. Doesn't require polynomial
packing on the local operator component of the prognosed field column.
Pays even at sparse footprints.Measures probes on near-link paths; regular
estimates always use actual supports and P..derivatives.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Port.Sect
open Filter Function Set Lattice Wilson Labels Overlay Marker Source RG Finset Pressure MeasureTheory Push.AbsoluteSums
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Animals FrameBox Grove Cabana
open Work.H03 Next.Foundations ConnectedActivityE6 Blaze Brush
attribute [local instance] Gauge.frobInner
variable {G:Gauge}(t:Finset Lattice.Cover)(A : Formula G t) (n:ℕ)
set_option quotPrecheck false
open Classical
-- Big geometry subpower in mode. Finite calls uniform. Exponent free.
local notation "X"=> Source.Index G t
lemma stroke (P:Side)(u:ℝ→ℝ)(h:Rate G P 0 u) : ∃ f:ℝ→ℝ, Rate G P 0 f∧∀ (r:ℝ)(L:Side)(E:Type)[NormedAddCommGroup E][NormedSpace ℝ E] (U:E→ Config G L)(x:E)(o:Site L), Mode U x n (u r) → Brush n (f r) 1 (fun z=> MvPolynomial.aeval (Source.entry (expandAt o (U z))) A) x:=by
    induction A using MvPolynomial.induction_on with
    | C c => refine ⟨(fun _ => ‖c‖),Rate.const _,fun r L E _ _ U x a h=> ?_⟩; simp_rw [MvPolynomial.aeval_C]; exact Brush.certified zero_le_one _
    | add p q hp hq=> obtain ⟨f,hF,hP⟩:=hp; obtain ⟨g,hG,hQ⟩:=hq; refine ⟨(fun i=>f i+g i),hF.add hG,fun r L E _ _ U x a h=>?_⟩; simp only [map_add]; exact (hP r L E U x a h).gathering (hQ r L E U x a h) -- implicit syntax
    | mul_X p i hp=>
       obtain ⟨f,hf,H⟩:= hp
       let F : G.Mat →ₗ[ℝ] ℂ := { toFun v:=v i.2.1 i.2.2.1,map_add' _ _:= rfl,map_smul' _ _:= rfl }
       let B : G.Mat →L[ℝ] ℂ:= if i.2.2.2 then (starL' ℝ).toContinuousLinearMap.comp F.toContinuousLinearMap else F.toContinuousLinearMap
       obtain ⟨l,hL,hV⟩:∃ l:ℝ, 0≤l∧∀ x, ‖B x‖≤l*‖x‖ := ⟨_,ContinuousLinearMap.opNorm_nonneg B,B.le_opNorm⟩
       let V r:=(f r*(l*royalty G))*(1+(1+u r))^n
       have he :=Rate.mul (hf.mul_right (l*(royalty G))) (((Rate.const 1).add ((Rate.const 1).add h)).pow n)
       refine ⟨V,(by simpa only [zero_mul,zero_add] using! he),fun r L E _ _ U x o hm=>?_⟩
       have hv:= H r L E U x o hm; simp_rw [map_mul,MvPolynomial.aeval_X]
       let g(z:E):= (Source.entry (expandAt o (U z)) i); let t(z:E):= G.mat (U z (wrap L i.1.val.1+o, i.1.val.2))
       have ht : Brush n (l* royalty G) (u r) g x:=by
           have hh:g=B ∘ t:=by unfold B; split <;> rename_i h <;> funext j <;> simp only [g,t, Source.entry,h] <;> split <;> first | rfl | contradiction
           rw [hh]; exact (hm.atLink _).report B (ContinuousLinearMap.opNorm_le_bound _ hL hV)
       exact (hv.paints ht).trim
variable (G) {d:ℕ} (d)
local notation "T"=> localSection G d
local notation "F"=> ((Labels.frames G).level d)
local notation "q"=> (F).Index
lemma soul (P:Side)(u:ℝ→ℝ)(h:Rate G P 0 u) : ∃ f:ℝ→ℝ, Rate G P 0 f∧∀ r:ℝ,0≤f r ∧∀ (L:Side)(E:Type)[NormedAddCommGroup E][NormedSpace ℝ E](U:E→ Config G L)(x:E)(o:Site L),Mode U x n (u r)→∀ k:(F).Coeff, Brush n ((F).coeffSize k*f r) 1 ((localSection G d|>.places k o)∘U) x:=by
   choose f hf hF using fun i:q=> stroke (G:=G) ((T).stencil) ((T).evalC (Extra.Histories.Size.axis (F) i)) n P u h
   let g r:= ∑ i:q,|f i r|; refine ⟨g,?_,fun r=>⟨Finset.sum_nonneg fun i _=> abs_nonneg _, fun L E _ _ U x o hx k=> ?_⟩⟩
   · have hh(v:Finset q):Rate G P 0 (fun r=>∑ i∈v,|f i r|):=by
         induction v using Finset.induction_on with
         | empty=> simp only [sum_empty]; exact Rate.const _
         | insert i v hi ih=> simp only [sum_insert hi]; exact ((hf i).compare (Eventually.of_forall fun r=>(abs_abs _).le)).add ih
     exact hh Finset.univ
   let A (i:q): E→ℂ:= ((T).places (Extra.Histories.Size.axis (F) i) o) ∘ U
   have he i: Brush n (g r) 1 (A i) x:= (hF i r L E U x o hx).climb ((le_abs_self _).trans (single_le_sum (f:=fun i:q=> |f i r|) (fun i _ => abs_nonneg _) (mem_univ _))) le_rfl
   have hK i: Brush n ((‖k i‖*g r)*(1+(0:ℝ)+1)^0) 1 (k i • A i) x:=by
      rw [pow_zero,mul_one]; have hf : Brush n (‖k i‖*g r) ((0:ℝ)+1) (k i • A i) x:=by
         exact (Brush.certified (show 0≤(0:ℝ) from le_rfl) (k i)).paints (he i)
      rwa [zero_add] at hf
   simp only [pow_zero,mul_one] at hK
   have hv:= Brush.spree Finset.univ _ _ zero_le_one fun i _=> hK i
   apply ((hv.climb ?_ le_rfl).shimmy ?_)
   · unfold Frame.coeffSize; rw [Finset.sum_mul]
   apply Eventually.of_forall; intro z; rw [Multi.Maquette.portions]; dsimp only [Function.comp_apply]; rw [Finset.sum_apply]; rfl
variable {n':ℕ}{z t':ℝ}
lemma tuition {a:ℝ} (h:1≤a)(j: (F).Coeff)(hp:d≤n') : (F).coeffSize ((F).scaled a j) ≤ a^n' * (F).coeffSize j:=by
   unfold Frame.coeffSize; rw [Finset.mul_sum]; refine sum_le_sum fun i _=>?_ ; rw [Frame.scaled_apply,norm_mul,Complex.norm_real,Real.norm_of_nonneg (pow_nonneg (zero_le_one.trans h) _)]; exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ h ((Planned.PrimaryIntegral295.Film.second_fits ..).trans hp)) (norm_nonneg _)
-- Envelope through actual horizon included. cite 
lemma kept (P:Side)(u:ℝ→ℝ)(h:Rate G P 0 u)(k:ℕ)(hk:d≤k)(Xi:ℂ→L[ℝ]ℝ) : ∃ f:ℝ→ℝ, Rate G P ((1/2:ℝ)*k) f ∧ ∀ r:ℝ,1≤ (fiery G r P)⁻¹→ ∀ (L:Side)(E:Type)[NormedAddCommGroup E][NormedSpace ℝ E](U:E→ Config G L)(x:E)(o:Site L),Mode U x n (u r)→∀ j:(F).Coeff, Brush n ((F).coeffSize j * f r) 1 (Xi ∘ (Push.Local.presented (T) o (Pressure.fiery G r P) j) ∘ U) x:=by
    obtain ⟨f,hF,hV⟩:= soul G n d P u h -- order
    let v t:= ‖Xi‖*((fiery G t P)⁻¹)^k*f t
    refine ⟨v,?_,fun r hr L E _ _ U x a hu j=>?_⟩
    · simpa only [add_zero] using! ((((inverse_mist G P).pow k).mul_left ‖Xi‖).mul hF)
    have hL:=((hV r).2 L E U x a hu ((F).scaled (fiery G r P)⁻¹ j)).report Xi le_rfl
    apply hL.climb _ le_rfl; apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (tuition G d hr _ hk) ((hV r).1)) (norm_nonneg _)); unfold v; apply le_of_eq; ring
end YM.LocalLTE.Port.Sect
