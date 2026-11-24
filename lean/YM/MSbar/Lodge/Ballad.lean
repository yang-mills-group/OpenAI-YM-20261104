import YM.MSbar.Lodge.Vase
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Lodge
open Function Filter Whisk Lis Measuring Cacao Aqua RawP Push Uniform Lattice RG
open Precision Gauge Midpoint Rolling Exterior Wilson Wave Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {σ ι M:Type}[Fintype σ]
variable {σ ι M:Type}[Fintype σ][Fintype ι][MeasurableSpace M]{μ:MeasureTheory.Measure M}[MeasureTheory.IsProbabilityMeasure μ]
open MeasureTheory Set Metric
local notation "Π"=>Positions σ
local notation "Λ"=>Positions ι
variable {k p s:ℕ}{a c C w B V ε:ℝ}{n:Side}{F:Positions σ→ℝ}(P:Positions ι→L[ℝ]Positions σ)
variable {m:ℕ}{D:ℝ}
variable {f:ℝ→ℝ}(h:Hat k w V f)(hs:Vase F k B w)(W: M→ Positions σ) (hW:Measurable W)(x: Positions ι) (hv:0≤ w)(hu:1≤V)
local notation "Z"=> F ∘ Clamp f
local notation "Y"=> (fun v:M=> W v+P x)
noncomputable def ballad (P:Positions ι→L[ℝ]Positions σ) (μ:Measure M) (f:ℝ→ℝ)(F:Positions σ→ℝ)(W:M→ Positions σ)(x:Positions ι)(L:List ι) := shaft L.length (fun j i=> P (bolt i) j) (fun l=> pearl F (Clamp f ∘ (fun i:M=> W i+P x)) l μ) L
-- need different Pbar when static. generalized
noncomputable def waltz (P:Positions ι→L[ℝ]Positions σ)(μ:Measure M)(F:Positions σ→ℝ)(Θ:M→Positions σ) (L:List ι) := shaft L.length (fun j i=> P (bolt i) j) (fun l=> pearl F Θ l μ) L
lemma moss (g:Λ →L[ℝ]Π)(y:Π)(L:List ι)(hq:ContDiffAt ℝ k F y)(hL:L.length≤ k) : roc F ((L.map (@bolt ι)).map g) y = shaft L.length (fun j i=>g (bolt i) j) (buoy F y) L:=by
    let H(v:Π):=F (y+v); have he:ContDiffAt ℝ k H 0:= ((show ContDiffAt ℝ k F (y+(0:Π)) from (add_zero y|>.symm ▸ hq)).comp (f:=fun x:Π=> y+x) 0 (contDiffAt_const.add contDiffAt_id)); have hp (l:List Π)(hp:l.length≤k): roc H l 0=roc F l y:=by rw [rod _ _ _ he hp, rod _ _ _ hq hp]; unfold H; rw [iteratedFDeriv_comp_add_left,add_zero]; -- shim
    have hy: ContDiffAt ℝ k H (g 0):= by rw [map_zero]; exact he
    rw [← hp _ (by simpa only [List.length_map]), ← map_zero g, ← toe g k (L.map (@bolt ι)) hy (by simpa only [List.length_map]),show roc _ _ _= buoy (H∘g) 0 L from rfl, Lis.paint H g L 0 k hy hL,map_zero]; unfold shaft; refine stitch _ fun t hh=> ?_; unfold buoy; rw [hp _ (by rw [List.length_map,hh]; exact hL)]
lemma castled (f:List σ→M→ℝ)(hp:∀ l:List σ,l.length=k→Integrable (f l) μ): Integrable (fun y=>Yarn k (fun l:List σ=> f l y)) μ∧(∫ x,Yarn k (fun l:List σ=>f l x)∂μ)= Yarn k (fun l:List σ=> ∫ x,f l x∂μ):=by
    induction k generalizing f with |zero=>exact ⟨hp [] rfl,rfl⟩|succ k ih=>
          simp_rw [twilled]; have ht(j:σ):= ih (fun l=> f (j::l)) (fun v he=>hp _ (by rw [List.length_cons,he])); refine ⟨integrable_finsetSum _ (fun i _=>ht i|>.1),?_⟩; rw [integral_finsetSum _ (fun i _=> ht i |>.1)]; exact Finset.sum_congr rfl (fun i _=>ht i|>.2)
include h hs hv hu hW
variable (L:List ι)(hk:L.length≤ k)
include hk
lemma cloth : buoy (shore μ P W (F ∘ Clamp f)) x L= waltz P μ Z Y L:=by
    unfold buoy; have hy:= wax h hs hv hu; rw [capsule hy.2 P W hW x hy.1 _ (by simpa only [List.length_map])]; simp_rw [fun y=> moss P y L (hy.2.contDiffAt (x:=y)) hk]; unfold shaft waltz; unfold shaft; let A:= fun l:List σ=> beads (fun j i=> P (bolt i) j) l L; let E(l:List σ)(y:M):= buoy Z (Y y) l*A l
    have hp(l:List σ)(he:l.length=L.length): Integrable (E l) μ:=Integrable.mul_const (issue hy.2 P W hW hy.1 _ x (by rw [List.length_map,he]; exact hk)) _ -- ambiguous
    rw [show (∫ z,Yarn L.length _ ∂μ) = _ from (castled E hp).2]; refine stitch _ fun T _=> ?_; unfold E pearl; rw [integral_mul_const]
variable (i:ι)(hL:L.length+1≤k)(hp:∀ A:σ, μ.real {i:M|w/2≤|W i A + (P x) A|} ≤ ε)(hD:∀ i:ι,∑ v:σ, |P (bolt i) v| ≤ D)(hd:0≤D)
omit hk
include hp hL hD hd
local notation "C'"=> boltω L.length ε V B
lemma rates (hg:0≤ ε): |buoy (shore μ P W (F ∘ Clamp f)) x (i::L)-waltz P μ F (Clamp f ∘Y) (i::L)|≤ boltω L.length ε V B*D^(L.length+1):=by
     rw [cloth P h hs W hW x hv hu (i::L) hL]; let A:= i::L; let G(j:σ)(v:ι):= P (bolt v) j; let s₀ (l):= beads G l A
     have hm:Yarn A.length (fun l:List σ=> |s₀ l|)≤ D^A.length:=by
          refine le_trans (le_of_eq (b:=Yarn A.length (beads (fun i v=> |G v i|) A)) ?_) (bolt_bound _ (fun i j=> abs_nonneg _) _ _ hd (fun i _=> hD i)); refine stitch _ fun t ht=> ?_; unfold s₀; have hx(L:List ι)(T: List σ)(h':T.length=L.length) : |beads G T L|=beads (fun i v=> |G v i|) L T:=by
               induction L generalizing T with | nil=> rw [show T=[] from (by simpa using h')]; simp [beads] | cons v L ih=> cases T with | nil=>simp at h' | cons w T=> rw [beads,beads, abs_mul, ih T (by simpa only [List.length_cons,Nat.add_right_cancel_iff] using h')]
          exact hx _ _ ht
     let B₁(l:List σ):= pearl F (Clamp f ∘Y) l μ; let g'(l:List σ):= (∫ y,buoy Z (Y y) l∂μ); let E(l:List σ):= g' l-B₁ l
     have he(l:List σ)(hh:l.length=A.length):|E l| ≤ C':=by
         cases l with
         | nil=>simp [A] at hh
         | cons j l=> rw [← show l.length=L.length from (by simpa only [A,List.length_cons,Nat.add_right_cancel_iff] using hh)]; exact price_diff P h hs W hW x hv hu hp j l (by unfold A at hh; rw [List.length_cons,List.length_cons] at hh; omega)
     have hE:0 ≤ C':=by unfold boltω expense; have ht:=hs.pos_; have hp:=zero_lt_one.trans_le hu; positivity
     unfold waltz shaft; rw [show Yarn _ _-Yarn _ _=Yarn A.length (fun l:List σ=> E l*s₀ l) from ?_]; swap
     · apply sub_eq_iff_eq_add.mpr; rw [← Whisk.pockets]; refine stitch _ fun i hi=> ?_; unfold E s₀ B₁ g' G pearl; unfold A; ring
     apply (polished ..).trans; refine le_trans ?_ (mul_le_mul_of_nonneg_left hm hE); rw [← sheen]; refine shiny _ fun l ht=>?_ ; rw [abs_mul]; exact mul_le_mul_of_nonneg_right (he _ ht) (abs_nonneg _)
end YM.MSbar.Lodge
