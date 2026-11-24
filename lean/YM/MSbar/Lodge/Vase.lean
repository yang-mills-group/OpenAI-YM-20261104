import YM.MSbar.Lodge.Shore
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
open MeasureTheory
local notation "S"=> Metric.closedBall (0:Positions σ) w
structure Vase (F:Positions σ→ℝ)(k:ℕ)(B w:ℝ): Prop where
    pos_ :0 ≤ B
    smooth x:x∈Metric.closedBall 0 w → ContDiffAt ℝ k F x
    part x : x∈Metric.closedBall 0 w →∀ l:List σ,l.length ≤ k → l≠[]→|buoy F x l| ≤ B
lemma cs {l:σ→Site n}(h:∀ i<k, JetTab l a p w (Metric.closedBall 0 w) F i C)(hs :∀ v∈S,ContDiffAt ℝ k F v)(hx:1≤ w)(hv:0 ≤ a)(hk:0<k): Vase F k C w:=by
    have hp:0≤ C:= (h _ hk).1; have hw:0<w:=zero_lt_one.trans_le hx; refine ⟨hp,hs,fun x hx₀ L hl ht=>?_⟩; cases L with
    | nil=> exact False.elim (ht rfl)
    | cons i L=>
       let f(t:List σ):= |buoy F x (i::t)| *swipe l a p (i::t); have hg:=JetTab.count (h L.length (by simp only [List.length_cons] at *; omega)) hw x hx₀ i; exact (le_mul_of_one_le_right (abs_nonneg _) (w_start hv _ _)).trans ((lit L f (fun i=> mul_nonneg (abs_nonneg _) (effect ..|>.le))).trans (hg.trans (div_le_self hp (one_le_pow₀ hx))))
variable {f:ℝ→ℝ}(h:Hat k w V f)(hs:Vase F k B w)(W: M→ Positions σ) (hW:Measurable W)(x: Positions ι) (hv:0≤ w)(hu:1≤V)
local notation "b₁"=> Clamp f
local notation "Z"=> F ∘ Clamp f
include h hs hv hu
lemma wax : Curb k (F ∘ Clamp f)∧ContDiff ℝ (k:ℕ) (F ∘ Clamp f):=by
    have hx(x:Π):ContDiffAt ℝ k F (b₁ x):= hs.smooth _ (peak h hv x)
    refine ⟨⟨fun l hl=>?_⟩,contDiff_iff_contDiffAt.mpr fun x=> (hx x).comp x (hut h).contDiffAt⟩; cases l with
    | nil=>
       obtain ⟨C,hC⟩:= ((isCompact_closedBall (0:Π) w).image_of_continuousOn (fun x hx=> ((hs.smooth x hx).continuousAt.abs).continuousWithinAt : ContinuousOn (fun x=>|F x|) S)).bddAbove; exact ⟨C,fun t=>hC ⟨_,peak h hv t,rfl⟩⟩
    | cons a l=>refine ⟨expense l.length V*B,fun x=> work h hu hx x a l rfl hl (fun l hp hk=> hs.part _ (peak h hv x) _ hk hp) hs.pos_⟩
omit hu
include hW
noncomputable def pearl (F:Positions σ→ℝ)(A:M→Positions σ)(t:List σ)(μ:Measure M):=∫ x,buoy F (A x) t ∂μ
local notation "Y"=> (fun v:M=> W v+P x)
lemma lake (l:List σ)(he:l.length≤k) : Integrable (fun y:M=> buoy F (Clamp f (W y+P x)) l) μ:=by
    let T:= b₁ ∘ Y; let Z':= roc F (l.map (@bolt σ)); have hF':ContinuousOn Z' S :=fun x hx=> ((Lis.smooth k 0 _ (hs.smooth x hx) (by simpa using he)).continuousAt.continuousWithinAt)
    have hK: MapsTo T Set.univ S:=fun v _=> peak h hv _; have hh:Measurable T:=((hut h).continuous.measurable.comp (hW.add measurable_const)); obtain ⟨c,hc⟩:=((isCompact_closedBall ..).image_of_continuousOn hF'.norm).bddAbove; refine Integrable.of_bound ?_ c (ae_of_all _ (fun i=> hc ⟨_, hK (Set.mem_univ i),rfl⟩)); let H: M→S:=fun i=> ⟨T i,hK (Set.mem_univ _)⟩; exact ((hF'.restrict|>.measurable).comp (show Measurable H from Measurable.subtype_mk hh ..)).aestronglyMeasurable
variable (hp:∀ A:σ, μ.real {i:M|w/2≤|W i A + (P x) A|} ≤ ε)
noncomputable def boltω(m:ℕ) (ε V B:ℝ) := ((m:ℝ)+1)*ε*(B+expense m V*B)
include hp hu
local notation "Y'"=> Y
lemma price_diff (i:σ)(l:List σ)(hh:l.length+1≤k):
    |(∫ y,buoy (F ∘ Clamp f) (W y+P x) (i::l) ∂μ)- pearl F (Clamp f ∘ (fun i:M=> W i+P x)) (i::l) μ|≤ boltω l.length ε V B:=by
    let L:= i::l; let U(j):={y:M|w/2≤|Y y j|}; let V':=∑ j∈L.toFinset,μ.real (U j); let Ω:=⋃ j∈ L.toFinset,U j
    have hu':Measurable Y:=hW.add measurable_const; have hU(j:σ) : MeasurableSet (U j):= measurableSet_le measurable_const ((measurable_pi_apply j|>.comp hu').abs); have hΩ:MeasurableSet Ω:=L.toFinset.measurableSet_biUnion (fun i _=>hU i)
    let X(y:M):= buoy Z (Y y) L; let E(y:M):= buoy F (b₁ (Y y)) L; have hX: Integrable X μ:= issue ((wax h hs hv hu).2) P W hW (hp:=wax h hs hv hu|>.1) _ x (by simp [L,hh]) -- map ℓ
    have hE : Integrable E μ:=lake P h hs W hW x hv L hh
    let c:=expense l.length V*B; let K:=Set.indicator Ω (fun _ => (B+c))
    have hr(y) : |X y - E y|≤ K y:=by
          by_cases hz : y∈Ω; swap
          · have hw:∀ j∈L,|Y y j|< w/2:=fun j hj=>lt_of_not_ge (fun h=>hz ((Set.mem_iUnion.mpr ⟨_,Set.mem_iUnion.mpr ⟨List.mem_toFinset.mpr hj,h⟩⟩)))
            rw [show X y=E y from paint_eq h (fun x=> hs.smooth _ (peak h hv x)) (Y y) i l hh hw,sub_self,abs_zero]; exact (Set.indicator_of_notMem hz ..).symm.le
          rw [show K y=B+c from Set.indicator_of_mem hz _]; apply (abs_sub ..).trans; refine (add_le_add (b:=c) ?_ ?_).trans_eq (add_comm c B); · exact work h hu (fun x=>hs.smooth _ (peak h hv x)) _ i l rfl hh (fun l hp hk'=> hs.part _ (peak h hv _) _ hk' hp) hs.pos_
          exact hs.part _ (peak h hv _) L hh (by simp [L])
    unfold pearl boltω; change |(∫ y,X y∂μ)-(∫ y,E y∂μ)| ≤ _; rw [←integral_sub hX hE]; refine (norm_integral_le_integral_norm _).trans ((integral_mono (hX.sub hE |>.norm) ((integrable_const _).indicator hΩ) hr).trans ?_); rw [integral_indicator hΩ, setIntegral_const,smul_eq_mul]
    have hk: V'≤ ((l.length:ℝ)+1)* ε:=(Finset.sum_le_sum (fun j _=> hp j)).trans (by rw [sum_const,nsmul_eq_mul]; have hp:0 ≤ ε:= measureReal_nonneg.trans (hp i); exact mul_le_mul_of_nonneg_right (by exact_mod_cast L.toFinset_card_le) hp)
    apply mul_le_mul_of_nonneg_right (le_trans _ hk) (add_nonneg hs.pos_ (mul_nonneg ?_ hs.pos_)); · exact show μ.real (⋃ j∈L.toFinset,U j) ≤ V' from measureReal_biUnion_finset_le _ _
    have hv:=zero_lt_one.trans_le hu; unfold expense; positivity
end YM.MSbar.Lodge
