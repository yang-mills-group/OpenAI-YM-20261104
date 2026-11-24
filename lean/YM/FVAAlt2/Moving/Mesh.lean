import YM.PertExtension.MeshIntegral
/-!
# Generalize `PertExtension/MeshIntegral` to the arbitrary spacing & large lattice periods
 of our expanding schedules. Also give discrepancy power estimates after comparing at the pinned
 mesh using genuine shared field/tag routes. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.MeshT
open Set Function Filter MeasureTheory Topology Lattice Extraction
open scoped Topology ENNReal NNReal BigOperators Classical Pointwise
variable {n:ℕ} {l:ℝ} {P:Side} (hl:0<l)
abbrev offsets (P:Side)(n:ℕ):= Fin n→Lattice.Site P
def scenes (l:ℝ) (x:offsets P n): Points n:= Extraction.tag l (Lattice.lift ∘ x)
def tile (l:ℝ)(x:offsets P n): Set (Points n):= Extraction.segment l (Lattice.lift∘ x)
def pin (l:ℝ) (x:Points n) (P:Side): offsets P n:= wrap _∘ Extraction.address l x
lemma pin_of {x:offsets P n}{p:Points n}(h:p∈ tile l x) : pin l p P=x:= by
 change Extraction.address _ _= _ at h; exact funext fun i=>by change wrap _ (Extraction.address _ _ _)=_; rw [h, Function.comp_apply, Lattice.wrap_lift (x i)]
include hl
lemma sense (x:offsets P n):MeasurableSet (tile l x):= Extraction.measurable_segment hl _
lemma pay (x:offsets P n): volume (tile l x)= ENNReal.ofReal ( l^(4*n) ):= Extraction.cell_volume hl _
lemma charge(x:offsets P n):volume.real (tile l x)=l^(4*n):=by unfold Measure.real; rw [pay hl, ENNReal.toReal_ofReal (by positivity)]
lemma price{x:offsets P n} {p:Points n}(hp:p∈ tile l x): dist (scenes l x) p≤ 4*n*l:=by have h:=Extraction.approximate hl p; change Extraction.address _ _= _ at hp; rw [hp] at h; exact h
omit hl
section Family
variable {X:Type}{e:X→ℝ}{A:X→Side}{R:Filter X}
structure Invoices (e:X→ℝ)(A:X→Side)(R:Filter X): Prop where
    pos (i:X): 0<e i
    scope : Tendsto e R (𝓝 0)
    local_r : Tendsto (fun i:X=> e i *((A i).val:ℝ)) R atTop
lemma Invoices.includes (f:Invoices e A R)(x:Points n): ∀ᶠ i in R,x∈ tile (e i) (pin (e i) x (A i)):=by
 let a (p:X) := Extraction.address (e p) x
 have hh (i:Fin n)(j:Axis): ∀ᶠ p in R, -((A p).val:ℤ)<2*a p i j∧2*a p i j≤ ((A p).val:ℤ):=by
    let u(p:X):= a p i j; have ht(p:X): |(u p:ℝ)|≤ (|x i j|+ e p)/e p:=by
       apply (le_div_iff₀ (f.pos p)).mpr
       have hx:= abs_add_le ( e p* (u p)-x i j ) (x i j)
       rw [sub_add_cancel] at hx; have he:= coord_grid_bound (n:=n) (f.pos p) x i j
       rw [abs_mul,abs_of_pos (f.pos p)] at hx; change |e p*(u p:ℝ)-x i j| ≤ _ at he; nlinarith
    filter_upwards [f.local_r.eventually (eventually_gt_atTop (4*(|x i j|+1))), f.scope.eventually (gt_mem_nhds (show (0:ℝ)<1 from zero_lt_one))] with w he hs
    have hv: |u w| * 3 < (A w).val:=(by
       have hh : |(u w:ℝ)| * 3 <( (A w).val:ℝ ):= by have hh0:= (le_div_iff₀ (f.pos w)).mp (ht w); have hz:0<e w:= f.pos w; change e w* _> _ at he; change e w<1 at hs; nlinarith [abs_nonneg (x i j)]
       rw [← Int.cast_abs] at hh; exact_mod_cast hh)
    have hb:= le_abs_self (u w); have hB:= neg_le_abs (u w); exact (by omega : - ((A w).val:ℤ)<2*u w ∧ 2*u w ≤ ((A w).val:ℤ))
 filter_upwards [eventually_all.mpr fun i=>eventually_all.mpr ( hh i )] with w hw
 change a w=_; funext i; exact Eq.symm (lift_eq_iff.mpr ⟨rfl,hw i⟩)
lemma Invoices.campaign (f:Invoices e A R) (x:Points n): Tendsto (fun i=>scenes (e i) (pin (e i) x (A i))) R (𝓝 x):= by
 rw [ tendsto_iff_dist_tendsto_zero ]; refine squeeze_zero' (Eventually.of_forall fun k=>dist_nonneg) ( ( f.includes x ).mono fun k hk=> price (f.pos k) hk ) ?_; simpa only [mul_zero] using! f.scope.const_mul (4*n:ℝ)
end Family
def stepper (l:ℝ)(f:offsets P n→ℝ)(p:Points n):ℝ:=∑ i: offsets P n,(tile l i).indicator (fun _=> f i) p
lemma stow {v:offsets P n}{x:Points n}{f:offsets P n→ℝ}(h:x∈ tile l v): stepper l f x=f v:= by
 unfold stepper; rw [ Finset.sum_eq_single_of_mem v (Finset.mem_univ _) ?_, indicator_of_mem h ]; intro i _ hi; exact indicator_of_notMem (fun hx=> hi ((pin_of hx).symm.trans (pin_of h))) _
lemma lease {x:Points n}{f: offsets P n→ℝ} (h:∀ v:offsets P n,x∉tile l v): stepper l f x=0:= Finset.sum_eq_zero fun i _=> indicator_of_notMem (h i) _
include hl
lemma ready {v:offsets P n}{a:ℝ}: Integrable ((tile l v).indicator (fun _=>a)):= IntegrableOn.integrable_indicator (integrableOn_const ( by rw [pay hl]; exact ENNReal.ofReal_ne_top )) (sense hl _)
lemma charged (f:offsets P n→ℝ): Integrable (stepper l f):= integrable_finsetSum _ fun _ _=>ready hl
lemma area (f:offsets P n→ℝ): (∫ x:Points n,stepper l f x)= l^(4*n)*∑ i,f i:= by
 unfold stepper; rw [MeasureTheory.integral_finsetSum _ (fun _ _=>ready hl),Finset.mul_sum]; exact Finset.sum_congr rfl fun i _=> by rw [MeasureTheory.integral_indicator (sense hl i),MeasureTheory.setIntegral_const, charge hl]; rfl
omit hl
section Limits
variable {X:Type}{v:X→ℝ}{A:X→Side} {K:Set (Points n)}{F: (i:X)→ offsets (A i) n→ℝ}{H:Points n→ℝ}{R:Filter X}{f: (x:Points n)→ℝ} (Γ: Invoices v A R)(h: IsCompact K) (ht: support H⊆ K) (hp:∀ i x, scenes (v i) x∉ K→ F i x=0)
variable (hC:∃ C:ℝ, 0≤C ∧ ∀ᶠ i in R,∀ x:offsets (A i) n, scenes (v i) x∈ K→|F i x|≤C)
variable (hh:∀ x∈K,Tendsto (fun i=> F i (pin (v i) x (A i))) R (𝓝 ( H x )))
include Γ h ht hp hh hC
lemma road [R.NeBot] [R.IsCountablyGenerated] : Integrable H ∧ Tendsto (fun i=> v i^(4*n)*∑ x,F i x) R (𝓝 (∫ x:Points n,H x)):=by
 obtain ⟨C,hD,hC⟩:=hC; obtain ⟨D,hK⟩:=h.isBounded.subset_closedBall (0:Points n)
 let S(i:X):=stepper (v i) (F i); have hF(i:X):Integrable (S i):= charged (Γ.pos i) _
 let L:= Metric.closedBall (0:Points n) (D+1); have hL:IsCompact L:= by unfold L; exact isCompact_closedBall ..
 let U:=L.indicator (fun _=> C); have hv:Integrable U:=(integrableOn_const hL.measure_ne_top).integrable_indicator hL.measurableSet
 have hR : Tendsto (fun i=>(4*n:ℝ)*v i) R (𝓝 0):= by simpa only [mul_zero] using! Γ.scope.const_mul (4*n:ℝ)
 have he:∀ᶠ w in R, ∀ x:Points n, ‖S w x‖ ≤ U x:= by
    filter_upwards [hC,hR.eventually (gt_mem_nhds (show (0:ℝ)<1 from zero_lt_one))] with w hw hk x; have hy:0≤ U x:=indicator_nonneg (fun y _=>hD) _
    by_cases h':∃ i:offsets (A w) n,x∈tile (v w) i
    · obtain ⟨i,hi⟩:=h'; rw [show S w x=F w i from stow hi]; by_cases hx : scenes (v w) i∈ K
      · unfold U; rw [indicator_of_mem (a:=x) ?_]; exact hw _ hx; change dist x 0≤ _; linarith only [show (4*n:ℝ)*v w<1 from hk, (show dist (scenes (v w) i) 0 ≤ D from hK hx), price (Γ.pos w) hi, dist_triangle x (scenes (v w) i) 0, dist_comm x (scenes (v w) i)]
      rw [hp _ _ hx,norm_zero]; exact hy
    rw [show S w x=0 from lease (by simpa using! h'),norm_zero ]; exact hy
 have hm(x:Points n): Tendsto (fun w=>S w x) R (𝓝 (H x)):= by
    by_cases hx:x∈ K
    · exact (hh x hx).congr' ((Γ.includes x).mono (fun i hi=> (stow (f:=F i) hi).symm))
    refine tendsto_const_nhds.congr' ?_; filter_upwards [Γ.includes x,(Γ.campaign x).eventually (h.isClosed.isOpen_compl.mem_nhds hx)] with w hw hV; unfold S; rw [stow hw,hp _ _ hV, Function.notMem_support.mp (fun g=> hx (ht g))]
 constructor
 · refine hv.mono' ( aestronglyMeasurable_of_tendsto_ae (β:=ℝ) R (fun m=> (hF m).aestronglyMeasurable) (Eventually.of_forall hm) ) <| Eventually.of_forall fun x=> le_of_tendsto (hm x).norm (he.mono fun i hi=> hi x)
 simp_rw [ ← fun i=> area (Γ.pos i) (F i) ]; exact tendsto_integral_filter_of_dominated_convergence _ (Eventually.of_forall (fun i=> (hF i).aestronglyMeasurable)) (he.mono fun i hi=>Eventually.of_forall hi) hv (Eventually.of_forall hm)
end Limits
end YM.FVAAlt2.MeshT
