import YM.WilsonCoeffUV.Product.Report.Slots
/-!
# Compact shape footprints
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Soil
open Gauge Power PathCost Precision Embroider Fountain Cosmos Shard Realm
open PowerSeries
open scoped Topology BigOperators
variable {n c:Side}{U V α β:Type*}{r h D j e i l k:ℕ}{A B C s:ℝ}{G:Gauge}
open Embroider
open scoped ContDiff
structure Rarity (D:ℕ) where
   ψ : Phrase D
   radius: ℝ
   markG :1 ≤ radius
   support : tsupport ψ.val ⊆ Metric.closedBall 0 radius

def Amplitude (T:Rarity D)(A:ℝ):Prop:=0≤A∧∀ i≤D,∀ v:Fin i→Axis,∀ x:E, ‖crease T.ψ v x‖≤ A
lemma scenery (p:Phrase D)(h:HasCompactSupport p.val): ∃ T:Rarity D,T.ψ=p:=by
    obtain ⟨C,c⟩:= Metric.isBounded_iff_subset_closedBall (0:E) |>.mp h.isBounded; exact ⟨⟨p,max 1 C,le_max_left ..,c.trans (Metric.closedBall_subset_closedBall (le_max_right ..))⟩,rfl⟩
lemma crestShelter {p:Phrase D}{v:Fin i→Axis}(x:E)(t:crease p v x ≠0): x∈tsupport p.val:= support_iteratedFDeriv_subset (𝕜:=ℝ) i (show x∈ Function.support _ from fun h=> t (show iteratedFDeriv ℝ i p.val x _=0 by rw [h]; rfl))
lemma amplitudes (p: Rarity D):∃ A, Amplitude p A:=by
   let f:=p.ψ
   let T:=tsupport f.val; have hx:IsCompact T:= (ProperSpace.isCompact_closedBall 0 p.radius).of_isClosed_subset isClosed_closure p.support
   have hp (v: Knob D) : ∃ C:ℝ,0≤C ∧∀ x:E,‖crease f v.2 x‖ ≤ C:=by
       let g:=crease f v.2; have he: Continuous g:= continuous_iff_continuousAt.mpr (fun x=> Analysis.iterD (x:=x) (scribble f (Nat.le_of_lt_succ v.1.isLt)).contDiffAt _)
       obtain ⟨C,h⟩:= Metric.isBounded_iff_subset_closedBall (0:ℝ) |>.mp (hx.image he).isBounded
       refine ⟨max 0 C,le_max_left ..,fun x=>?_⟩; by_cases hz:g x=0; · change ‖g x‖≤ _; rw [hz,norm_zero]; exact le_max_left ..
       rw [← dist_zero_right]; exact (Metric.mem_closedBall.mp (h (Set.mem_image_of_mem g (crestShelter x hz)))).trans (le_max_right ..)
   choose A a h using hp; let C:=∑ i,A i; refine ⟨C,Finset.sum_nonneg (fun i _=>a i),fun i b v x=>?_⟩; let V: Knob D:= ⟨⟨i,Nat.lt_succ_of_le b⟩,v⟩; exact (h V x).trans (Finset.single_le_sum (f:=A) (fun i _=> a _) (Finset.mem_univ V))
lemma amplitudes_bound {p:Rarity D} (x y:ℝ)(v:Amplitude p A)(h:0≤x)(hp:x≤1)(o:CellR)(d:Cover): ‖wheelC x y d p.ψ o‖≤ A:= by
    apply pledge (sonal x y o d p.ψ) v.1; intro i hi w j; rw [currentP _ _ _ _ _ _ hi, norm_mul,norm_pow,Real.norm_eq_abs,abs_of_nonneg h]; exact (mul_le_mul_of_nonneg_left (v.2 _ hi w _) (by positivity)).trans (mul_le_of_le_one_left v.1 (pow_le_one₀ h hp))
lemma featureV (p:Rarity D)(x y:ℝ)(o:CellR)(b:Cover)(t:wheelC x y b p.ψ o≠0) : ∃ v:CellR,address x y o b v.val∈tsupport p.ψ.val:=by
   by_contra! h
   apply t; refine norm_le_zero_iff.mp (pledge (sonal x y o b p.ψ) le_rfl (fun i hi s w=> ?_)); rw [currentP x y o b p.ψ s hi, show crease p.ψ _ _= 0 from not_ne_iff.mp (mt (crestShelter (v:=s) _) (h w)),mul_zero,norm_zero]

-- ℓ∞ vs ℓ1
lemma actual_axis (x:Cover)(i): (↑(x i).natAbs:ℝ)=‖actualW x i‖:=by simp [actualW,Real.norm_eq_abs]
lemma norm_actual (x:Cover): ‖actualW x‖≤ size x:= (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun i=> by rw [← actual_axis]; exact_mod_cast Finset.single_le_sum (f:=fun i=>(x i).natAbs) (fun _ _=> Nat.zero_le _) (Finset.mem_univ i))
lemma actual_within (x:Cover): (size x:ℝ)≤4*‖actualW x‖:= by
    unfold size; rw [Nat.cast_sum]; apply (Finset.sum_le_sum (f:=fun i=> ↑(x i).natAbs) (g:=fun _=>‖actualW x‖) (fun i _=> (actual_axis ..) ▸ norm_le_pi_norm _ i)).trans; simp [Axis]
lemma actual_dis (x y:Cover): dist (actualW x) (actualW y)≤ Bank.terrain.gap x y:= by rw [Bank.terrain.swap,dist_eq_norm,←actual_minus]; exact norm_actual _
-- root radius. δ covers origin displacement charge y radius. explicit tested supports permit multiple pull operations. Hull used for independence of center. candidate root independent of x
lemma hall_fit (p:Rarity D)(x y:ℝ)(o:CellR)(b:Cover)(hp:wheelC x y b p.ψ o≠0) : |x| *‖actualW b‖ ≤ p.radius+|y| +|x| :=by
    obtain ⟨w,h⟩:=featureV p x y o b hp; let V:=w.val; let T:= address x y o b w.val; have hx:‖V‖≤1:= (c_norm w).trans (by norm_num)
    rw [← Real.norm_eq_abs, ← norm_smul]; rw [show x • actualW b=T+y • o.val-x • V by unfold T address position V; abel]; refine (norm_sub_le ..).trans (add_le_add ((norm_add_le ..).trans ?_) ?_)
    · refine add_le_add (show ‖T‖≤ p.radius from (dist_zero_right T).symm ▸ p.support h) ?_; rw [norm_smul]; exact mul_le_of_le_one_right (norm_nonneg _) ((c_norm _).trans (by norm_num))
    · rw [norm_smul]; exact mul_le_of_le_one_right (norm_nonneg _) hx

def radiusH (p:Rarity D)(x y:ℝ) :ℝ:= p.radius+|y|+|x|
def cairnM (p:Rarity D)(x y:ℝ):ℕ:= ⌈(radiusH p x y) / |x|⌉₊
-- coordinate box
lemma fieldCap (p:Rarity D)(x y:ℝ): 1≤ radiusH p x y := (p.markG.trans (le_add_of_nonneg_right (abs_nonneg _))).trans (le_add_of_nonneg_right (abs_nonneg _))
def canvasM (p:Rarity D)(x y:ℝ): Finset Cover:= let K:=cairnM p x y; Fintype.piFinset fun _=> Finset.Icc (-(K:ℤ)) (K:ℤ)
lemma contour (p:Rarity D)(x y:ℝ)(o:CellR)(b:Cover)(h:0<x)(v:wheelC x y b p.ψ o≠0): b∈canvasM p x y:=by
    have he:= le_trans ((le_div_iff₀ (abs_pos.mpr h.ne')).mpr (mul_comm ‖actualW b‖ _ ▸ hall_fit p x y o b v)) (Nat.le_ceil (R:=ℝ) (radiusH p x y / |x|)); unfold canvasM; simp only [Fintype.mem_piFinset,Finset.mem_Icc]
    intro i; set K:= cairnM p x y; have hb: (↑(b i):ℝ) ≤ K ∧ -(K:ℝ) ≤ ↑(b i):= And.symm (abs_le.mp (le_trans (norm_le_pi_norm (actualW b) _) he)); constructor
    · exact_mod_cast hb.2
    exact_mod_cast hb.1
lemma canvas_count (p:Rarity D)(x y:ℝ): (canvasM p x y).card=(2*cairnM p x y+1)^4:=by
    unfold canvasM; dsimp only; rw [Fintype.card_piFinset]; simp_rw [Int.card_Icc]; rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin];
    congr 1; omega
lemma census (p:Rarity D)(x y:ℝ)(v:0<x)(h:x ≤ 1): x^4 * (canvasM p x y).card ≤ (5* radiusH p x y)^4:=by
    let K:=cairnM p x y; rw [canvas_count]; push_cast; change x^4*((2*(K:ℝ)+1)^4) ≤ _; rw [←mul_pow]; apply pow_le_pow_left₀ (by positivity); have hx (f:ℝ) (q:0≤f): (⌈f⌉₊:ℝ)≤ f+1:= Nat.ceil_lt_add_one q |>.le
    have hy:= fieldCap p x y; let R:=radiusH p x y; have he:x*(K:ℝ)≤ R+x:= by
       unfold K cairnM; rw [mul_comm,abs_of_pos v]; apply (mul_le_mul_of_nonneg_right (hx (R/x) (by change 0≤ radiusH _ _ _ / x; positivity)) v.le).trans_eq ?_
       field_simp
    change _≤ 5*R; linarith
end YM.WilsonCoeffUV.Mer
