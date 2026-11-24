import YM.X.Wrap.Porch
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
/-!
# Porch: decay class on seam-lit neighborhoods. ∑far Tonelli budget.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Crate.Porch
open Lattice Wilson Next.Rank CellsInt Beamer Interval PertExtension LatticePT Normal Filter Set Function Metric MeasureTheory Asymptotics
open Reed Fielding Haze Rays Braid Shelf Print
open scoped Topology BigOperators Classical ENNReal
variable {q:ℕ+}{n:Side} {k l m d:ℕ} {R:ℝ} {I:Type*} {G:Gauge} (hq:1<q.val)
local notation "Fℕ"=>(atTop:Filter ℕ)
local notation "ε"=>epsilon q
variable (S: Finset I) (x:I→ Fielding.Walk) (p:I→E4)(hp:∀ i∈ S, plot q (x i) (p i))(χ:Floor R)
local notation "regL" i => side q i
abbrev Post:=ℕ×Cover
abbrev Lapse:= Post→ℂ
structure Isle (q:ℕ+)(S:Finset I)(x:I→Fielding.Walk)(p:I→E4)(χ:Floor R)(n:ℕ)(f:Lapse): Prop where
    born : ∃ C:ℝ,0≤ C∧ ∀ᶠ k in Fℕ,∀ z:Cover,lift (wrap (side q k) z)=z→Quiet q S x χ k (wrap _ z)≠0→ ‖f (k,z)‖ * Width q k z^n≤C
    path {a:E4}(H:a∉ p '' (S:Set I))(z:Fielding.Walk)(hz:plot q z a) : Released (fun k=> f (k,z k))
namespace Isle
variable {S x p χ}
lemma zero : Isle q S x p χ m 0:=⟨⟨0,le_rfl,by simp⟩,fun _ _ _=> Released.zero⟩
variable {f g:Lapse}
lemma add (h:Isle q S x p χ m f)(hp:Isle q S x p χ m g): Isle q S x p χ m (f+g):= by
    obtain ⟨C,hC,t⟩:=h.born; obtain ⟨D,hD,u⟩:=hp.born; refine ⟨⟨C+D,add_nonneg hC hD,?_⟩,fun a z hz=> (h.path a z hz).add (hp.path a z hz)⟩; filter_upwards [t,u] with i hi hj z h hz; rw [Pi.add_apply]; apply le_trans (mul_le_mul_of_nonneg_right (norm_add_le ..) (pow_nonneg (zero_le_one.trans (depth ..)) m)); rw [add_mul]; exact add_le_add (hi z h hz) (hj z h hz)
lemma mul (h:Isle q S x p χ m f)(hp:Isle q S x p χ l g): Isle q S x p χ (m+l) (f*g):=by
    obtain ⟨C,hC,t⟩:=h.born; obtain ⟨D,hD,u⟩:=hp.born; refine ⟨⟨C*D,mul_nonneg hC hD,?_⟩,fun a z hz=> breaths (h.path a z hz) (hp.path a z hz)⟩; filter_upwards [t,u] with i hi hj z h hz; rw [Pi.mul_apply, norm_mul,pow_add, mul_mul_mul_comm]; apply mul_le_mul (hi z h hz) (hj z h hz) (mul_nonneg (norm_nonneg _) (pow_nonneg (zero_le_one.trans (depth ..)) l)) hC
lemma iota (n:ℕ)(hx:n ≤ m)(h:Isle q S x p χ m f): Isle q S x p χ n f:= by
    obtain ⟨C,hc,h'⟩:= h.born; refine ⟨⟨C,hc,?_⟩,fun a z hz=> h.path a z hz⟩; filter_upwards [h'] with i hi z hp hz; exact le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (depth ..) hx) (norm_nonneg _)) (hi z hp hz)
lemma clock(h:f ∈ token Prod.fst): Isle q S x p χ 0 f:= by
    obtain ⟨c,h,rfl⟩:=h; obtain ⟨C,hc⟩:= h; refine ⟨⟨‖C‖+1,by positivity,?_⟩,fun a z hz=>⟨C,hc⟩⟩; simp only [pow_zero,mul_one]; filter_upwards [hc.norm.eventually (ge_mem_nhds (lt_add_one ‖C‖))] with i hi z hz hh; exact hi
end Isle
def island (q:ℕ+)(S:Finset I)(x:I→ Fielding.Walk)(p:I→E4)(χ:Floor R)(m:ℕ):Submodule ℂ Lapse where
    carrier:= {f|Isle q S x p χ m f}; add_mem':= fun p q=> Isle.add p q; zero_mem':= Isle.zero; smul_mem' z f h:= by
      have hz: Isle q S x p χ 0 (fun _:Post=> z):= Isle.clock (f:= fun _:Post=>z) (rear Prod.fst (fun _:ℕ=> z) (constell _)); -- edit
      exact Nat.zero_add m ▸ hz.mul h
-- one_add_norm^6 ∈ L¹. separate neighborhood all roots. interpret via Post on lift iff and χ. Sum ∶ over periodic hats
abbrev Room (q:ℕ+)(S:Finset I)(x:I→ Fielding.Walk)(χ:Floor R)(f:Lapse)(k:ℕ)(z:Cover):ℂ:= if lift (wrap (side q k) z)=z then Quiet q S x χ k (wrap _ z) • f (k,z) else 0
def paisley (n:Side):Finset Cover:= Finset.univ.image (lift (n:=n)) -- n arg
lemma register (f:Lapse) : Frugal (Room q S x χ f k) (paisley (side q k)):= by
    intro z hz; change Room _ _ _ _ _ _ _≠0 at hz; by_cases hf:lift (wrap (side q k) z)=z; exact Finset.mem_image.mpr ⟨_,Finset.mem_univ _,hf⟩; simp [Room,hf] at hz
lemma cost_origin (z:E4)(w:Cover)(he:index (ε k) z=w): 1+‖z‖≤ 5*Width q k w:= by
    have ht:= voxel_near z (epsilon_pos q k); rw [he,dist_eq_norm,norm_sub_rev] at ht; have hg:= (norm_sub_norm_le z _).trans ht; have he : ε k≤1:= inv_le_one_of_one_le₀ (Interval.cane q k); unfold Width; nlinarith only [hg,he,spot_cost (q:=q) (k:=k) w, mul_nonneg (epsilon_pos q k|>.le) (Nat.cast_nonneg (α:=ℝ) (street w))]
def tipV (w:E4):ℝ:=(1+ ‖w‖)⁻¹^6
lemma tip_integrable : Integrable tipV := by
    have ht:= integrable_one_add_norm (μ:=volume) (E:=E4) (r:=6) (by norm_num [E4]); unfold tipV; apply ht.congr; apply Eventually.of_forall; intro z; change (1+‖z‖)^(-(6:ℝ))=_; rw [Real.rpow_neg (by positivity), show (6:ℝ)= ((6:ℕ):ℝ) from by norm_num,Real.rpow_natCast,← inv_pow]
variable {f:Lapse}
lemma tip_budget (h:Isle q S x p χ 6 f):∃ C:ℝ,C≥0∧∀ᶠ i in Fℕ,∀ z:E4, ‖mosaic (ε i) (Room q S x χ f i) z‖≤ C*tipV z:= by
    obtain ⟨C,hc,he⟩:=h.born; let D:=1+(S.card:ℝ); refine ⟨ D*C*5^6,by unfold D; positivity,?_⟩; filter_upwards [he] with i hi v; let k:= index (ε i) v; let x':= wrap (side q i) k; have ht : 1+‖v‖>0:= by positivity
    have hY: Width q i k>0:= zero_lt_one.trans_le (depth ..); change ‖Room _ _ _ _ _ _ k‖≤_
    by_cases h: lift x'=k; swap; · unfold Room; rw [if_neg h]; unfold tipV D; simp only [norm_zero]; positivity -- abbrev unfold?
    unfold Room; rw [if_pos h]; let a:=Quiet q S x χ i x'; by_cases hx:a=0; · rw [show Quiet _ _ _ _ _ _=0 from hx,zero_smul,norm_zero]; unfold tipV D; positivity
    change ‖a • f (i,k)‖ ≤ D*C*5^6*tipV v; rw [norm_smul,Real.norm_eq_abs]; apply le_trans (mul_le_mul_of_nonneg_right (mildQ S x χ x') (norm_nonneg _));
    have ht' : ‖f (i,k)‖*(1+‖v‖)^6 ≤ C*5^6:= by
       calc _ ≤ ‖f (i,k)‖ *(5*Width q i k)^6:= by gcongr; apply cost_origin v k rfl
            _ = ‖f (i,k)‖*Width q i k^6*5^6:= by ring
            _ ≤ _ := by gcongr; exact hi k h hx
    unfold tipV; rw [inv_pow, ← div_eq_mul_inv]; apply (le_div_iff₀ (pow_pos ht _)).2; change D*_ * _≤_; rw [mul_assoc,mul_assoc]; exact mul_le_mul_of_nonneg_left ht' (by unfold D; positivity)
include hq hp
lemma suite (H:Apart S p R)(h:Isle q S x p χ 6 f)(z:E4): Released (fun i=> mosaic (ε i) (Room q S x χ f i) z):= by
    unfold mosaic Room; let k(i):= index (ε i) z; have hz : plot q k z:= entrant hq z; by_cases he:z∈p '' (S:Set I)
    · obtain ⟨i,hi,rfl⟩:=he; refine ⟨0,tendsto_const_nhds.congr' ?_⟩; filter_upwards [tends_zero_at hq k S x p hp χ H hi hz,plot_lift hq hz] with j h hh; rw [if_pos hh,h,zero_smul] -- h path K definitional?
    obtain ⟨C,hc⟩:= h.path he k hz; refine ⟨Rest χ S p z • C, ((quiet_path hq k S x p χ hz hp).smul hc).congr' ?_⟩; filter_upwards [plot_lift hq hz] with i hi; rw [if_pos hi]
lemma expand_suite (H:Apart S p R)(h:Isle q S x p χ 6 f): Released (fun i=> (ε i ^4) • (∑ z:Site (regL i), Quiet q S x χ i z • f (i,lift z))):= by
    obtain ⟨C,hc,hw⟩:=tip_budget S x p χ h; let F(i:ℕ):= mosaic (ε i) (Room q S x χ f i); choose g hg using suite hq S x p hp χ H h
    refine ⟨_,(tendsto_integral_filter_of_dominated_convergence (F:=F) (μ:= (volume : Measure E4)) (fun z=>C*tipV z) (Eventually.of_forall fun i=> (mosaic_ok (epsilon_pos q i) (register S x χ f)).aestronglyMeasurable) (hw.mono fun i hi=> Eventually.of_forall (fun z=>hi z)) (tip_integrable.const_mul C) (Eventually.of_forall hg)).congr ?_⟩
    intro i; change ∫ x:E4,mosaic _ _ x=_; rw [mosaic_sum (epsilon_pos q i) (register S x χ f),paisley,Finset.sum_image]; swap; · intro x _ y _ hh; exact Function.LeftInverse.injective (g:=wrap (side q i)) (fun i=> wrap_lift i) hh -- exact 
    simp only [Room,wrap_lift,↓reduceIte]
end YM.PositionX.Crate.Porch
