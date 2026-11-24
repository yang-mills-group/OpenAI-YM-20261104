import YM.FormalBulk08.Pose.Harbor

/-! Scalar readout rooted payment from a general Knoxville tensor through
prescribed weight projection. No Norm on Frame fabricated.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Pose
open Filter Function Lattice Laurent Gauge Wilson Exterior Stationary
open Lava Lotus Mesa Gorge Shore City Kemp Rift
open Planned.PrimaryIntegral295 Place Carrier Film Labels Source Source.Drops Next.Foundations
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius ComplexConjugate Classical
variable {G : Gauge} {r u d j n D m:ℕ} {η A θ B : ℝ} {I : Type*} {a:Loc G 1}
variable (F: Labels.Frame G d)
lemma slate_plus {T K:Tile (edgeL G) r}(h:Knoxville (fame _) η (0,a) T A)(hv:Knoxville (fame _) η (0,a) K B) (hs:0<η)(d l): slate (T+K) d l=slate T d l+slate K d l:= by
    ext x; rw [slate_read a _ x hs (h.add hv),_root_.add_apply,slate_read a _ x hs h, slate_read a _ x hs hv, ←Summable.tsum_add (slate_wind a _ _ hs h) (slate_wind a _ _ hs hv)]; apply tsum_congr; intro i;rw [Pi.add_apply,add_mul]
lemma slate_scale {T:Tile (edgeL G) r}(h:Knoxville (fame _) η (0,a) T A)(hs:0<η)(c:ℝ)(d l): slate (c • T) d l=c • slate T d l:= by ext x; rw [slate_read a _ x hs (h.smul c),_root_.smul_apply, slate_read a _ x hs h,smul_eq_mul,←tsum_mul_left]; exact tsum_congr fun _=>mul_assoc ..
lemma slate_zero (r l d : ℕ): slate (0:Tile (edgeL G) r) d l=0 := by
    let H : Slate G d l:=0; have h :∀ x:Fin l→Snap G d,H x=∑' v,(0:Tile (edgeL G) r) v*(Tensor.coeff (tier v) l 0 x) := by simp [H];
    have e : ∃ T:Slate G d l,∀ x,T x=∑' v,(0:Tile (edgeL G) r) v*(Tensor.coeff (tier v) l 0 x):=⟨H,h⟩
    ext1 x; unfold slate; rw [dif_pos e]; exact (Classical.choose_spec e x).trans (by simp)
lemma bunch (F : Labels.Frame G d)(P Q:Slate G d n)(m): pocket F (P+Q) m=pocket F P m+pocket F Q m:= by
    unfold pocket lent; rw [←map_add (F.coords),←map_add]; apply congr_arg; apply congr_arg; unfold WardBin.tile; rw [← Finset.sum_add_distrib];apply Finset.sum_congr rfl; intro i _; simp only [tide_at,_root_.add_apply, Complex.ofReal_add,map_add,add_mul]
lemma stip (F: Labels.Frame G d)(P : Slate G d n)(m)(b:ℝ) : pocket F (b • P) m=(b:ℂ) • pocket F P m := by
   unfold pocket lent; rw [← F.coords.map_smul,← map_smul]; apply congr_arg; apply congr_arg; unfold WardBin.tile; rw [Finset.smul_sum]; apply Finset.sum_congr rfl;intro i _; simp only [tide_at,_root_.smul_apply,smul_eq_mul,Complex.ofReal_mul,map_mul,MvPolynomial.smul_eq_C_mul,mul_assoc]
lemma no_buns (F: Labels.Frame G d)(n): pocket F (0 : Slate G d n) m=0:= by simpa only [zero_smul,Complex.ofReal_zero] using stip F (0: Slate G d n) m 0

lemma pocket_cost (k n:ℕ) (i : F.Index) : ∃ C: ℝ,0≤C ∧ ∀ T: Slate G d n,∀ A:ℝ,0≤ A → (∀ v,‖T v‖≤ A*∏ i,‖v i‖) →
    ‖pocket F T k i‖≤ C*A:= by
   let M:=pieceL G d
   let s: Finset (Fin n→WardBin.Board G d):=Finset.univ.filter (fun i=>WardBin.depth i=k); let f (x:Fin n→WardBin.Board G d): Pol G:=∏ a,MvPolynomial.X (WardBin.key (x a));
   let p(x:Fin n→WardBin.Board G d):= (∏ i,‖(WardBin.chip (x i):Snap G d)‖); let C x:= p x * ‖F.coords (M (f x)) i‖
   have hc x:0≤C x:= by unfold C p; positivity
   refine ⟨∑ i∈s,C i,Finset.sum_nonneg fun i _=>hc i, fun T A hp H=>?_⟩
   rw [pocket_at]; unfold WardBin.tile
   rw [map_sum, map_sum,Finset.sum_apply];rw [Finset.sum_mul]; refine (norm_sum_le ..).trans (Finset.sum_le_sum (fun j hj=>?_)); change ‖F.coords (M (MvPolynomial.C _ * f j)) i‖≤ C j*A
   rw [←MvPolynomial.smul_eq_C_mul,map_smul,F.coords.map_smul,Pi.smul_apply,norm_smul,tide_at,Complex.norm_real]; exact (mul_le_mul_of_nonneg_right (H _) (norm_nonneg _)).trans_eq (show A*p j*_=_ from by unfold C;ring)
lemma pocket_lifts (p : Loc G 1) (i:F.Index) (r k n:ℕ)(hs : 0<η):∃ C:ℝ, 0≤C∧∀ T:Tile (edgeL G) r,∀ A:ℝ, Knoxville (fame _) η (0,p) T A → ‖pocket F (slate T d n) k i‖≤ C*A := by
   obtain ⟨C,hC,H⟩:= pocket_cost F k n i
   obtain ⟨B,hB,hP⟩:= slate_bill p r d n hs; refine ⟨C*B,mul_nonneg hC hB, fun T A ht=>?_⟩; rw [mul_assoc]; exact H _ _ (mul_nonneg hB ht.1) (fun x=>by rw [slate_read p T x hs ht]; exact (hP T A ht x).2)
end YM.FormalBulk08.Pose
