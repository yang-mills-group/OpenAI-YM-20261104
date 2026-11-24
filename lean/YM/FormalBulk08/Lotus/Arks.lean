import YM.FormalBulk08.Lotus.Dishes

noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Lotus
open Lava Gorge Lattice Laurent Bloch Filter Set Function Wick
open scoped BigOperators Classical ENNReal Topology
variable {I : Type*} [Fintype I] {m p : ℕ} (i : Fin (m+p))
    {K : Tile (Biglot I) (m+1)} {T : (n:Side)→Tile (Tor n I) (m+1)} {Z : Tile (Biglot I) (p+1)} {S : (n:Side)→Tile (Tor n I) (p+1)}
    {q : Biglot I→ Biglot I→ℝ} {M : (n:Side)→ Tor n I→ Tor n I→ ℝ}
omit [Fintype I] in
lemma cast_pair (h : Light K T) (z : Light Z S) (e : Wind q M) (v : chain (Biglot I) (m+p)) (x : Biglot I × Biglot I) :
    Tendsto (fun n=> weld (M n) (T n) (S n) (drip n ∘ v) (drip n x.1,drip n x.2)) atTop (𝓝 (weld q K Z v x)) := by
    unfold weld halve clutch shed; refine (((tendsto_const_nhds.mul (e x.1 x.2)).mul_const _).mul_const _).mul (Tendsto.mul ?_ ?_)
    · have hv:=h (arm v x.1); simpa only [arm,Fin.comp_cons,Function.comp_assoc] using hv
    have hv:=z (leg v x.2); simpa only [leg,Fin.comp_cons,Function.comp_assoc] using hv
-- W's wide controls roots with origin skit shifted
omit [Fintype I] in
lemma skit_anchor {r : ℕ} (n : Side) (u : chain (Tor n I) r) (i j : Fin r) : skit n (u j).1 ≤ wide (lake n I) u + skit n (u i).1 := by
   have hh:=skit_add n ((u j).1-(u i).1) ((u i).1);rw [sub_add_cancel] at hh; exact hh.trans (Nat.add_le_add_right (reached (lake n I) u j i) _)
omit [Fintype I] in
lemma pair_amount (v : chain (Biglot I) (m+p)) (n : Side) (a b : Tor n I) :
     skit n a.1 + skit n b.1 ≤ 2*(wide (lake n I) (arm (drip n ∘ v) a)+wide (lake n I) (leg (drip n ∘ v) b)+skit n (a.1-b.1))+2*size (v i).1 := by
   have ht :=skit_add n (a.1-b.1) b.1; have hz:= skit_add n (b.1-a.1) a.1; rw [sub_add_cancel] at ht hz; rw [skit_sub n b.1] at hz
   cases i using Fin.addCases with
   | left i=>
      have h : skit n a.1 ≤ wide (lake n I) (arm (drip n ∘ v) a) + size (v (Fin.castAdd p i)).1 := (skit_anchor n (arm (drip n ∘ v) a) i.succ 0).trans (Nat.add_le_add_left (by simp only [arm,Fin.cons_succ,comp_apply,drip]; exact skirt ..) _)
      omega
   | right j=>
      have h : skit n b.1 ≤ wide (lake n I) (leg (drip n ∘ v) b) + size (v (Fin.natAdd m j)).1 := (skit_anchor n (leg (drip n ∘ v) b) j.succ 0).trans (Nat.add_le_add_left (by simp only [leg,Fin.cons_succ,comp_apply,drip];exact skirt ..) _)
      omega
include i

lemma sparkle_bond (h : Light K T) (z : Light Z S) (e : Wind q M) (B A C : ℝ) {η : ℝ}
    (hs : 0<η) (H : Bright T η B) (hv : Bright S η A) (hg : ∀ᶠ n in atTop, Grate (lake n I) η (M n) C) :
    Light (bond q K Z) (fun n=>bond (M n) (T n) (S n)) := by
   intro v
   let X := 1/2*((m+1:ℕ):ℝ)*((p+1:ℕ):ℝ); let d:=size (v i).1; let Y:=X*(C*(B*A))
   obtain ⟨l,hl,hx,hj⟩:= (H.and (hv.and hg)).exists
   have hB:=hl.1; have hA:=hx.1; have hC:=hj.1; have hX : 0≤X:=by unfold X; positivity
   let U (x:Biglot I×Biglot I):= Real.exp (η*d)*Y* (coast (η/2) x.1*coast (η/2) x.2)
   refine jolt_limit (windup I I) (fun n=> weld (M n) (T n) (S n) (drip n ∘ v)) (weld q K Z v) U ((coast_pair (half_pos hs)).mul_left _) (fun i=>by unfold U Y coast;positivity) (cast_pair h z e v) ?_
   filter_upwards [H,hv,hg] with n hn ha hc k
   refine sloped d _ n k.1 k.2 _ (pair_amount i v n k.1 k.2) ?_ hs.le
   let W:= arm (drip n ∘ v) k.1; let R:= leg (drip n ∘ v) k.2;let t:=skit n (k.1.1-k.2.1);
   have he := mul_le_mul_of_nonneg_left (mul_le_mul (grove hc k.1 k.2) (mul_le_mul (palmed hn W 0) (palmed ha R 0) (by positivity) hB) (show 0 ≤ (Real.exp (η*wide (lake n I) W)*‖T n W‖)*(Real.exp (η*wide (lake n I) R)*‖S n R‖) by positivity) hC) hX
   -- m ambiguous x's. specialize
   refine le_trans (le_of_eq ?_) he
   unfold weld;rw [show clutch (shed (T n) k.1) (shed (S n) k.2) (drip n ∘ v) = T n W*S n R from rfl];simp_rw [norm_mul,half_norm,Nat.cast_add,mul_add η,Real.exp_add]; unfold X; push_cast;
   rw [Real.norm_of_nonneg (show (0:ℝ)≤(m:ℝ)+1 by positivity),Real.norm_of_nonneg (show (0:ℝ)≤(p:ℝ)+1 by positivity)];unfold W R; ring
end YM.FormalBulk08.Lotus
