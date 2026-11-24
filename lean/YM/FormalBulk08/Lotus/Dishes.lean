import YM.FormalBulk08.Lotus.Tall

noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Lotus
open Lava Gorge Lattice Laurent Bloch Filter Set Function Wick
open scoped BigOperators Classical ENNReal Topology
variable {I : Type*} [Fintype I] {r : ℕ} {η : ℝ}
lemma sparkle_stare {K : Tile (Biglot I) (r+1+1)} {T : (n:Side)→Tile (Tor n I) (r+1+1)}
    {q : Biglot I→ Biglot I→ℝ} {M : (n:Side)→ Tor n I → Tor n I → ℝ} (h : Light K T) (e : Wind q M) (B C : ℝ)
    (hs : 0<η) (H : Bright T η B) (hp : ∀ᶠ n in atTop, Grate (lake n I) η (M n) C) (i : Fin r) :
    Light (stare q K) (fun n=>stare (M n) (T n)) := by
   intro v
   let R n := drip n ∘ v
   let L:= size (v i).1
   let d := C*((r+2:ℕ):ℝ)*((r+1:ℕ):ℝ)
   let U (x : Biglot I × Biglot I) := Real.exp (η*L)*(d*B)* (coast (η/2) x.1*coast (η/2) x.2)
   obtain ⟨l,hl,hx⟩:= (H.and hp).exists
   have hb:=hl.1; have hh:=hx.1; have hd : 0≤d:=mul_nonneg (mul_nonneg hh (by positivity)) (by positivity)
   refine jolt_limit (windup I I) (fun n=> telescopeTerm (M n) (T n) (R n)) (telescopeTerm q K v) U ((coast_pair (half_pos hs)).mul_left _) (fun j=> mul_nonneg (mul_nonneg (Real.exp_pos _).le (mul_nonneg hd hb)) (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)) (height_pair h e v) ?_
   filter_upwards [H,hp] with n hn hm k
   let W : chain (Tor n I) (r+1+1):= Fin.cons k.2 (Fin.cons k.1 (R n)); let t:=wide (lake n I) W
   have he : skit n k.1.1 + skit n k.2.1 ≤ 2*t+2*L := by
      have hz (j : Fin (r+1+1)): skit n (W j).1 ≤ t+L:= by
         have hh := reached (lake n I) W j i.succ.succ; change skit n ((W j).1- (W (i.succ.succ)).1) ≤ t at hh; apply le_trans ?_ (Nat.add_le_add hh (show skit n (W i.succ.succ).1≤L by simp only [W,R, Fin.cons_succ, Function.comp_apply,drip];exact skirt ..))
         have ha:=skit_add n ((W j).1- (W i.succ.succ).1) ((W i.succ.succ).1); rw [sub_add_cancel] at ha; exact ha
      have hu:=hz 0; have hv:=hz (Fin.succ 0); change skit n k.2.1 ≤ t+L at hu; have ht : skit n k.1.1≤t+L:=by simpa only [W,Fin.cons_zero,Fin.cons_succ] using hv
      omega
   refine sloped L t n k.1 k.2 _ he ?_ hs.le
   have ho : ‖halve (M n k.1 k.2)*((r+2:ℕ):ℝ)* ((r+1:ℕ):ℝ)‖ ≤ d := by
      rw [norm_mul,norm_mul,half_norm,Real.norm_of_nonneg (show 0≤((r+2:ℕ):ℝ) by positivity),Real.norm_of_nonneg (show 0≤((r+1:ℕ):ℝ) by positivity)]; unfold d; gcongr
      have hg := hm.rough hs.le k.1 k.2; rw [Real.norm_eq_abs]; linarith
   unfold telescopeTerm; rw [norm_mul,mul_left_comm]; exact mul_le_mul ho (palmed hn W 0) (by positivity) hd
end YM.FormalBulk08.Lotus
