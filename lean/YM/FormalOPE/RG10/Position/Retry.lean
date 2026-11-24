import YM.FormalOPE.RG10.Position.Rails

/-! # Solving the mass-independent conjugacy equation using one-step dilation -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Position.Grade
open Function Maxwell Labels Extraction Filter Finset Extra.FD PertExtension MeasureTheory
  Topology Metric PertExtension.Position PertExtension.Physical PowerSeries Triangle Matrix
open scoped Topology BigOperators ContDiff Classical
variable {J : Type*} [Fintype J] [DecidableEq J] {w:J→ℕ}
variable {g:Flow}
local notation "T" => Matrix J J Triangle.fps
namespace Retry
variable {s:ℝ}{A B L M P:Matrix J J Triangle.fps}(hu:stamp A 0=stone w s)(hv:stamp B 0=stone w s)
open Flow
omit [DecidableEq J] in
lemma stamped (n) : stamp (A * P) n = ∑ a∈Finset.HasAntidiagonal.antidiagonal n,stamp A a.1 * stamp P a.2 := by
 ext i j; rw [Matrix.sum_apply]; simp_rw [stamp_apply, Matrix.mul_apply,_root_.map_sum,stamp_apply,coeff_mul]
 exact Finset.sum_comm

def inter (g:Flow) (s:ℝ) (A B P : Matrix J J Triangle.fps) := (P.map (g.warp s))*A-B*P
omit [DecidableEq J] in
lemma inter_add : inter g s A B (P+L)= inter g s A B P + inter g s A B L := by
 simp only [inter,show (P+L).map (g.warp s) = P.map (g.warp s) + L.map (g.warp s) from by ext i j : 1; simp,add_mul,mul_add]; abel
omit [DecidableEq J] in
lemma inter_sub : inter g s A B (P-L)= inter g s A B P-inter g s A B L := by
 simp only [inter,show (P-L).map (g.warp s) = P.map (g.warp s) - L.map (g.warp s) from by ext i j : 1; simp,sub_mul,mul_sub]; abel
-- all lower-than-first-weight series forget algebraic sizing
omit [Fintype J] [DecidableEq J] in
lemma first_sup {n:ℕ} (hp:∀ i<n,stamp P i=0) : stamp (P.map (g.warp s)) n=stamp P n := by
 ext i j; simp only [stamp_apply,Matrix.map_apply, Flow.through, add_eq_left]; apply sum_eq_zero; intro b hb; rw [← stamp_apply, hp b (mem_range.mp hb), Matrix.zero_apply,zero_mul]
omit [DecidableEq J] in
lemma stamp_left {n:ℕ} (hp:∀ i<n,stamp P i=0) : stamp (P*A) n= stamp P n*stamp A 0 := by
 rw [stamped,sum_eq_single_of_mem (n,0) (by simp)]; rintro ⟨i,j⟩ hj hi; apply Eq.trans (congr_arg (fun x=> x * stamp A j) (hp i ?_)) (by simp); obtain hz:=mem_antidiagonal.mp hj; grind
omit [DecidableEq J] in
lemma stamp_right {n:ℕ} (hp:∀ i<n,stamp P i=0) : stamp (A*P) n= stamp A 0*stamp P n := by
 rw [stamped,sum_eq_single_of_mem (0,n) (by simp)]; rintro ⟨i,j⟩ hj hi; apply Eq.trans (congr_arg (fun x=> stamp A i*x) (hp j ?_)) (by simp); obtain hz:=mem_antidiagonal.mp hj; grind
omit [Fintype J] [DecidableEq J] in
lemma subtract (n) : stamp (A-B) n= stamp A n-stamp B n := by ext; simp
omit [Fintype J] [DecidableEq J] in
lemma added (n) : stamp (A+B) n=stamp A n+stamp B n := by ext; simp
include hu hv
lemma definite {n:ℕ} (hp:∀ i<n,stamp P i=0) : stamp (inter g s A B P) n= stamp P n*stone w s - stone w s*stamp P n := by
 unfold inter; rw [subtract,stamp_left,stamp_right hp,first_sup hp,hu,hv]; intro i hi; rw [first_sup, hp i hi]; exact fun j hj=>hp j (hj.trans hi)
lemma rises {n:ℕ} (hp:∀ i<n,stamp P i=0) (i j : J) : stamp (inter g s A B P) n i j= stamp P n i j*(Real.exp (-s*w j)-Real.exp (-s*w i)) := by rw [definite hu hv hp]; simp [stone]; ring
lemma alone (h:0<s) (hZ:Trim w P)(hK:inter g s A B P=0) : P=0 := by
 suffices ∀ i,stamp P i=0 by
   ext i j k; exact (by rw [← stamp_apply,this]; simp) -- ext order
 intro n; induction n using Nat.strong_induction_on with
 | _ n ih =>
    ext i j; by_cases h':w j<w i
    · have hw:0< Real.exp (-s*w j)-Real.exp (-s*w i):= sub_pos.mpr (Real.exp_lt_exp.mpr (mul_lt_mul_of_neg_left (Nat.cast_lt.mpr h') (by linarith)))
      have ht:= rises hu hv ih i j (g:=g); rw [hK] at ht;
      exact (mul_eq_zero.mp (ht.symm.trans (by simp))).resolve_right hw.ne'
    simp only [stamp_apply,hZ _ _ (le_of_not_gt h'),map_zero,Matrix.zero_apply]

-- precision transferred through equal lower jets
lemma similar {n:ℕ} (hp:∀ i≤n,stamp P i=stamp L i) : stamp (inter g s A B P) n= stamp (inter g s A B L) n := by
 apply sub_eq_zero.mp; rw [← subtract,← inter_sub,definite hu hv,subtract,hp n le_rfl]; swap; · intro j hj; rw [subtract,hp j hj.le,sub_self]
 simp
omit hu hv
end Retry

namespace Passe
variable (h:Passe g w)
open Retry
-- use the step s=1 only. compatibility across all other scales is proved afterwards.
def demand (N: Matrix J J fps) := inter g 1 (h.train 1) (h.drive 1) N
lemma nonTile {N : T} (hu : Cut w N)(hv:tile w N=1) : Trim w (h.demand N) := by
  refine Cut.crush ?_ ?_;
  · exact ((hu.carries _).mul (h.rank _)).sub ((layer_cut (h.station_block _)).mul hu)
  unfold demand inter; rw [tile_sub,Cut.tile (hu.carries _) (h.rank _), Cut.tile (layer_cut (h.station_block _)) hu, tile_map,hv,layer_fixed (h.station_block 1)]; simp [drive]

def rebate (N: Matrix J J fps) (n:ℕ) : Matrix J J fps := of fun i j=> monomial (R:=ℝ) n
   (if w j < w i then (stamp (h.demand N) n i j)/(Real.exp (-(w i:ℝ)) - Real.exp (-(w j:ℝ))) else 0 )
lemma rebate_trim (N:T)(n): Trim w (h.rebate N n):= fun _ _ hz=> by simp [rebate, hz.not_gt]
lemma rebate_prior (N:T){n k : ℕ}(hk:k<n): stamp (h.rebate N n) k=0:= by ext; simp [rebate,coeff_monomial, hk.ne]

lemma cleared {N : T} (n:ℕ) (hu: Cut w N)(hv:tile w N=1) : stamp (h.demand (N+h.rebate N n)) n=0 := by
  unfold demand; rw [inter_add,added]; ext i j; simp only [Matrix.zero_apply, Matrix.add_apply]; rw [rises (h.full _) (h.stationed _) (fun _ ha=>h.rebate_prior N ha)];
  by_cases e:w j<w i
  · change stamp (h.demand N) _ _ _ + _ =_; rw [stamp_apply (h.rebate N n),rebate, of_apply,coeff_monomial,if_pos rfl,if_pos e]; simp only [neg_mul,one_mul];
    have hz:Real.exp (-(w i:ℝ)) - Real.exp (-(w j:ℝ)) < 0:=sub_neg.mpr (Real.exp_lt_exp.mpr (neg_lt_neg (by exact_mod_cast e)))
    rw [← neg_sub (Real.exp (-↑(w i))) (Real.exp (-↑(w j))), mul_neg,div_mul_cancel₀ _ hz.ne]; ring
  have ha:= h.nonTile hu hv _ _ (le_of_not_gt e); change stamp (h.demand N) _ _ _ + _ =_; simp [ha,rebate,e]

def work : ℕ→Matrix J J fps
  | 0=>1
  | n+1=> work n+h.rebate (work n) (n+1)
lemma work_on (n) : Cut w (h.work n) ∧ tile w (h.work n)=1 := by induction n with
 | zero=> exact ⟨layer_cut (tiled_one w),layer_fixed (tiled_one w)⟩
 | succ n ih=> rw [work]; exact ⟨ih.1.add (trim_cut (h.rebate_trim _ _)),by rw [tile_add,ih.2,zero_tile (h.rebate_trim _ _),add_zero]⟩

lemma effort {m n:ℕ}(hi:m ≤ n) : stamp (h.work n) m=stamp (h.work m) m := by induction n,hi using Nat.le_induction with
 | base=>rfl
 | succ n hx ih=> rw [work,added,h.rebate_prior _ (Nat.lt_succ_of_le hx), add_zero]; exact ih

lemma radius (n:ℕ) : stamp (h.demand (h.work n)) n=0:= by
 cases n with
 | zero=> rw [work,demand,inter]; simp [subtract,h.full,h.stationed]
 | succ n=> exact h.cleared _ (h.work_on _).1 (h.work_on _).2

def book : Matrix J J fps := of fun i j=> PowerSeries.mk fun n=> stamp (h.work n) n i j
lemma row (n) : stamp h.book n= stamp (h.work n) n:= by ext; simp [book]
theorem booked : Cut w h.book ∧ tile w h.book=1 ∧ h.demand h.book=0 := by
 constructor
 · intro i j hi; ext n : 1; rw [← stamp_apply,row,stamp_apply, (h.work_on _).1 _ _ hi]
 constructor
 · ext i j n; rw [← stamp_apply, canvas_tile,h.row,← canvas_tile,(h.work_on _).2]; rfl
 ext i j n; rw [← stamp_apply, show stamp (h.demand h.book) n=stamp (h.demand (h.work n)) n from similar (h.full _) (h.stationed _) (fun i hi=>(h.row _).trans (h.effort hi).symm), h.radius]; simp
lemma recovered {N:Matrix J J Triangle.fps}(hu:Cut w N)(hv:tile w N=1)(ht:h.demand N=0) : N=h.book := by
 apply sub_eq_zero.mp; apply alone (h.full _) (h.stationed _) zero_lt_one ((hu.sub h.booked.1).crush (by rw [tile_sub,h.booked.2.1,hv,sub_self])); rw [inter_sub]; change h.demand N - h.demand h.book=0; rw [h.booked.2.2,ht,sub_self]
end Passe
end YM.FormalOPE.RG10.Position.Grade
