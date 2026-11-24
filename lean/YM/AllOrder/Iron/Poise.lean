import YM.AllOrder.Iron.Branch
import YM.Next.STATIONARY.Block.Static
import YM.TraceExtension.Perfect.Stove
import YM.Next.STATIONARY.Joint.FourPoint
import YM.Next.STATIONARY.Joint.HaarJac
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Iron
open Lattice Laurent RG Filter Tree Metric Finset Function Gauge Matrix Module
open Exterior Wilson Precision Tree MeasureTheory Stationary
open scoped Matrix BigOperators Topology Classical ContDiff InnerProductSpace Matrix.Norms.Frobenius ENNReal
variable {G:Gauge}{c f:Side}{S:StepData c f} (F:Forest S.ratio)(t:S.Choices) {p:Clip}{R:PathData G}

open Work.F05
local notation "C"=> cash (helmets G c f)
local notation "W"=> Cou G c f
variable (i: G.ColorIndex)
local notation "J"=> Bodies G c f
open Wilson Precision
abbrev addressJ (S:StepData c f)(i:Bodies G c f):= (clothe G S i).1
lemma addrL (S:StepData c f)(i:Lines G f 1): addressJ S (.inl i)=S.ratio.parent i.1 := by unfold addressJ; rw [inflowL]; simp [unitSplit,Bloch.split_co]
lemma addrR (S:StepData c f)(i:Lines G c 0): addressJ (G:=G) S (.inr i)=i.1:=rfl
-- price envelope. row norm via resulting decay
lemma seed_near (x:Site f)(j:J) (h : addressJ S j ≠ S.ratio.parent x): seed F i x j=0:= by
 induction x using Forest.hike.induct F with
 | case1 x hx ih=>
    have hv: S.ratio.parent ((F.up x).used x).1=S.ratio.parent x:=by
       have ht:= F.stays x hx; cases he:F.up x with
       | mk a b=> cases b; · rfl
                  rw [he] at ht; simpa only [Step.used,Step.vec,↓reduceIte, sub_eq_add_neg] using ht
    have hk: link i ((F.up x).used x) j=0:= by
      apply Pi.single_eq_of_ne; rintro rfl; exact h ((addrL ..).trans hv)
    rw [seed,dif_pos hx,Pi.add_apply,ih (by rwa [F.stays x hx]),add_zero]; split; simp only [Pi.neg_apply,hk,neg_zero]; exact hk
 | case2 x hx=> rw [seed,dif_neg hx, Pi.neg_apply]; have ht : j ≠ Sum.inr (S.ratio.parent x,vac,i):=fun he=>h (he ▸ rfl); simp [ht]
lemma seed_bound (x:Site f)(j:J):|seed F i x j| ≤ (F.height x:ℝ)+1:= by
  induction x using Forest.hike.induct F with
  | case1 x hx ih=>
     have ht : ((F.height (x+(F.up x).vec):ℕ):ℝ)+1≤ F.height x:= by exact_mod_cast F.rise x hx
     have hp : |link i ((F.up x).used x) j| ≤1:= by simp [link, Pi.single_apply]; split <;> simp
     rw [seed,dif_pos hx,Pi.add_apply]; refine (abs_add_le ..).trans ?_; split
     · rw [Pi.neg_apply,abs_neg]; linarith
     linarith
  | case2 x hx=> rw [seed,dif_neg hx]; simp only [Pi.neg_apply, abs_neg,Pi.single_apply]; split <;> (rename_i hp; try simp); positivity
set_option maxHeartbeats 200000 in
lemma grace_bond (x:Key F G)(j:J): |graces F x j| ≤ 2*(4*(S.ratio.count.val:ℝ))+3 ∧ (3 < separation (S.ratio.parent x.1.val.1) (addressJ S j) → graces F x j=0):= by
 let k:=F.height; let a:= x.1.val.1; let b:=a+step x.1.val.2
 change |link x.2 x.1.val j - seed F x.2 a j + seed F x.2 b j|  ≤ _ ∧ _
 constructor
 · have ht x': (k x':ℝ)≤ 4*(S.ratio.count.val:ℝ):=by exact_mod_cast F.bound x'
   have hp : |link x.2 x.1.val j| ≤ 1:= by simp [link,Pi.single_apply]; split<;> simp
   refine (abs_add_le ..).trans ((add_le_add (abs_sub ..) le_rfl).trans ?_);
   have ha := ht a; have hh:= ht b; unfold k at *; linarith only [hp,seed_bound F x.2 a j,seed_bound F x.2 b j,ha,hh]
 intro h; let T:=S.ratio.parent; have hh: addressJ S j ≠ T a:= fun hx=> by rw [(show addressJ S j=T a from hx),separation_self] at h; omega
 have hx: addressJ S j ≠ T b:= fun hx=>by
   have hs: separation a b≤1:= Work.E03.sep_step a _
   have hb := Work.E04.parent_separation S.ratio a b; change 3 < separation (T a) _ at h; rw [hx] at h; unfold T at h; omega
 have he : link x.2 x.1.val j=0:= by apply Pi.single_eq_of_ne; intro h; exact hh (h ▸ addrL ..)
 change link _ _ _-seed F _ a j+seed F _ b j=_; rw [he,seed_near F _ _ _ hh,seed_near F _ _ _ hx]; ring

end YM.AllOrder.Iron
