import YM.FormalBulk08.Rift.Glory

/-! Strict resources — tapped width affine conversions. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Rift
open Reef Lava Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 PowerSeries
open Lotus Shore Mesa Gorge City Cork
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G : Gauge} {I J V : Type*}{η C : ℝ} {m n : ℕ} {D : Reach V} (a : V)

lemma meet_wide (x y : V)(P : chain V m)(U : chain V n):
     wide D (Fin.cons y (Fin.append P U) : chain V (m+n+1)) ≤ wide D (Fin.cons x P : chain V (m+1)) + wide D (Fin.cons x U : chain V (n+1))+D.d x y := by
    apply known_wide; intro i j
    let H: chain V (m+1):= Fin.cons x P; let W:chain V (n+1):=Fin.cons x U
    have ht p:D.d x (P p) ≤ wide D H:= reached D H 0 p.succ
    have hz p:D.d (U p) x ≤ wide D W:= reached D W p.succ 0
    have he p q:D.d (P p) (U q) ≤ wide D H+wide D W:= (D.tri _ x _).trans (add_le_add (by rw [D.turn (P p)]; exact ht p) (by rw [D.turn x]; exact hz q))
    cases i using Fin.cases with
    | zero=>
       cases j using Fin.cases with
       | zero=> rw [D.self];exact Nat.zero_le _
       | succ j=>
         cases j using Fin.addCases with
         | left j=> simp only [Fin.cons_zero,Fin.cons_succ,Fin.append_left]; have hx:=D.tri y x (P j);rw [D.turn y x] at hx; change _≤wide D H+wide D W+_; have hj:=ht j;omega
         | right j=> simp only [Fin.cons_zero,Fin.cons_succ,Fin.append_right]; have hx:=D.tri y x (U j);rw [D.turn y x,D.turn x (U j)] at hx;change _≤wide D H+wide D W+_;have hj:=hz j;omega
    | succ i=>
       cases j using Fin.cases with
       | zero=> cases i using Fin.addCases with
                | left i=> simp only [Fin.cons_zero,Fin.cons_succ,Fin.append_left]; have hx:=D.tri (P i) x y;rw [D.turn (P i) x] at hx;change _≤wide D H+wide D W+_;have hi:=ht i;omega
                | right i=> simp only [Fin.cons_zero,Fin.cons_succ,Fin.append_right]; have hx:=D.tri (U i) x y; change _≤wide D H+wide D W+_; have hi:=hz i;omega
       | succ j=>
           cases i using Fin.addCases <;> cases j using Fin.addCases <;> rename_i i j <;> simp only [Fin.cons_succ,Fin.append_left,Fin.append_right]
           · exact le_trans (reached D H i.succ j.succ) (show wide D H ≤ wide D H+wide D W+_ by omega)
           · exact (he i j).trans (Nat.le_add_right ..)
           · rw [D.turn]; exact (he j i).trans (Nat.le_add_right ..)
           exact (reached D W i.succ j.succ).trans (show wide D W ≤ wide D H+wide D W+_ by omega)
variable {a}
lemma knox_clasp {T:Tile V m}{K:Tile V n}{B:ℝ}(h:Knoxville D η a T C)(e:Knoxville D η a K B)(hp:0≤η)(x:V):
      Knoxville D η x (clutch T K) (Real.exp (η*D.d a x)*(C*B)) := by
    refine ⟨mul_nonneg (Real.exp_pos _).le (mul_nonneg h.1 e.1),?_⟩
    rw [←Equiv.tsum_eq (castle V m n),ENNReal.tsum_prod'];rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_mul h.1]; refine le_trans ?_ (mul_le_mul_right (mul_le_mul' h.2 e.2) _)
    rw [←ENNReal.tsum_mul_right,←ENNReal.tsum_mul_left];apply ENNReal.tsum_le_tsum; intro u;rw [←ENNReal.tsum_mul_left, ←ENNReal.tsum_mul_left]; apply ENNReal.tsum_le_tsum; intro v; have hh:=shine_le η hp (meet_wide (D:=D) a x u v); rw [shine_add,shine_add] at hh
    refine le_trans (mul_le_mul_left hh _) (le_of_eq ?_); rw [show clutch _ _ _=_ from ?_, enorm_mul]; unfold Gorge.shine; ac_rfl
    case _=> show clutch T K (castle V m n (u,v))=T u*K v; simp [clutch,castle,Function.comp_def]

lemma ash_pledge (G : Gauge) (w : TypeFace 1 × hue G)(l:Bool)(k r)(z:hue G): ∃ B:ℝ, 0≤B ∧ ∀ a:Cover, Knoxville (fame _) η (a,w) (hill z (a,w) l k r) B := by
    let P:=rancho (paste (will z l w.2)) k r
    let U a (p:chain (hue G) r) : Tile (edgeL G) r:= fun v=>if rowD (a,w) ∘ p=v then P p else 0
    have he (a:Cover)(p):Knoxville (fame _) η (a,w) (U a p) |P p|:= by
        refine ⟨abs_nonneg _,?_⟩; let v:=rowD (a,w)∘p; rw [tsum_eq_single v]; swap;· intro x hx; unfold v at hx;simp only [U,if_neg (Ne.symm hx),enorm_zero,mul_zero]
        have hv: wide (fame _) (Fin.cons (a,w) v)=0:= Nat.eq_zero_of_le_zero (known_wide _ _ 0 (fun i j=>by cases i using Fin.cases <;> cases j using Fin.cases <;> simp [v,fame,capD,rowD,Laurent.size]))
        unfold U; rw [if_pos rfl,hv,show Gorge.shine η 0=1 by simp [Gorge.shine],one_mul,← Real.norm_eq_abs,ofReal_norm]
    refine ⟨∑ p:chain (hue G) r,|P p|,by positivity,fun a=>?_⟩
    rw [show hill z (a,w) l k r= (∑ p:chain (hue G) r,U a p) from funext fun v=> by simp [U,Finset.sum_apply,hill,P]];exact knox_sum _ (fun p _=> he a p)

lemma ash_charge (G : Gauge)(z:hue G)(w : TypeFace 1 × hue G)(l:Bool)(k)(p:diagD n)(hs:0≤η): ∃ B:ℝ,0≤B ∧ ∀ (T: Tile (edgeL G) (p.val.1+1)) (a:Cover),∀ x:edgeL G,(fame _).d (a,w) x≤1 →∀ C:ℝ,Bail (fame _) η T C→ Knoxville (fame _) η x (plaster z (a,w) l k p T) (B*C) := by
   obtain ⟨K,hK,H⟩:= ash_pledge G w l k p.val.2 z (η:=η)
   refine ⟨|(↑(p.val.1+1:ℕ):ℝ)| * Real.exp η*K,by positivity,fun T a x he C h=>?_⟩
   have ht:= knox_clasp (show Knoxville (fame _) η (a,w) (shed T (a,w)) C from ⟨h.1,rim_stud h _⟩) (H a) hs x
   apply (ht.polish.rename (Finset.mem_antidiagonal.mp p.property) |>.smul ((p.val.1+1:ℕ):ℝ)).mono
   have he' := le_trans (Real.exp_monotone (mul_le_mul_of_nonneg_left (show (((fame _).d (a,w) x:ℕ):ℝ) ≤ (1:ℝ) by exact_mod_cast he) hs)) (le_of_eq (congr_arg Real.exp (mul_one _)))
   refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right he' (mul_nonneg h.1 hK)) (abs_nonneg _)).trans_eq ?_;ring
end YM.FormalBulk08.Rift
