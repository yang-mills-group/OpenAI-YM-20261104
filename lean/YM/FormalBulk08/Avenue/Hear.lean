import YM.FormalBulk08.Avenue.Bough
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Avenue
open Filter Set Metric MeasureTheory Function Lattice Laurent Bloch Exterior Precision RG Next.Free
open Stationary
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix
variable {n:Side}
open MSbar.Tree.Resolvent
variable {j:ℕ}{k:ℝ}
open Flat UVExtension.Free
variable {G:Gauge}
open Reef Mesa Gorge

variable {D l:ℕ}
open Kemp Pose Dawn Spigot Orb Wick Series Jets MeasureTheory Lotus Shore Lava Rift
open Grail
variable {x:Loc G 1}{η σ A B C:ℝ}{u r p:ℕ} {q:edgeL G→edgeL G→ℝ}
lemma stare_plus {V W:Tile (edgeL G) (r+2)}(h:Knoxville (fame _) η (0,x) V A)(he:Knoxville (fame _) η (0,x) W B)(hs:0≤η)(hv:∀ i j,‖q i j‖≤C)(hc:0≤C): stare q (V+W) = stare q V+stare q W:= by
   let T:=V+W
   have hx:= Quire.stove (h.add he) h hs hv hv hc hc; change stare q T-_ = _ at hx
   rw [show T - V=W from add_sub_cancel_left V W, sub_self,show stare (0:edgeL G→edgeL G→ℝ) V=0 from funext fun v=>by simp [stare, halve],add_zero] at hx; change stare q T=_; rw [add_comm]; exact eq_add_of_sub_eq hx
lemma stare_smul (a:ℝ)(V: Tile (edgeL G) (r+2)): stare q (a • V)=a • stare q V:= by
   ext1 v; refine tsum_congr ?_ |>.trans (show (∑' i, a*telescopeTerm q V v i) =a*(∑' i,telescopeTerm q V v i) from tsum_mul_left); intro i; unfold telescopeTerm Lava.shed; simp only [Pi.smul_apply];ring
lemma shed_spin {X:Type*}(g:X)(a:X)(v:chain X r)(T:Tile X (r+1+1))(h:Agate T): shed (shed T a) g v=shed (shed T g) a v:= by
    unfold Lava.shed; let s:= Equiv.swap (0: Fin (r+2)) (Fin.succ 0); rw [← h _ s]; apply congr_arg T; funext i; cases i using Fin.cases with
    | zero=> simp [s]
    | succ j=> cases j using Fin.cases with
               | zero=> simp [s]
               | succ j=> have he : s (j.succ.succ)=j.succ.succ:= Equiv.swap_apply_of_ne_of_ne (by simp) (by exact (Fin.succ_injective _).ne (Fin.succ_ne_zero _)); simp [he]
lemma tower_star (V:Tile (edgeL G) (r+2))(hT:Agate V)(hs:0≤η)(hp:Knoxville (fame _) η (0,x) V B)(hv:Torrid V η 0 x)(h:∀ i j,‖q i j‖≤ C)(hc:0≤C) : Torrid (stare q V) η 0 x := by
    cases r with
    | zero=> intro r hr; omega
    | succ r=> apply Grail.current.mpr
               rw [show tap (stare q V)=0 from ?_]; apply Knox_zeros
               funext v; apply Eq.trans (?_ : tap (stare q V) v=0) rfl
               let p: Loc G 1:=(v 0).2; let y:=(v 0).1; let z:= Fin.tail v
               let H (x:TypeFace 1)(b:edgeL G × edgeL G):= telescopeTerm q V (Fin.cons (y,x,p.2) z) b; let J(x:TypeFace 1)(b):=telescopeTerm q V (Fin.cons (City.backwards y x,x,p.2) z) b
               have hH x:Summable (H x):=((fund_stare hp hs h hc).points hs _).of_norm;have hJ x:Summable (J x):=((fund_stare hp hs h hc).points hs _).of_norm
               have he b: (∑ x,(H x b-J x b))=0:= by
                  let F:edgeL G→ℝ:=fun x=> V (Fin.cons x (Fin.cons b.2 (Fin.cons b.1 z)))
                  have hz (i:edgeL G): shed (shed V b.2) b.1 (Fin.cons i z)=F i:= by
                     have hx:= shed_spin i b.1 z (shed V b.2) (hT.shed b.2)
                     have ht:= shed_spin i b.2 (Fin.cons b.1 z) V hT
                     exact hx.trans ht
                  have ht:= Palm.lease_cut x _ (hv (r+1+1) rfl)
                  let L:chain (edgeL G) (r+3):= Fin.cons (y,p) (Fin.cons b.2 (Fin.cons b.1 z))
                  have hd := congr_fun ht L; simp only [tap,L,Fin.cons_zero,Fin.tail_cons,City.riverP,Finset.sum_apply,Pi.sub_apply,Pi.zero_apply,lengthen] at hd
                  unfold H J telescopeTerm; simp_rw [hz,←mul_sub]; rw [←Finset.mul_sum, show (∑ x,(F (y,x,p.2)-F (City.backwards y x,x,p.2)))=0 from hd,mul_zero]
               unfold tap City.riverP; rw [Finset.sum_apply]; change (∑ x:TypeFace 1,((∑' i,H x i)-∑' i,J x i))=_; simp_rw [← Summable.tsum_sub (hH _) (hJ _)]; rw [←Summable.tsum_finsetSum (fun x _=> (hH x).sub (hJ x))]; simp_rw [he,tsum_zero]
-- recurse
lemma lofty (u:Loc G 1)(S:Beams (edgeL G))(hp:∀ i,Torrid (S i) η 0 u)(h:∀ i j,‖q i j‖≤C)(hc:0≤C)(H:∀ i,∃ A,Knoxville (fame _) η (0,u) (S i) A)(he:∀ i,Agate (S i))(hs:0≤η)(p i:ℕ): Torrid (bleat q S p i) η 0 u ∧ Agate (bleat q S p i) ∧ ∃ B, Knoxville (fame _) η (0,u) (bleat q S p i) B:= by
   induction p generalizing i with
   | zero=> exact ⟨hp i,he i,H i⟩
   | succ p ih=> obtain ⟨hT,H,W,hw⟩:= ih (i+2);exact ⟨tower_star _ H hs hw hT h hc,H.staring q,_,knox_stare hw hs h hc⟩
end YM.FormalBulk08.Avenue
