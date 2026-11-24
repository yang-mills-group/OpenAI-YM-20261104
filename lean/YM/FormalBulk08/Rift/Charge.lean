import YM.FormalBulk08.Rift.Pass

/-! One arrow strict (and can use on DIFFERENCES). Shifts from any root.
`tap` extended into all slots with dummy direction. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Rift
open Reef Lava Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 PowerSeries
open Lotus Shore Mesa Gorge City Cork
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G : Gauge} {I J V : Type*}{η C : ℝ} {m n : ℕ}

lemma mount_hull (G : Gauge)(k:ℕ×ℕ)(r:ℕ)(hs:0≤η):∃ M: hue G→ℝ,(∀ a,0≤M a)∧∀ a x (t:Stationary.Loc G 1) (T : Pot G) (C:ℝ),(∀ i,1 ≤ i → i≤r+1 → Bail (fame _) η (T k.1 i) C)→0≤C → Knoxville (fame _) η (x,t) (cruisesD a x k r T) (M a*C) := by
   choose B hB H using fun (z:hue G)(w : TypeFace 1×hue G)(l:Bool)(p:diagD r)=> ash_charge G z w l k.2 p hs
   let J (a:hue G) w l := ∑ p∈(Finset.antidiagonal r).attach, B a w l p
   refine ⟨fun a=> ∑ w:TypeFace 1× hue G,(J a w true + J a w false),fun a=>?_ , fun a x t T C he hc=>?_⟩
   · unfold J; exact Finset.sum_nonneg fun b _=> add_nonneg (Finset.sum_nonneg (fun p _=>hB a b true _)) (Finset.sum_nonneg fun p _=>hB a b false _)
   have hh w z l (hy : (fame _).d (z,w) (x,t)≤1):Knoxville (fame _) η (x,t) (shapeD a (z,w) l k r T) (J a w l*C):= by
       unfold shapeD J; rw [Finset.sum_mul]; refine knox_sum _ fun i _=> H a w l i (T k.1 _) z _ hy C (he _ (by omega) (by have :=Finset.mem_antidiagonal.mp i.property;omega))
   unfold cruisesD; rw [Finset.sum_mul]; simp_rw [add_mul]; refine knox_sum _ fun w _=>(hh w x true ?_).add (hh w (backwards x w.1) false ?_)
   · change size (x-x)≤1;simp [Laurent.size]
   change size ((x-_)-x)≤1; rw [show ∀ b:Cover, x-b-x= -b from fun _=> by abel]; simp [Laurent.size,apply_ite Int.natAbs]

def tap {r : ℕ} (T: Tile (edgeL G) (r+1)) := fun v:chain (edgeL G) (r+1)=> riverP (v 0).2.2 (v 0).1 T (Fin.tail v)
-- undecl `r`
lemma tap_up {T:Tile (edgeL G) (m+1)}(h:Up T): Up (tap T):= by
    intro x v; simp only [tap,Function.comp_apply,Lotus.tint_fst,Lotus.tint_snd,riverP,Finset.sum_apply]; apply Finset.sum_congr rfl;intro k _; simp only [Pi.sub_apply,shed];congr 1
    · rw [← h x (Fin.cons ((v 0).1,k,(v 0).2.2) (Fin.tail v))]; rw [Fin.comp_cons]; rfl
    rw [←h x (Fin.cons (backwards (v 0).1 k,k,(v 0).2.2) (Fin.tail v)), Fin.comp_cons]; rw [show backwards ((v 0).1+x) k=backwards (v 0).1 k+x by unfold backwards; abel];rfl

def Authorized (T: Pot G) := ∀ z x e r, ∑ a∈Finset.antidiagonal e,cruisesD z x a r T=0
lemma authoritative {T: Pot G}{M: Row (TypeFace 2) (TypeFace 2)}(h:Story T M):Authorized T:=fun z=> storied z h
lemma authorized_sub {T U:Pot G}(h:Authorized T)(e:Authorized U): Authorized (T-U):= by
   intro z x i r
   have hf {m n}{T U:Tile (edgeL G) m}(e:m=n): lengthen e (T-U)=lengthen e T-lengthen e U := by cases e; rfl
   have hp {m}{X Y:Tile (edgeL G) m}: sand (X-Y)=sand X-sand Y := by ext v;simp only [sand, Pi.sub_apply, Finset.sum_sub_distrib, sub_div]
   -- polym issue V
   have he a b v l : shapeD z v l a b (T-U)=shapeD z v l a b T-shapeD z v l a b U:= by
      unfold shapeD; rw [← Finset.sum_sub_distrib];apply Finset.sum_congr rfl; intro t _; rw [plaster,plaster,plaster,←smul_sub, ←hf,←hp];congr 3;ext;simp [clutch,shed,sub_mul]
   have hh a : cruisesD z x a r (T-U)= cruisesD z x a r T-cruisesD z x a r U:= by unfold cruisesD; rw [← Finset.sum_sub_distrib];apply Finset.sum_congr rfl;intro j _;rw [he,he];abel
   simp_rw [hh]; rw [Finset.sum_sub_distrib,h z x i r,e z x i r,sub_zero]
lemma revenue (G : Gauge)(e n)(hs:0≤η):∃ C:ℝ,0<C ∧ ∀ T: Pot G, Authorized T → Agate (T e (n+1)) → Up (T e (n+1)) → ∀ B,0≤B → (∀ j<e,∀ i,1 ≤ i→ i≤n+1 → Bail (fame _) η (T j i) B) → Bail (fame _) η (tap (T e (n+1))) (C*B) := by
    let S:=(Finset.antidiagonal e).erase (e,0)
    choose A Ha H using fun k=> mount_hull G k n hs
    let w (a:hue G) := ∑ k∈S,A k a
    let C:= ∑ a,w a
    have he a : 0≤w a:=Finset.sum_nonneg fun k _=>Ha k a; have hx:0≤C:=Finset.sum_nonneg fun i _=>he i
    let d:ℝ:= (n+1:ℕ); have hd:0<d:=by unfold d; positivity
    let L:=|-d⁻¹| * C; let M:= (Fintype.card (Stationary.Loc G 1):ℝ)*L
    refine ⟨max 1 M,lt_max_of_lt_left one_pos,fun T ht h' hY B hb hK=>?_⟩
    have hg (v:edgeL G): Knoxville (fame _) η v (shed (tap (T e (n+1))) v) (L*B):= by
       let a:=v.2.2
       have hz:=ht a v.1 e n; rw [←Finset.add_sum_erase _ _ (a:= (e,0)) (by simp), cruise_head a T e h'] at hz
       let U:=∑ k∈S,cruisesD a v.1 k n T
       have hw:d • shed (tap (T e (n+1))) v= -U:= by
           rw [show shed (tap (T e (n+1))) v= riverP a v.1 (T e (n+1)) from funext fun z=>by unfold a; simp only [shed,tap,Fin.cons_zero,Fin.tail_cons]];exact eq_neg_of_add_eq_zero_left hz
       have hy: shed (tap (T e (n+1))) v= (-d⁻¹) • U:= by rw [neg_smul, ←smul_neg, ←hw, ←mul_smul,inv_mul_cancel₀ hd.ne',one_smul]
       have hl: Knoxville (fame _) η v U (w a*B):= by
            unfold U w; rw [Finset.sum_mul]; apply knox_sum; intro i hi; have ht:=Finset.ne_of_mem_erase hi; have hv:= Finset.mem_antidiagonal.mp (Finset.mem_of_mem_erase hi); exact H _ a _ _ _ B (hK _ (by rcases i; simp at *; omega)) hb
       rw [hy]; apply (hl.smul _).mono; unfold L; rw [←mul_assoc]; apply mul_le_mul_of_nonneg_right _ hb; exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (f:=w) (fun a _=>he a) (Finset.mem_univ _)) (abs_nonneg _)
    apply (from_stud (tap_up hY) (by unfold L; positivity) hg).mono; rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_right ..) hb
end YM.FormalBulk08.Rift
