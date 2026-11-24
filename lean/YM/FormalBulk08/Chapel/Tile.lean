import YM.FormalBulk08.Chapel.Wiring

noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Chapel
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 PowerSeries Next.Free RG Precision
open Lotus Shore Mesa Gorge City Cork Rift Lava
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G : Gauge}{σ B C : ℝ}{m r:ℕ}{L : Side}{I J : Type}

lemma height_none {A: Type}[Fintype A](p: Grades A) (h:upper p=0): p=0:= by
    ext x; have he: p x ≤ upper p := Finset.single_le_sum (f:=p) (fun k _=> Nat.zero_le _) (Finset.mem_univ x); exact Nat.eq_zero_of_le_zero (h ▸ he)
lemma growth_cloak {A:Type}[Fintype A](p:Grades A)(h:0<upper p):∃ i:A,∃ q,p=q+grain i ∧ upper p=upper q+1 := by
   obtain ⟨i,hi⟩: ∃ i:A,p i≠0:= Function.ne_iff.mp (show p≠(0 : Grades A) from fun he=>by simp [he,upper] at h)
   let q:= p-grain i; have hv:p=q+grain i:= by ext j;by_cases he:i=j <;> first|subst j;simp [q,grain];omega|simp [q,grain,Ne.symm he]
   exact ⟨i,q,hv,hv ▸ upper_push q i⟩
lemma grain_one {A:Type}[Fintype A](i:A)(v:Wand A): hat (grain i) v=curveW i v:= by
   rw [hat,Finset.prod_eq_single i]; swap;· intro j _ hj;simp [grain,hj]
   swap;· simp
   simp [grain,curveW]
lemma grain_two {A:Type}[Fintype A](i j:A)(v:Wand A):
   hat (grain i+grain j) v=if i=j then (curveW i v * curveW i v-curveW i v)/2 else curveW i v*curveW j v:= by
   by_cases he:i=j
   · subst j; rw [hat,if_pos rfl,Finset.prod_eq_single i];swap;· intro j _ hj;simp [grain,hj]
     swap;· simp
     rw [Pi.add_apply, show grain i i=1 by simp [grain],rise_hat (v i:ℝ) 1]; simp [curveW];ring
   rw [if_neg he,hat,← Finset.prod_subset (Finset.subset_univ {i,j}) ?h,Finset.prod_pair he];simp [grain,he, Ne.symm he,curveW]
   case h=> intro x _ hx;simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hx; simp [grain,hx.1,hx.2]

def duct : Cover≃ cloud 1 where
   toFun v:= v ∘ Prod.snd
   invFun w:= rack w 0
   left_inv _:=rfl
   right_inv w:= by ext ⟨i,j⟩;fin_cases i;rfl
lemma null_price {T:Tile (edgeL G) 2}(hs:0<σ) (hp:Agate T) (hz:Up T) (h:Null T) (H:Bail (fame _) σ T C)(t:chain (Stationary.Loc G 1) 1)(x:edgeL G)(p:Grades (Fin 1 × Axis))(he:upper p≤2): piles T x t p=0 := by
   let U := t 0; let k:= axisEquiv.symm U.1;let a:=axisEquiv.symm x.2.1;let i:=U.2;let j:= x.2.2
   have hh (v:Cover): rowC T x t (duct v)=hem T k a i j v := by
       unfold rowC; rw [← hp _ (Equiv.swap (0:Fin 2) 1), ←hz (-x.1),hem];congr 1; ext1 b;fin_cases b <;> simp [snake, show ∀ i: Fin 1, rack (duct v) i=v from fun _=>rfl]
       · apply Prod.ext; simp
         exact Prod.ext (axisEquiv.apply_symm_apply _).symm rfl
       apply Prod.ext; simp
       exact Prod.ext (axisEquiv.apply_symm_apply _).symm rfl
   rw [piles,←Equiv.tsum_eq duct];simp_rw [hh]; let F:= hat p ∘ duct
   change Cork.net T k a i j F=0; unfold F
   by_cases ht:upper p=0
   · rw [height_none p ht,show (hat (0:Grades (Fin 1×Axis)) ∘ duct)=1 by funext; simp [hat]]; exact h.bottom ..
   obtain ⟨⟨l,b⟩,u,h1,hu⟩:=growth_cloak p (Nat.pos_of_ne_zero ht); subst p
   by_cases hu':upper u=0
   · rw [height_none u hu',zero_add,show hat (grain (l,b)) ∘ duct=ch b from funext fun v=>grain_one ..]; exact h.air ..
   obtain ⟨⟨m,z⟩,y,hy,hz⟩:=growth_cloak u (Nat.pos_of_ne_zero hu'); have h':y=0:= height_none y (by omega); rw [hy,h',zero_add]
   have hk: Purse T:= ⟨_,_,hs,H⟩
   by_cases e:(m,z)=(l,b)
   · rw [←e,show hat (grain (m,z)+grain (m,z))∘duct=(1/2:ℝ) • (ch z * ch z) + (-1/2:ℝ) • ch z from ?H]; rw [add_net hk _ _ _ _ (((Pad.ch z).mul (Pad.ch z)).smul _) ((Pad.ch z).smul _),smul_net,smul_net,←mir,h.water,h.air];ring
     case H=> ext v; rw [comp_apply,grain_two,if_pos rfl];change (ch z v*ch z v- ch z v)/2=(1/2:ℝ)*(ch z v*ch z v)+(-1/2:ℝ)* ch z v;ring
   rw [show hat (grain (m,z)+grain (l,b))∘duct=ch z * ch b from funext fun v=> (grain_two _ _ (duct v)).trans (if_neg e)]; exact h.water k a i j z b

def Valed (T: Tile (edgeL G) m):= (∀ h:m=2, Null (lengthen h T))
-- use cost_row H with width `sigma` for tap (can adapt with h0)
lemma curtain_owed (r m:ℕ) (hm:1≤m) (hd:r≤4-m) (G:Gauge)(hs:0<σ): ∃ K:ℝ,0≤K∧∀ B C:ℝ,∀ T:Tile (edgeL G) (m+1), Up T → Agate T → Bail (fame _) σ T C → Bail (fame _) σ (tap T) B → Valed T →∀ x t p,p∈trimmed _ r → |piles T x t p| ≤ K*B:= by
   by_cases h:m=1
   · subst m; refine ⟨0,le_rfl,fun B C T hT ha H hh hp x t p hv=>?_⟩
     rw [null_price hs ha hT (hp rfl) H t x p (by have :=(trim_def ..).mp hv;omega),abs_zero,zero_mul]
   choose! F hF H using (fun p (he:p∈trimmed (Fin m×Axis) r) => route_price p hs (show upper p<m by have := (trim_def ..).mp he;omega) G)
   refine ⟨∑ p∈trimmed (Fin m×Axis) r,F p, Finset.sum_nonneg (fun i hi=>(hF i hi).le),fun B C T _ ha ht hb _ x t p hp=>?_⟩
   exact (H p hp _ _ T ha B hb C ht).trans (mul_le_mul_of_nonneg_right (Finset.single_le_sum (f:=F) (fun i hi=> (hF i hi).le) hp) hb.1)
end YM.FormalBulk08.Chapel
