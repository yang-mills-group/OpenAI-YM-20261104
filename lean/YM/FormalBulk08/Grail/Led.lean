import YM.FormalBulk08.Grail.Star

/-! Augmentation Tap in mark norm. No width change for an
irrelevant input; only on strict Ward arrows, before block prescription.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Grail
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G : Gauge}{I V:Type*}{η σ A C : ℝ}{n r k u:ℕ}{W:Reach V}{x:V}
lemma delay (U : Reach V)(v v' x:V)(h : U.d v v'≤1)(hs:0≤η): Real.exp (-η*U.d v x)≤Real.exp η * Real.exp (-η*U.d v' x):= by
    rw [←Real.exp_add]; apply Real.exp_monotone; have hy: U.d v' x≤1+U.d v x:= by apply le_trans (U.tri v' v x); rw [U.turn v' v];omega
    have hx : ((U.d v' x:ℕ):ℝ)≤1+U.d v x:= by exact_mod_cast hy
    nlinarith
lemma plaza (p:Loc G 1)(i:hue G)(w:Loc G 1)(l:Bool)(hs:η≤σ)(he:0≤η)(a:diagD n)(k):∃ B:ℝ,0≤B ∧ ∀ Z:Tile (edgeL G) (a.val.1+1),∀ C:ℝ, Knoxville (fame _) σ (0,p) Z C→∀ z x:Cover,∀ v: Loc G 1,
   (fame _).d (z,w) (x,v) ≤1 → Knoxville (fame _) η (x,v) (plaster i (z,w) l k a Z) (B*Real.exp (-(σ-η)*size x)*C):= by
   obtain ⟨K,hK,H⟩:= ash_pledge G w l k _ i (η:=η)
   let R:ℝ:=|(↑(a.val.1+1:ℕ):ℝ)|; let B:=R*Real.exp η * K*Real.exp (σ-η)
   have hR:0≤R:=abs_nonneg _
   refine ⟨B,by unfold B; positivity,fun Z C hC z x v u=>?_⟩
   let U:=fame (Loc G 1)
   have hz:U.d (x,v) (0,p)=size x:=by simp [U,fame,capD]
   have hk:= delay U (z,w) (x,v) (0,p) u (sub_nonneg.mpr hs); rw [hz] at hk
   have ht:=knox_clasp (penn_slice (z,w) hs he hC |>.mono (mul_le_mul_of_nonneg_right hk hC.1)) (H z) he (x,v)
   apply ((ht.polish.rename (Finset.mem_antidiagonal.mp a.property)).smul ((a.val.1+1:ℕ):ℝ)).mono
   let y:=Real.exp η; let t:=Real.exp (σ-η)*Real.exp (-(σ-η)*size x)*C; change R* (Real.exp _ * (t*K)) ≤ _; have hp:= ht.1
   have hh : Real.exp (η*(U.d (z,w) (x,v))) ≤ y:= by unfold y; apply Real.exp_monotone; exact mul_le_of_le_one_right he (by exact_mod_cast u)
   have hx:=hC.1; have hE:0≤t:= by unfold t; positivity
   refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hh (mul_nonneg hE hK)) hR).trans_eq ?_;unfold t y B; ring

lemma apt (b i:Loc G 1)(k:ℕ×ℕ)(r:ℕ)(hs:η ≤ σ)(he:0≤η): ∃ B:ℝ,0≤B ∧ ∀ T:Pot G,∀ C:ℝ,0≤C → (∀ v,1 ≤ v→ v≤ r+1→ Knoxville (fame _) σ (0,b) (T k.1 v) C) → ∀ x:Cover, Knoxville (fame _) η (x,i) (cruisesD i.2 x k r T) (B*Real.exp (-(σ-η)*size x)*C):= by
    choose W hW H using fun (w:Loc G 1)(l:Bool)(p:diagD r)=>plaza b i.2 w l hs he p k.2
    let X w l:= ∑ p∈(Finset.antidiagonal r).attach,W w l p
    have hx w l:0≤ X w l:=Finset.sum_nonneg fun p _=> hW w l p
    refine ⟨∑ w,(X w true+X w false), Finset.sum_nonneg (fun w _=> add_nonneg (hx w true) (hx w false)),fun T C hc hp x=>?_⟩
    have hh w z l (hy:(fame _).d (z,w) (x,i)≤1): Knoxville (fame _) η (x,i) (shapeD i.2 (z,w) l k r T) (X w l* Real.exp (-(σ-η)*size x)*C):= by
       unfold shapeD X; simp_rw [Finset.sum_mul]; refine knox_sum _ fun t _=> H _ _ t _ _ (hp _ (by omega) (by have :=Finset.mem_antidiagonal.mp t.property;omega)) z x i hy
    unfold cruisesD; simp_rw [Finset.sum_mul, add_mul]; refine knox_sum _ fun z _=> (hh z x true ?_).add (hh z (backwards x z.1) false ?_)
    · change size (x-x) ≤ 1;simp [Laurent.size]
    change size ((x-_)-x)≤1; rw [show ∀ b:Cover, x-b-x= -b from fun _=> by abel]; simp [Laurent.size,apply_ite Int.natAbs]

lemma marker_print (a: Loc G 1) (e r:ℕ)(hA:2*η < σ)(hp:0≤η):∃ C:ℝ,0≤C ∧ ∀ V: Pot G,Authorized V → Agate (V e (r+1)) → ∀ B,0≤B → (∀ j<e,∀ v, 1≤v → v ≤ r+1 → Knoxville (fame _) σ (0,a) (V j v) B) → Knoxville (fame _) η (0,a) (tap (V e (r+1))) (C*B):= by
    have hθ:=sub_pos.mpr hA
    let D:=fame (Loc G 1); let R:=(Finset.antidiagonal e).erase (e,0)
    choose C hC H using fun (i:Loc G 1)(t:ℕ×ℕ)=> apt a i t r (show η≤σ by linarith) hp
    let L:ℝ:=(r+1:ℕ); let W i:= |-L⁻¹| * ∑ t∈R,C i t
    let M:=∑ i,W i; have hW i:0≤W i:=mul_nonneg (abs_nonneg _) (Finset.sum_nonneg (fun t _=>hC i t))
    have hM: 0≤M:= Finset.sum_nonneg (fun i _=>hW i)
    let Z : ℝ:=∑' x:edgeL G, Lotus.coast (σ-2*η) x
    have hZ:0≤Z:= tsum_nonneg fun i=>(Real.exp_pos _).le
    let u:edgeL G:= (0,a)
    refine ⟨Z*M,mul_nonneg hZ hM,fun V hV hx B hb hv=>?_⟩
    let f v:=M*Real.exp (-(σ-η)*(size (v:edgeL G).1))*B
    have hL:0<L:= by unfold L; positivity
    apply penn_pile u hp (tap (V e (r+1))) f _ _ (by positivity); swap
    · let c t : ℝ:=Lotus.coast (σ-2*η) (t:edgeL G)*(M*B)
      have he t: Gorge.shine η (D.d t u)* ENNReal.ofReal (f t)=ENNReal.ofReal (c t):= by
         have hv:D.d t u=size t.1:=by simp only [D,u,fame,capD,sub_zero]
         rw [hv,Gorge.shine,←ENNReal.ofReal_mul (Real.exp_pos _).le]; congr 1
         unfold c f Lotus.coast
         rw [show -(σ-2*η)*↑(size t.1)= η *↑(size t.1)+ (-(σ-η)* (size t.1)) by ring,Real.exp_add]; ring
      change (∑' v,Gorge.shine η (D.d v u)*_ ) ≤ _
      simp_rw [he]; rw [←ENNReal.ofReal_tsum_of_nonneg]; rotate_left
      · intro v; exact mul_nonneg (Real.exp_pos _).le (mul_nonneg hM hb)
      · exact (coast_sum hθ).mul_right _
      unfold c; rw [tsum_mul_right]; apply le_of_eq; unfold Z; rw [mul_assoc]
    rintro ⟨x,w⟩
    let U:=∑ t∈R,cruisesD w.2 x t r V; let k:=-(σ-η)*size x
    have hh:=hV w.2 x e r; rw [←Finset.add_sum_erase _ _ (a:= (e,0)) (by simp), cruise_head w.2 V _ hx] at hh
    have hg:L • Lava.shed (tap (V e (r+1))) (x,w)= -U:= by rw [show Lava.shed (tap _) _= riverP w.2 x (V e (r+1)) from funext fun v=>by simp only [Lava.shed,tap,Fin.cons_zero,Fin.tail_cons]]; exact eq_neg_of_add_eq_zero_left hh
    have he: Knoxville D η (x,w) U ((∑ t∈R,C w t)*Real.exp k*B):= by
       unfold U; simp_rw [Finset.sum_mul]; refine knox_sum _ fun i hi=> H w i _ B hb (hv i.1 (by have he:=Finset.mem_antidiagonal.mp (Finset.mem_of_mem_erase hi); have ht:=Finset.ne_of_mem_erase hi; by_contra hg; apply ht; exact Prod.ext (by dsimp;omega) (by dsimp;omega))) x
    rw [show Lava.shed (tap (V e (r+1))) (x,w)= -L⁻¹ • U from (by rw [neg_smul,←smul_neg,←hg,←mul_smul,inv_mul_cancel₀ hL.ne',one_smul])]; apply (he.smul _).mono;change _ ≤ M * Real.exp k * B; simp_rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Finset.single_le_sum (f:=W) (fun i _=> hW i) (Finset.mem_univ w)) (Real.exp_pos _).le) hb
end YM.FormalBulk08.Grail
