import YM.FormalBulk08.Cork.Quit

/-! Detect all Rank2 valuations. Color factor separately. Hessian convention.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Cork
open Reef Lava Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 PowerSeries
open Lotus Shore Mesa Gorge City
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G : Gauge}

structure Splendid (T : Slopes G) : Prop where
    fares : Purse T
    gradient : Grad T
    worn : Sworn T
    up : Up T
    symmetric : Agate T
    stain : Lust T
lemma splendid {T : Pot G} {R : Row (TypeFace 2) (TypeFace 2)}(h:Story T R)(j): Splendid (T j 2):= ⟨h.fare _ _,directP h j,named h _ _ (by decide),h.civil _ _,h.agate _ _,colorful h _ _ (by decide)⟩
lemma splendid_sub {T S : Slopes G}(h:Splendid T)(e: Splendid S): Splendid (T-S):= by
    refine ⟨?_,?_,?_,?_,h.symmetric.sub e.symmetric,?_⟩
    · obtain ⟨s,A,hs,hp⟩:=h.fares; obtain ⟨t,B,ht,he⟩:=e.fares; exact ⟨min s t,A+B,lt_min hs ht,(hp.shrink (min_le_left ..)).sub (he.shrink (min_le_right ..))⟩
    · intro a b; have he: riverP a b (T-S) = riverP a b T-riverP a b S:= by
         unfold riverP; rw [←Finset.sum_sub_distrib];refine Finset.sum_congr rfl fun i _=>?_ ;ext; simp only [Pi.sub_apply,shed];ring
      rw [he,h.gradient,e.gradient,sub_zero]
    · intro s w; rw [Pi.sub_apply,Pi.sub_apply,h.worn s w,e.worn s w,sub_mul]
    · intro z w; rw [Pi.sub_apply,Pi.sub_apply,h.up z w,e.up z w]
    intro g u; simp only [Pi.sub_apply,sub_mul,Finset.sum_sub_distrib]; rw [h.stain g u,e.stain g u]
lemma splendid_smul {T : Slopes G}(h:Splendid T)(k:ℝ): Splendid (k • T):= by
    refine ⟨?_,?_,?_,?_,h.symmetric.smul _,?_⟩
    · obtain ⟨s,A,hs,h⟩:= h.fares; exact ⟨s,_,hs,h.smul k⟩
    · intro a b; have he: riverP a b (k • T)=k • riverP a b T:= by unfold riverP; rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro j _;rw [smul_sub];rfl
      rw [he,h.gradient,smul_zero]
    · intro s w; rw [Pi.smul_apply,Pi.smul_apply,h.worn s w,smul_eq_mul,smul_eq_mul,mul_assoc]
    · intro z w; rw [Pi.smul_apply,Pi.smul_apply,h.up z w]
    intro g u;simp only [Pi.smul_apply,smul_eq_mul,mul_assoc,←Finset.mul_sum];rw [h.stain g u]

variable {T : Slopes G}(h: Splendid T)
include h
lemma moniker (a:Axis)(i j : hue G) : mir T a a i j a a=0 := by
    have he:=cash_grad h.gradient h.fares (ch a^3) ((Pad.ch a).pow _) a i j
    rw [Finset.sum_eq_single a] at he
    · rw [show frow (ch a^3) a= (3:ℝ) • (ch a*ch a)+(3:ℝ) • ch a + 1 by ext;simp [frow,ch];ring] at he
      rw [add_net h.fares a a i j ((((Pad.ch a).mul (Pad.ch a)).smul (3:ℝ)).add ((Pad.ch a).smul (3:ℝ))) (show Pad (1:Cover→ℝ) from flat_pad 1),add_net h.fares a a i j (((Pad.ch a).mul (Pad.ch a)).smul _) ((Pad.ch a).smul _),smul_net,smul_net, direct_line h.gradient h.worn h.up h.fares,direct_zero h.gradient h.fares] at he
      change net T a a i j _=0;linarith only [he]
    · intro w _ hu; rw [show frow (ch a ^3) w=0 by ext; simp [frow,ch,Ne.symm hu]]; simp [net]
    simp
lemma monarch (a b : Axis)(hb:a≠b)(i j:hue G): 2*mir T a b i j a b + mir T b b i j a a=0 := by
    let f:= ch a*ch a*ch b
    have hf:=cash_grad h.gradient h.fares f (((Pad.ch a).mul (Pad.ch a)).mul (Pad.ch b)) b i j
    rw [←Finset.sum_subset (Finset.subset_univ {a,b}) ?h,Finset.sum_pair hb] at hf
    · have he: frow f a= (2:ℝ) • (ch a * ch b)+ch b:= by ext; simp [frow,f,ch,Ne.symm hb];ring
      have H: frow f b = ch a*ch a:=by ext; simp [f,ch,frow,hb];ring
      rw [he,H,add_net h.fares a b i j (((Pad.ch a).mul (Pad.ch b)).smul _) (Pad.ch b),smul_net,direct_line h.gradient h.worn h.up h.fares,add_zero] at hf; exact hf
    case h=> intro x _ hx; simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hx;rw [show frow f x=0 by ext; simp [frow,f,ch,Ne.symm hx.1,Ne.symm hx.2]]; simp [net]
lemma tag_rule (a b:Axis)(hb:a≠b)(i j:hue G)(p q:Axis)(hq : p≠q): mir T a a i j b b=mir T p p i j q q := by
   let r:= Equiv.swap a p; let t:= r.trans (Equiv.swap (r b) q); have ha: t a=p := by
       unfold t; rw [Equiv.trans_apply,show r a=p from Equiv.swap_apply_left ..]; exact Equiv.swap_apply_of_ne_of_ne (fun e=>hb (r.injective ((Equiv.swap_apply_left a p).trans e))) hq
   let s : Signed:= ⟨t,fun _=>false⟩; have he:= turn_mir h.gradient h.worn h.up h.fares a a i j b b s; rw [show s.perm a=p from ha,show s.perm b=q from Equiv.swap_apply_left ..] at he; simpa [s,banner] using he.symm

-- Mirror selection with sign flips. Assumes every diagonal color choice zero.
lemma all_caps (hp:∀ a b i j, a≠b → mir T a a i j b b=0)(a b : Axis)(i j:hue G)(u v : Axis): mir T a b i j u v=0 := by
   have he (p : Axis) := turn_mir h.gradient h.worn h.up h.fares a b i j u v (s:=⟨1,fun k=>decide (k=p)⟩)
   let x:=mir T a b i j u v
   have H (p : Axis): x=(if a=p then -1 else 1)*(if b=p then -1 else 1)*(if u=p then -1 else 1)*(if v=p then -1 else 1)*x := by simpa only [x,banner,Equiv.Perm.one_apply,decide_eq_true_eq] using he p
   unfold x at H
   by_cases ha:a=b
   · subst a; by_cases hh:u=v
     · subst v; by_cases h':u=b
       · subst u; exact moniker h ..
       exact hp b u i j (Ne.symm h')
     have hz:=H v;rw [if_neg hh,if_pos rfl] at hz;split_ifs at hz <;> linarith only [hz]
   by_cases hu:u=v
   · subst v; have hz:= H a; rw [if_pos rfl,if_neg (Ne.symm ha)] at hz;split_ifs at hz <;> linarith only [hz]
   by_cases h':u=a ∨ u=b
   · by_cases h'':v=a ∨ v=b
     · rcases h' with h1|h1 <;> rcases h'' with h2|h2 <;> subst u <;> subst v
       · contradiction
       · have he:= monarch h a b ha i j; rw [hp b a i j (Ne.symm ha)] at he; linarith only [he]
       · have he:= monarch h a b ha i j; rw [hp b a i j (Ne.symm ha)] at he; rw [mir,mul_comm (ch b),←mir];linarith only [he]
       contradiction
     have hh:=H v; rw [if_pos rfl,if_neg hu,if_neg (fun e=>h'' (Or.inl e.symm)),if_neg (fun e=>h'' (Or.inr e.symm))] at hh;linarith only [hh]
   have hh:=H u; rw [if_pos rfl,if_neg (Ne.symm hu),if_neg (fun e=>h' (Or.inl e.symm)),if_neg (fun e=>h' (Or.inr e.symm))] at hh;linarith only [hh]

-- transitivity
lemma shift_hem (a i j v) : hem T a a i j v=hem T a a j i (-v) := by
   rw [hem, ← h.symmetric _ (Equiv.swap (0:Fin 2) 1), hem, ←h.up (-v)]; congr 1; ext1 k; fin_cases k <;> simp [Lotus.tint]
lemma invert_hem (a i j w): mir T a a i j w w=mir T a a j i w w:=by
   rw [mir,net,mir,net,←Equiv.tsum_eq (Equiv.neg Cover) (fun v=>hem T a a j i v*(ch w*ch w) v)]; apply tsum_congr; intro v; rw [shift_hem h a i j v]; simp [ch]
end YM.FormalBulk08.Cork
