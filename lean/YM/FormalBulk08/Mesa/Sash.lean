import YM.FormalBulk08.Mesa.Sponge

/-! Dictionary for finite port stencils on cover, permits coincident ports. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Mesa
open Lava Gorge Shore Lattice Laurent Filter Function Lotus Orb Wick
open scoped Topology ENNReal BigOperators Classical
variable {r : ℕ} {I V U : Type*}
variable {C : Type*} [AddCommGroup C]
-- one necklace at absolute positions, all translates

def Pendant (w v : chain (C × I) r) : Prop := ∃ z:C, v=tint z ∘ w
theorem pendant_iff (w v : chain (C×I) r) (i : Fin r) : Pendant w v ↔ v=tint ((v i).1-(w i).1) ∘ w := by
   refine ⟨?_,fun h=>⟨_,h⟩⟩; rintro ⟨z,rfl⟩; simp

def ribbon (w : chain (C×I) r) (a : ℝ) : Tile (C×I) r := fun v=> if Pendant w v then a else 0
lemma follows (w v : chain (C×I) r) (x:C) : Pendant w v ↔ Pendant w (tint x ∘ v) := by
   constructor
   · rintro ⟨y,rfl⟩; use y+x;ext <;> simp [add_assoc]
   rintro ⟨y,h⟩; use y-x; ext j
   · have e := congr_arg Prod.fst (congr_fun h j);simp at *; grind -- potential bad
   · have e:=congr_arg Prod.snd (congr_fun h j); simp only [Function.comp_apply, tint_snd] at *;exact e
lemma up_ribbon (w : chain (C × I) r) (a : ℝ) : Up (ribbon w a) := by intro x v; simp only [ribbon,← follows]
-- Width bound
lemma necklaces (w : chain (Biglot I) r) (a : ℝ) (σ : ℝ) : Bail (fame I) σ (ribbon w a) (Real.exp (σ * wide (fame I) w) * ‖a‖) := by
   refine ⟨by positivity,fun i x=>?_⟩
   by_cases e : x.2=(w i).2
   · let b:=x.1-(w i).1
     let v : pack i x :=⟨tint b ∘ w,Prod.ext (by simp [b]) e.symm⟩
     have hv (j : pack i x) : Pendant w j.val ↔ j=v := by
        rw [pendant_iff _ _ i,j.property]; change j.val=v.val ↔ _; exact Subtype.ext_iff.symm
     rw [tsum_eq_single v]; swap
     · intro u hu; simp only [glitter,ribbon,hv u, if_neg hu,enorm_zero,mul_zero]
     unfold glitter; rw [show ribbon w a v.val=a from if_pos ((hv v).mpr rfl)]; unfold v; unfold shine wide; simp only [comp_apply,fame,tint_fst,capD,add_sub_add_right_eq_sub];rw [←ofReal_norm,←ENNReal.ofReal_mul (Real.exp_pos _).le] -- le
   have hx (v:pack i x) : ribbon w a v.val=0 := if_neg (by intro h; obtain ⟨b,hb⟩:=h; apply e; exact ((congr_arg Prod.snd v.property).symm.trans (by have ht:=congr_arg Prod.snd (congr_fun hb i);simpa using ht)))
   simp_rw [glitter,hx,enorm_zero,mul_zero,tsum_zero]; exact zero_le
lemma wrap_ribbon (w : chain (Biglot I) r) (a : ℝ) (n : Side) (i : Fin r) : cum i n (ribbon w a)=ribbon (drip n ∘ w) a := by
   funext v
   let W:= Picks i n (boil n (v i)) v
   have h (t:W) : Pendant w t.val → Pendant (drip n ∘ w) v := by
      rintro ⟨b,hb⟩; use wrap n b; funext j;exact (congr_fun t.property.2.symm j).trans (by rw [comp_apply,congr_fun hb,comp_apply,drip_tint];rfl)
   unfold cum vat; by_cases e : Pendant (drip n ∘ w) v
   · let z := (boil n (v i)).1-(w i).1
     have hx: v=tint ((v i).1-((drip n (w i)).1)) ∘ (drip n ∘ w):= (pendant_iff (drip n ∘ w) v i).mp e
     have ht:tint z (w i)=boil n (v i):= Prod.ext (by simp [z]) (by change (w i).2=(v i).2; exact congr_arg Prod.snd (congr_fun hx.symm i))
     have hg : drip n ∘ tint z ∘ w = v := by
         have he : wrap n z=(v i).1-(drip n (w i)).1:= by simp [z,drip,boil];
         exact Eq.trans (funext fun j=> by rw [comp_apply,comp_apply,drip_tint,he]; exact rfl) hx.symm
     let u : W:=⟨tint z ∘ w,ht,hg⟩
     change (∑' b:W,ribbon w a b.val)=_; rw [tsum_eq_single u]
     · exact (show ribbon w a u.val=a from if_pos ⟨z,rfl⟩).trans (if_pos e).symm
     intro t ht; exact if_neg (fun g=> ht (Subtype.ext (by have he:= (pendant_iff _ _ i).mp g; rw [t.property.1] at he;exact he)))
   rw [show ribbon _ _ v=_ from if_neg e]; have hv (p:W) : ribbon w a p.val=0:=if_neg (fun hp=> e (h p hp)); change (∑' p:W,ribbon w a p.val)=_;simp_rw [hv,tsum_zero]

lemma threaded (v w : chain (C × I) r) (s : Equiv.Perm (Fin r)) : Pendant (w ∘ s) (v ∘ s) ↔ Pendant w v := by
   refine ⟨?_,?_⟩
   · rintro ⟨z,h⟩; use z; funext i; simpa [comp_apply] using congr_fun h (s.symm i)
   rintro ⟨z,rfl⟩; exact ⟨z,rfl⟩

variable [Fintype V]
def deploy (R : V→ C × I) (T : Tile V r) := ∑ v: chain V r,ribbon (R ∘ v) (T v)
lemma parade (R : V→ C×I) (T : Tile V r) : Up (deploy R T) := up_sums _ _ (fun _ _=> up_ribbon _ _)
lemma polished (R : V→ C × I) {T : Tile V r} (h : Agate T) : Agate (deploy R T):= by
   intro v s;simp_rw [deploy,Finset.sum_apply]; symm; refine Fintype.sum_equiv (Equiv.arrowCongr s.symm (Equiv.refl _)) _ _ fun w=>?_
   unfold ribbon; change _= if Pendant ((R ∘ w) ∘ s) (v ∘ s) then T (w ∘ s) else 0; simp only [h w s,threaded]
lemma obeys (R : V→ Biglot I) (T : Tile V r) (σ) : Bail (fame I) σ (deploy R T) (∑ v:chain V r, Real.exp (σ*wide (fame I) (R ∘ v))*‖T v‖) := bail_many _ _ _ fun v _=> necklaces (R ∘ v) _ _
lemma deploy_void (R : V → C × I) (r : ℕ) : deploy R (0 : Tile V r)=0 := by funext; simp [deploy,Finset.sum_apply,ribbon]
lemma deploy_fold (R : V → Biglot I) (T : Tile V r) (n : Side) (i : Fin r) : cum i n (deploy R T)=deploy (drip n ∘ R) T := by
   unfold deploy; rw [cum_sums _ _ _ _ (C:=fun v=>_) (fun v _=>necklaces _ _ 0) (show (0:ℝ)≤0 from le_rfl)]
   simp_rw [wrap_ribbon]; rfl
end YM.FormalBulk08.Mesa
