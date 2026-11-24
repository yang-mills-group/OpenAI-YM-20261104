import YM.FormalBulk08.Lotus.Dust

noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Lotus
open Lava Gorge Lattice Laurent Filter Set Function
open scoped BigOperators Classical ENNReal Topology
variable {r : ℕ} {I : Type*} {C : Type*} [AddCommGroup C]
def tint (c : C) : C × I ≃ C × I := Equiv.prodCongr (Equiv.addRight c) (Equiv.refl I)
@[simp] lemma tint_fst (c : C) (a : C × I) : (tint c a).1=a.1+c := rfl
@[simp] lemma tint_snd (c : C) (a : C× I) : (tint c a).2=a.2:=rfl
def Up (T : Tile (C×I) r) := ∀ c:C,∀ v:chain (C×I) r, T (tint c ∘ v)=T v
lemma Up.add {T S : Tile (C×I) r} (h : Up T) (g : Up S) : Up (T+S) := by intro x v; rw [Pi.add_apply,Pi.add_apply,h,g]
lemma Up.sub {T S : Tile (C×I) r} (h : Up T) (g : Up S) : Up (T-S) := by intro x v; rw [Pi.sub_apply,Pi.sub_apply,h,g]
lemma Up.smul {T : Tile (C×I) r} (h : Up T) (a : ℝ) : Up (a • T) := by intro x v; rw [Pi.smul_apply,Pi.smul_apply,h]
lemma Up.sums {T : C → Tile (C×I) r} (h : ∀ i,Up (T i)) (F : Finset C) : Up (∑ i∈F,T i) := by intro x v; simp_rw [Finset.sum_apply]; exact Finset.sum_congr rfl fun i _=> h i _ _
variable (i : Fin r) (n : Side)
abbrev Picks (x : Biglot I) (v : chain (Tor n I) r) := {w: chain (Biglot I) r // w i=x ∧ drip n ∘ w=v}

def vat (x : Biglot I) (T : Tile (Biglot I) r) (v : chain (Tor n I) r) := ∑' w:Picks i n x v,T w.val
-- nonzero rank periodization only; connect to rooted sums by peeling
lemma drip_tint (x : Cover) (v : Biglot I) : drip n (tint x v)= tint (wrap n x) (drip n v):= by ext <;> simp [drip,map_add]
def twin (x : Biglot I) (v : chain (Tor n I) r) (y : Cover): Picks i n x v≃ Picks i n (tint y x) (tint (wrap n y) ∘ v) where
   toFun w := ⟨tint y ∘ w.val, by simp only [comp_apply,w.property.1,true_and]; funext j; rw [comp_apply,comp_apply,comp_apply,drip_tint]; exact congr_arg (tint (wrap n y)) (congr_fun w.property.2 j)⟩
   invFun w:=⟨(tint y).symm ∘ w.val, by
       simp only [comp_apply,w.property.1,Equiv.symm_apply_apply,true_and]; funext j; apply (tint (wrap n y)).injective; rw [comp_apply,comp_apply,←drip_tint,Equiv.apply_symm_apply]; exact congr_fun w.property.2 j⟩
   left_inv w:= Subtype.ext (funext fun j=> Equiv.symm_apply_apply ..)
   right_inv w:= Subtype.ext (funext fun j=> Equiv.apply_symm_apply ..)
lemma vats (x : Biglot I) (v : chain (Tor n I) r) (y : Cover) {T : Tile (Biglot I) r} (h : Up T) :
    vat i n (tint y x) T (tint (wrap n y) ∘ v) = vat i n x T v := by
   unfold vat; rw [←Equiv.tsum_eq (twin i n x v y)]; exact tsum_congr fun w=>h y w.val
lemma twins (x y : Biglot I) (v : chain (Tor n I) r) {T : Tile (Biglot I) r} (ht : Up T) (h : drip n x=drip n y) : vat i n x T v=vat i n y T v := by
   symm; have h₁ : wrap n x.1=wrap n y.1 := congr_arg Prod.fst h; have h₂:(drip n x).2=(drip n y).2:= congr_arg Prod.snd h
   let b:=y.1-x.1
   have he: tint b x = y := Prod.ext (by simp [b]) h₂
   have hh : tint (wrap n b) ∘ v=v := funext fun j=>by ext <;> simp [b,map_sub,h₁]
   have hj:=vats i n x v b ht; rw [he,hh] at hj; exact hj

def cum (T : Tile (Biglot I) r) : Tile (Tor n I) r:= fun v=> vat i n (boil n (v i)) T v
lemma cum_near {T : Tile (Biglot I) r} (h : Up T) (v : chain (Tor n I) r) (x : Biglot I) (e : drip n x=v i) : cum i n T v=vat i n x T v :=
    twins i n _ _ _ h (by rw [e,drip_boil])
lemma Up.stir {T : Tile (Biglot I) r} (h : Up T) : Up (cum i n T):=by
   intro x v
   rw [cum_near i n h (tint x ∘ v) (tint (Lattice.lift x) (boil n (v i))) (by simp [drip_tint])];
   have he:=vats i n (boil n (v i)) v (Lattice.lift x) h; rw [wrap_lift] at he;exact he
end YM.FormalBulk08.Lotus
