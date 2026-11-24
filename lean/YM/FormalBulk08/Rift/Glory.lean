import YM.FormalBulk08.Wine.Toon

/-! Absolute charges with all-real lanes & potentials. Reseating root when
the other legs symmetric not needed. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Rift
open Reef Lava Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 PowerSeries
open Lotus Shore Mesa Gorge City Cork
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G : Gauge} {I J V : Type*}{η C : ℝ} {n : ℕ} {D : Reach V} (a:V)

def Knoxville (D : Reach V) (η : ℝ)(x: V) (T : Tile V n)(C:ℝ) : Prop := 0 ≤ C ∧ (∑' v:chain V n,Gorge.shine η (wide D (Fin.cons x v : chain V (n+1)))*‖T v‖ₑ) ≤ ENNReal.ofReal C

lemma Knox_zeros : Knoxville D η a (0:Tile V n) 0:=⟨le_rfl,by simp⟩
variable {a}
lemma Knoxville.mono {T:Tile V n}(h:Knoxville D η a T C){B:ℝ}(hb:C≤B):Knoxville D η a T B:= ⟨h.1.trans hb,h.2.trans (ENNReal.ofReal_le_ofReal hb)⟩
lemma Knoxville.add {T S:Tile V n}(h: Knoxville D η a T C){B:ℝ}(e:Knoxville D η a S B):Knoxville D η a (T+S) (C+B):= by
    refine ⟨add_nonneg h.1 e.1,?_⟩; rw [ENNReal.ofReal_add h.1 e.1];refine le_trans ?_ (add_le_add h.2 e.2); rw [←ENNReal.tsum_add];apply ENNReal.tsum_le_tsum;intro v;rw [←mul_add]; exact mul_le_mul_right (enorm_add_le _ _) _
lemma Knoxville.smul {T:Tile V n}(h: Knoxville D η a T C)(b:ℝ): Knoxville D η a (b • T) (|b| *C):= by
    refine ⟨mul_nonneg (abs_nonneg b) h.1,?_⟩; rw [ENNReal.ofReal_mul (abs_nonneg _)]; refine le_trans ?_ (mul_le_mul_right h.2 _); rw [←ENNReal.tsum_mul_left]; apply ENNReal.tsum_le_tsum; intro v; rw [Pi.smul_apply,smul_eq_mul,enorm_mul,←Real.norm_eq_abs, ofReal_norm,mul_left_comm]
lemma knox_sum (B:Finset I) {T:I→Tile V n}{K:I→ℝ}(h:∀ i∈B,Knoxville D η a (T i) (K i)): Knoxville D η a (∑ i∈B,T i) (∑ i∈B,K i):= by
    induction B using Finset.induction with
    | empty=> simp only [Finset.sum_empty];apply Knox_zeros
    | @insert i B hi h'=> rw [Finset.sum_insert hi,Finset.sum_insert hi]; exact (h i (Finset.mem_insert_self ..)).add (h' fun j hj=> h j (Finset.mem_insert_of_mem hj))
lemma Knoxville.polish {T:Tile V n}(h: Knoxville D η a T C):Knoxville D η a (sand T) C:= by
    let X:= Equiv.Perm (Fin n); let u:ℝ:=Fintype.card X;have hu:0<u := by change (0:ℝ)< (Fintype.card _ : ℝ);positivity
    let U (s : X) (v:chain V n):=T (v ∘ s);
    have ht (s:X): Knoxville D η a (U s) C:= by
       refine ⟨h.1,le_trans ?_ h.2⟩; apply le_of_eq
       let g: X := s; let f : Equiv.Perm (chain V n):=Equiv.arrowCongr g.symm (Equiv.refl _)
       rw [← Equiv.tsum_eq f (fun v=>Gorge.shine η (wide D (Fin.cons a v : chain V (n+1))) * ‖T v‖ₑ)]; refine tsum_congr fun v=> ?_
       let V1: chain V (n+1):= Fin.cons a v;let V2:chain V (n+1):= Fin.cons a (f v)
       let r : Equiv.Perm (Fin (n+1)):= ⟨Fin.cases 0 (fun i=>Fin.succ (s i)), Fin.cases 0 (fun i=>Fin.succ (s.symm i)),(fun i=>by cases i using Fin.cases <;> simp; exact s.symm_apply_apply _),fun i=>by cases i using Fin.cases <;> simp; exact s.apply_symm_apply _⟩
       have he: V2= V1 ∘ r := by ext1 i;cases i using Fin.cases with
                       | zero=> simp [V1,V2,r]
                       | succ i=> simp only [V1,V2,r, Fin.cons_succ,comp_apply,Equiv.coe_fn_mk,Fin.cases_succ]; rfl -- `cons` issue
       change Gorge.shine η (wide D V1)* ‖U s v‖ₑ = Gorge.shine η (wide D V2)* _;rw [he,wide_turn];rfl
    have hh: sand T= ∑ s:X,u⁻¹ • U s := by funext i;simp only [sand,Finset.sum_apply,Pi.smul_apply,smul_eq_mul, ← Finset.mul_sum,U];rw [div_eq_mul_inv,mul_comm]
    rw [hh]; apply (knox_sum Finset.univ (fun i _=>(ht i).smul u⁻¹)).mono; simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ,abs_of_pos (inv_pos.mpr hu)]; change u*(u⁻¹ * C)≤ C; rw [←mul_assoc,mul_inv_cancel₀ hu.ne',one_mul]
lemma Knoxville.rename {T:Tile V n}(h: Knoxville D η a T C){m : ℕ}(e:n=m):Knoxville D η a (lengthen e T) C:=by cases e; exact h
lemma from_stud [Fintype I] {T:Tile (Biglot I) (n+1)}(h:Up T)(hx:0≤C)(hp:∀ a, Knoxville (fame I) η a (shed T a) C): Bail (fame I) η T ((Fintype.card I:ℝ)*C) := by
   refine ⟨mul_nonneg (Nat.cast_nonneg _) hx,fun i a=> ?_⟩
   let f : pack i a→ I×chain (Biglot I) n := fun u=> let x:=(u.val 0).1; ((u.val 0).2, Fin.tail (Lotus.tint (-x) ∘ u.val))
   let base (x:I):Biglot I:=(0,x)
   have hg (u: pack i a): Fin.cons (base (f u).1) (f u).2 = (Lotus.tint (-(u.val 0).1)) ∘ u.val := by
      ext1 k; cases k using Fin.cases
      · apply Prod.ext <;> simp [base,f]
      · rfl
   have hh: Injective f := by
      intro u v he; have ht: Lotus.tint (-(u.val 0).1) ∘ u.val=Lotus.tint (-(v.val 0).1) ∘ v.val:= by rw [←hg,←hg,he]
      have hy: -(u.val 0).1= -(v.val 0).1:= by
          apply add_left_cancel (a:=a.1); have hh:=congr_arg Prod.fst (congr_fun ht i);simp only [Function.comp_apply, Lotus.tint_fst] at hh; nth_rw 1 [u.property] at hh; -- modifies all?
          convert hh using 1; rw [v.property]
      rw [hy] at ht;exact Subtype.ext (funext fun k=>(Lotus.tint _).injective (congr_fun ht k))
   let D:=fame I; let U (p : I × chain (Biglot I) n):= glitter D η T (Fin.cons (base p.1) p.2)
   have he: (∑' v,U v)≤ ENNReal.ofReal ((Fintype.card I:ℝ)*C) := by
      rw [ENNReal.tsum_prod',tsum_fintype]; refine (Finset.sum_le_sum (fun x _=>show (∑' v, glitter D η T (Fin.cons (base x) v : chain (Biglot I) (n+1)))≤ _ from (hp (base x)).2)).trans_eq ?_; simp [ENNReal.ofReal_mul (Nat.cast_nonneg _)]
   apply le_trans (b:=∑' v:pack i a,U (f v)) ?_ ((ENNReal.tsum_comp_le_tsum_of_injective hh U).trans he); apply le_of_eq; refine tsum_congr fun v=> ?_; unfold U; rw [hg]; simp [glitter,wide,D,fame,capD,h ..] -- h .. issue
end YM.FormalBulk08.Rift
