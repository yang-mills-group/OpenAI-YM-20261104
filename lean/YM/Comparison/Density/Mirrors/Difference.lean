import YM.Comparison.Density.Mirrors.Profile
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-! # Elimination by a fourth-box-difference

Full interior is the *only* pattern with four independent positions.
Count with every duplication caused by reflection. No jets/formal physics
in this counting operation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Density.Mirrors
open Function Lattice Finset
open scoped BigOperators

private lemma pair_of (k : Side) (z : ℤ) (hl : -(k.val:ℤ)≤z) (hp : z ≤ k.val) :
    (univ.filter fun x : Per (quad k) => wave k x=z)= {(z : Per _),((2*(k.val:ℤ)-z:ℤ) : Per _)} := by
  ext x; simp only [mem_filter,mem_univ,true_and,mem_insert,mem_singleton]
  constructor
  · intro h; simpa only [h] using wave_period k x
  rintro (rfl|rfl)
  · exact wave_core k z hl hp
  rw [wave_upper k _ (by omega) (by omega),sub_sub_cancel]

private lemma twice_wave (k : Side) (z : ℤ) (hl : -(k.val:ℤ)<z) (hu : z<k.val) :
    (univ.filter fun x : Per (quad k) => wave k x=z).card = 2 := by
  rw [pair_of k z hl.le hu.le,card_insert_of_notMem _,card_singleton]
  intro h
  have hh:= (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ (quad k).val).1 (mem_singleton.mp h)
  change ((↑(4*k.val):ℤ) ∣ 2*(k.val:ℤ)-z-z) at hh
  push_cast at hh
  have he:= Int.le_of_dvd (show 0 < 2*(k.val:ℤ)-z-z by omega) hh
  omega

private lemma endpoint_lower (k : Side) :
    (univ.filter fun x : Per (quad k) => wave k x= -(k.val:ℤ)).card=1 := by
  have he : (((4*k.val:ℕ):ℤ):Per (quad k))=0 := by change ((↑(quad k).val:ℤ) : Per (quad k))=0; simp [Per]
  rw [pair_of k _ le_rfl (by omega),show 2*(k.val:ℤ)- (-(k.val:ℤ))= -(k.val:ℤ)+(↑(4*k.val):ℤ) by push_cast; ring]
  rw [Int.cast_add,he]; simp

private lemma endpoint_upper (k : Side) :
    (univ.filter fun x : Per (quad k) => wave k x=(k.val:ℤ)).card=1 := by
  rw [pair_of k _ (by omega) le_rfl,show 2*(k.val:ℤ)-(k.val:ℤ)=(k.val:ℤ) by ring]
  simp

def bill (r k : Side) : Wall r → ℝ
  | none=>2*(2*((k.val:ℝ) - r.val) + 1)
  | some (_,d)=> if d.val=0 then 1 else 2

private lemma counter (r k : Side) (hr : r.val≤k.val) (s : Wall r) :
    ((univ.filter fun i => shade r k i=s).card : ℝ)=bill r k s := by
  have hp : 0<r.val:= r.property
  cases s with
  | none=>
    let l : ℤ:= -(k.val:ℤ)+r.val; let h : ℤ:= (k.val:ℤ)-r.val
    have hj : ∀ i : ℤ, i ∈ Icc l h → -(k.val:ℤ) < i ∧ i < k.val := by
      intro i hi; have H:= mem_Icc.mp hi; dsimp only [l,h] at H; omega
    have hx : (univ.filter fun i => shade r k i=none).card=(Icc l h).card*2 := by
      rw [show (univ.filter fun i=>shade r k i=none)=(univ.filter fun i=>wave k i∈Icc l h) by ext; simp only [mem_filter,shade_none,l,h,mem_Icc],← sum_card_fiberwise_eq_card_filter]
      rw [← sum_congr rfl (show ∀ i∈ Icc l h,(2:ℕ)=(univ.filter fun j=> wave k j=i).card from
        fun i hi=> (twice_wave k i (hj i hi).1 (hj i hi).2).symm),sum_const, smul_eq_mul]
    rw [hx,Int.card_Icc]
    have he : (↑(h+1-l).toNat:ℤ)=h+1-l:=by dsimp [l,h]; omega
    change ((↑((h+1-l).toNat * 2):ℝ))=_
    rw [Nat.cast_mul, ← Int.cast_natCast,he]
    dsimp only [bill,l,h]; push_cast; ring
  | some u=>
    obtain ⟨d,b⟩:=u
    have hb:= b.isLt
    cases d
    · rw [bill]
      simp_rw [shade_false]
      split
      · rename_i h; rw [h,Nat.cast_zero,add_zero,endpoint_lower,Nat.cast_one]
      rw [twice_wave _ _ (by omega) (by omega),Nat.cast_ofNat]
    simp_rw [shade_true r k hr]; rw [bill]; split
    · rename_i h; rw [h,Nat.cast_zero,sub_zero,endpoint_upper,Nat.cast_one]
    rw [twice_wave _ _ (by omega) (by omega),Nat.cast_ofNat]

def bill4 (r k : Side) (s : Sky r) : ℝ := ∏ i, bill r k (s i)

lemma counter4 (r k : Side) (hr : r.val≤k.val) (s : Sky r) :
    ((univ.filter fun x : Site (quad k)=> sky r k x=s).card:ℝ)=bill4 r k s := by
  let H (i : Axis) : Finset (Per (quad k)):= univ.filter fun j => shade r k j=s i
  have h : (univ.filter fun x : Site (quad k) => sky r k x = s)= Fintype.piFinset H := by
    ext x; rw [Fintype.mem_piFinset,mem_filter]
    simp only [H,funext_iff,sky,Function.comp_apply,mem_univ,true_and,mem_filter]
  rw [h,Fintype.card_piFinset,Nat.cast_prod]
  exact prod_congr rfl fun i _=> counter r k hr (s i)

def advance (k : Side) (j : Fin 5) : Side := ⟨k.val+j.val,Nat.add_pos_left k.property j.val⟩

def multiplier (j : Fin 5) : ℝ := (![1,-4,6,-4,1] j : ℝ) / (256*24)

private lemma line (A B : Axis → ℝ) (x : ℝ) :
    (∑ j : Fin 5, multiplier j * ∏ i : Axis, (A i * (x+j.val)+ B i))=(1/256)*∏ i, A i := by
  simp [Axis, multiplier,Fin.sum_univ_succ, Fin.prod_univ_succ]
  ring

private lemma cancelled (r k : Side) (e : Sky r) :
    ∑ j : Fin 5, multiplier j * bill4 r (advance k j) e= if e=fun _=>none then 1 else 0 := by
  let A i : ℝ:= if e i=none then 4 else 0
  let B i : ℝ:= bill r k (e i)- A i*k.val
  unfold bill4
  have ht i j : bill r (advance k j) (e i)=A i * ((k.val:ℝ)+j.val)+B i := by
    dsimp only [A,B]
    cases he:e i with
    | none=>
      rw [if_pos rfl,bill,bill,show (advance k j).val = k.val+j.val from rfl]; push_cast; ring
    | some u=>
      obtain ⟨a,b⟩:=u; rw [bill,bill]; simp
  simp_rw [ht]
  rw [line A B]; split
  · rename_i h; rw [show A=fun _=>4 from by unfold A; simp [h]]; norm_num [Axis]
  rename_i h
  rw [funext_iff] at h; push Not at h
  obtain ⟨i,hi⟩:=h
  rw [prod_eq_zero (mem_univ i) (if_neg hi : A i=0),mul_zero]

lemma eliminated (r k : Side) (hr : r.val≤k.val) (w : Sky r → ℝ) :
    ∑ j : Fin 5, multiplier j * (∑ x, w (sky r (advance k j) x))= w (fun _=>none) := by
  have he j : (∑ x,w (sky r (advance k j) x))=∑ i, bill4 r (advance k j) i * w i := by
    rw [← sum_fiberwise']
    apply sum_congr rfl; intro i _
    rw [sum_const,nsmul_eq_mul,counter4 r (advance k j) (hr.trans (Nat.le_add_right _ _)) i]
  simp_rw [he,mul_sum,← mul_assoc]; rw [sum_comm]; simp_rw [← sum_mul,cancelled]
  simp
end YM.Comparison.Density.Mirrors
