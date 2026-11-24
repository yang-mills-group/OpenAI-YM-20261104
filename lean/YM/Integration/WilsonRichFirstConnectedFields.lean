import YM.Integration.WilsonRichFirstConnectedMoments
import YM.Integration.WilsonRichContinuumTree

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRichFirstConnectedFields
open Function Set Finset Maxwell Maxwell.Wick Labels Extra.FD
open MS MS.Local.Physical MS.Land MS.Book MS.Rake MS.Dial MS.Fleet
open scoped Classical BigOperators

variable {G : Gauge} {B : Deck G} {A : Booked B}

theorem tree_zero (v : Rake.Label B) (hp : 0<v.h) :
    Maxwell.Wick.moment G (0:Points 1) (fun _ => Maxwell.reduceEq (Milk.Lightning v))=0 := by
  have hx : (0:Points 1) ∈ conf 1 := fun i j _ => Subsingleton.elim i j
  have h := Pert.Scale.rising_moment hx (fun _ : Fin 1 => WilsonRichContinuumTree.degree v)
    (show (2:ℝ)≠0 by norm_num)
  rw [MultilinearMap.map_smul_univ,smul_eq_mul] at h
  simp only [smul_zero,prod_const,Finset.card_univ,Fintype.card_fin,pow_one,
    Complex.ofReal_ofNat] at h
  have hn : (2:ℂ)^v.h≠1 := by
    exact_mod_cast (ne_of_gt (one_lt_pow₀ (by norm_num : 1<(2:ℝ)) hp.ne'))
  have hh : ((2:ℂ)^v.h-1)*Maxwell.Wick.moment G (0:Points 1)
      (fun _ => Maxwell.reduceEq (Milk.Lightning v))=0 := by
    rw [sub_mul,one_mul,h,sub_self]
  exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hn)

theorem singleton (M : MS_Data G A) (p : Fin 2 → Rake.Label B) (u : ℝ)
    {x : Fin 2 → MS.Tone.QP} (hx : Injective x) (i : Fin 2) (hp : 0<(p i).h) :
    book M p u x {i} 0=0 := by
  let v : Fin 1 → Rake.Label B := fun _ => p i
  let y := (0:Points 1)
  let X : Fin 1 → MS.Tone.QP := fun k => Theater.out (y k)
  have hy : y ∈ conf 1 := fun a b _ => Subsingleton.elim a b
  have hX : Injective X := fun {a b} _ => Subsingleton.elim a b
  have had := Dial.highest_zero M u y v hy
  change Puff.Mom.bouquet (book M v u X) univ 0=_ at had
  rw [WilsonRichFirstConnectedMoments.single] at had
  have hunit : (univ:Finset (Fin 1))={0} := by decide
  rw [hunit] at had
  change Vane.blade (spine M v u X {0} 0) ()=_ at had
  rw [(pin M v u hX).2.1 0] at had
  change Vane.blade (spine M p u x {i} 0) ()=_
  rw [(pin M p u hx).2.1 i]
  exact had.trans (tree_zero (p i) hp)

theorem joined (M : MS_Data G A) (p : Fin 2 → Rake.Label B) (u : ℝ)
    {x : Fin 2 → MS.Tone.QP} (hx : Injective x) (hp : ∀i,0<(p i).h) :
    Dial.tour M p u x univ 1=Vane.blade (spine M p u x univ 1) () := by
  have h0 : book M p u x ∅=0 := by
    funext j
    change Vane.blade (spine M p u x ∅ j) ()=0
    rw [(pin M p u hx).1]
    exact (allow_zero ()).2
  change Puff.Mom.bouquet (book M p u x) univ 1=_
  rw [WilsonRichFirstConnectedMoments.pair _ h0,singleton M p u hx 0 (hp 0),
    singleton M p u hx 1 (hp 1),zero_mul,mul_zero,add_zero,add_zero]

end YM.Integration.WilsonRichFirstConnectedFields
