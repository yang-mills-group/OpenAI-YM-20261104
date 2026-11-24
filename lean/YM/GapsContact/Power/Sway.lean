import YM.GapsContact.Power.Reserve
import YM.Pert.Scale.Engineering
/-!
# Free reading geometry

Tie through ``≤ d`` to engineering weights. Don't pretend it's a homogeneous frame
on the physical side. Pay grade mixing via quotient identities. This is what
measuring frames all inherit.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GapsContact.Power
open Function Filter Set MeasureTheory Analysis Table Extraction Spec Push.FiniteDetection.Free OPE.Levy Ascent
open Labels Pert Pert.Position Pert.Scale Extra.FD Maxwell RawLabels
open scoped Topology BigOperators Classical NNReal InnerProductSpace
variable {G:Gauge}(C: Family G) {d e n:ℕ}{r s:ℝ}
set_option quotPrecheck false
local notation "K" => C.labels
local notation "H" => Maxwell.Free.hierarchy C.labels
local notation "S" => Climb.Bel C.book
local notation "P" => Maxwell.Free.scheme C.labels
local notation "O" => Maxwell.Free.phase_orientation C.labels
local notation "I" => Maxwell.Free.scheme_filters C.labels

abbrev Rise0 (d:ℕ) := Up (P) d

def setGear (d:ℕ)(ratio:ℝ):= gear C.labels d ratio

-- common reference acts; adapt Gear basis; essential use alignment through exact weights
lemma ahead (t u : ℝ)(x:(S).Field d):setGear C d t (setGear C d u x)=setGear C d (t*u) x:=by
  let B:=recorded C.labels d
  unfold setGear
  rw [← B.b.sum_equivFun x]; simp only [map_sum,map_smul,rare, Complex.ofReal_mul,mul_pow,mul_smul]
  apply Finset.sum_congr rfl; intro i _; rw [smul_comm ((u:ℂ)^(B.w i).1) ((t:ℂ)^(B.w i).1)]
lemma ahead_one (x:(S).Field d): setGear C d 1 x=x:=by unfold setGear; rw [←motor_bank (K) x 1,bank_origin];change x+(0:Position.operator C.labels d) x=_; rw [_root_.zero_apply,add_zero]
lemma ahead_inv (hr:r≠0)(x:(S).Field d): setGear C d r (setGear C d r⁻¹ x)=x:=by rw [ahead,mul_inv_cancel₀ hr,ahead_one]
lemma ahead_onto (hr:r≠0): Bijective (setGear C d r):=by
   have he(x:(S).Field d): setGear C d r⁻¹ (setGear C d r x)=x:=by rw [ahead,inv_mul_cancel₀ hr,ahead_one]
   exact ⟨(show LeftInverse (setGear C d r⁻¹) (setGear C d r) from he).injective,fun x=> ⟨_,ahead_inv C hr x⟩⟩
lemma ahead_adj (x:(S).Field d): setGear C d r ((S).adj (H).spin d timeAxis x)=(S).adj (H).spin d timeAxis (setGear C d r x):=by
   let K0:=Signed.mirror timeAxis
   change gear C.labels d r ((S).mirror (H).spin d K0 ((S).conj (H).spin d x))=(S).mirror (H).spin d K0 ((S).conj (H).spin d (gear C.labels d r x))
   simp_rw [show ∀ x:(S).Field d,(S).mirror (H).spin d K0 x=rideO C.labels K0.ortho d x from Rigid.wear_ride _ _]
   rw [←gear_spin]; apply congr_arg; exact (gear_conj C.labels x r).symm
lemma ahead_pair (hr:0<r)(x y:(S).Field d): valTwo (S) d (r • detectors) (setGear C d r x) (setGear C d r y)= valTwo (S) d detectors x y:=by
   have he:= points_equ detectors_in (![x,y] : Fin 2→E C.labels d) hr.ne'; unfold valTwo
   rw [show (![_,_] : Fin 2→ E C.labels d)=(fun i : Fin 2=> gear C.labels d r (![x,y] i)) from ?_]; swap; funext i; fin_cases i<;> rfl
   exact he
lemma ahead_cost (hr:0<r)(x:(S).Field d): chip (H) d r (setGear C d r x)=chip (H) d 1 x:=by unfold chip; rw [one_smul,← ahead_adj C,ahead_pair C hr]
lemma good_blue (d:ℕ)(hr:0<r): Good H d r:=by
   intro x hx; obtain ⟨y,rfl⟩:=(ahead_onto (d:=d) C hr.ne').surjective x
   have hp:y≠0:=fun h=> hx (h.symm ▸ map_zero _); rw [ahead_cost C hr,chip,one_smul]; exact Real.sqrt_pos.mpr (norm_pos_iff.mpr (show valTwo (S) d _ _ _≠0 from fun ht=>(free_positive (C:=C) d y hp).ne' (congr_arg Complex.re ht)))

lemma prograde {x:(S).Field (d+1)} (hp:x∈LinearMap.range (Rise0 C d)): setGear C (d+1) r x∈ LinearMap.range (Rise0 C d):=by
   have hh:LinearMap.range (Rise0 C d)= lower (K) d (d+1):= SetLike.ext' (by rw [← stairs_eq, upward (K) (Nat.le_succ d) _ (I)])
   rw [hh] at hp ⊢; exact gear_lower _ x hp _
lemma graded_lower (B:RStage (K) d)(i: Fin (B.m+1)) (he:(B.w i).1 ≤ e)(hu:e ≤ d): B.b i∈LinearMap.range ((P).rise hu):=by
   obtain ⟨j,h⟩:= B.corners i; let Y:=(C.labels.level d)
   let w:=(Y.grades j).1
   have hw : w=(B.w i).1 := by
      refine MvPolynomial.IsWeightedHomogeneous.inj_right (φ:=writes C.labels d (B.b i)) ?_ ?_ (B.weighs i)
      · exact fun he => B.b.ne_zero i ((writes_inj C.labels d) (he.trans ((writes C.labels d).map_zero.symm)))
      intro v hv; exact congrArg Prod.fst ((weight_collapse v).symm.trans ((at_alcove C.labels d j) (h ▸ hv)))
   let x:= Y.basis j; let y:= enroll C.labels d x
   have hy: B.b i=y:= h
   rw [←SetLike.mem_coe, ← upward C.labels hu P (I), hy]
   refine ⟨x,rfl,?_,x.property.2⟩
   apply (MvPolynomial.mem_restrictSupport_iff ℂ).mpr
   intro b hb; change height b ≤e
   have hp := (pure_grade _ _ |>.mp (Y.pure j)) (MvPolynomial.mem_support_iff.mp hb)
   have hi: height b =w:= congrArg Prod.fst ((weight_slot b).symm.trans hp); exact hi.trans_le (hw.trans_le he)

lemma gear_grade (t:ℝ)(x:(S).Field (d+1)):
    setGear C (d+1) t x- t^(d+1) • x∈LinearMap.range (Rise0 C d) := by
   let B:=recorded C.labels (d+1)
   rw [← (B.b).sum_equivFun x,map_sum,Finset.smul_sum,← Finset.sum_sub_distrib]
   apply Submodule.sum_mem; intro i _
   rw [map_smul, show setGear C _ _ (B.b i)=_ from rare B i t,← Complex.coe_smul]; simp only [Complex.ofReal_pow, ← mul_smul]
   rcases lt_or_eq_of_le (B.cap i) with hx|hx
   · exact (LinearMap.range (Rise0 C d)).sub_mem ((LinearMap.range _).smul_mem _ (graded_lower C B i (by omega) (Nat.le_succ d))) ((LinearMap.range _).smul_mem _ (graded_lower C B i (by omega) (Nat.le_succ d)))
   rw [hx,mul_comm ((t:ℂ)^(d+1)), sub_self]; exact Submodule.zero_mem _ -- order

lemma gear_sip (hr:0<r)(x:(S).Field (d+1)): sip H P d r (setGear C (d+1) r x)=sip H P d 1 x :=by
   let g:=setGear C (d+1) r
   let f:=setGear C (d+1) r⁻¹
   have he := good_blue C d hr; have he':=good_blue C d (r:=1) one_pos
   let z:=f (ridge H P d r (g x)); let y:=ridge H P d 1 x
   refine le_antisymm ?_ ?_
   · change sip H P d r (g x) ≤ chip H (d+1) 1 y
     rw [← ahead_cost C hr]; refine le_trans (sip_leaves H P I O hr he (x:=g x) (y:=g y) ?_|>.le) (sip_le H P I O hr he _);
     rw [← map_sub]; apply prograde C; unfold y; rw [ridged,sub_sub_cancel]; exact ⟨_,rfl⟩
   change chip H (d+1) 1 y ≤ chip H (d+1) r _
   rw [show ridge H P d r (setGear C (d+1) r x)=setGear C (d+1) r z from (ahead_inv C hr.ne' _).symm, ahead_cost C hr]
   have ht:sip H P d 1 x=sip H P d 1 z:=by
      apply sip_leaves H P I O one_pos he'
      unfold z
      rw [ridged,map_sub, show f (g x)=x from (show _ from ?_),sub_sub_cancel]
      · exact prograde (d:=d) C ⟨_,rfl⟩
      unfold f g; rw [ahead,inv_mul_cancel₀ hr.ne',ahead_one]
   exact ht.le.trans (sip_le H P I O one_pos he' z)
lemma sip_gain (hr:0<r)(x:(S).Field (d+1)): r^(d+1)*sip H P d r x = sip H P d 1 x:=by
    rw [← gear_sip C hr, sip_leaves H P I O hr (good_blue C d hr) (gear_grade C _ x), sip_smul H P, Real.norm_of_nonneg (pow_pos hr _|>.le)]
end YM.GapsContact.Power
