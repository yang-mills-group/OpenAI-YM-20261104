import YM.FormalOPE.RG10.Shutters.Lamp
/-! Exact parity for each regulator. At the common top lattice no center tolerance needed. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalOPE.RG10.Shutters
open Function Maxwell Labels Extraction Filter Finset Extra.FD PertExtension MeasureTheory
  Topology Metric PertExtension.Position PertExtension.Physical PowerSeries Triangle Matrix
  InversionTop Orb Chart LatticePT RG10.Position Mixed
open scoped Topology BigOperators ContDiff Classical
variable {I Q :Type*} {G:Gauge}{F: Frames G}{d n:ℕ}(q:ℕ+)(m:ℕ)(P:Plan F)
section Word
variable [Fintype I] (v:I→ LatticePT.Word G)
local notation "e" => epsilon q m
include q m
lemma preserve_sign (k:ℕ)(y:I→Native q m)(z:Native q m)(t:Mixed.Task v)(h:Odd (k+∑ i,((v i).F.grades (v i).axis).2)) :
 diagonalWith (tray G) (restrictedO (placements v q m z y t)) (Mixed.number v t+k)=0 := by
 by_cases hh : Odd (Mixed.number v t+k)
 · exact normalized_odd (traySpec G) (side_even q m) _ hh
 have ht : ∃ i,Odd (((v i).F.grades (v i).axis).2 + ((v i).F.grades (t i)).2) := by
   by_contra! hw
   have he: lapse (S:=ℝ) (∑ i,((v i).F.grades (v i).axis).2) = lapse (Mixed.number v t):= by
     unfold lapse Mixed.number; rw [← prod_pow_eq_pow_sum,← prod_pow_eq_pow_sum]; exact prod_congr rfl (fun i _=>lap_twist (hw i))
   have hu:= congr_arg (fun x:ℝ=> lapse (S:=ℝ) k * x) he; unfold lapse at hu; simp_rw [← pow_add] at hu; rw [h.neg_one_pow, Nat.not_odd_iff_even.mp (by rw [add_comm]; exact hh) |>.neg_one_pow] at hu; norm_num at hu
 obtain ⟨i,he⟩:=ht; have hf : (v i).cost (t i) e=0:= by rw [LatticePT.Word.cost,LatticePT.even_slot _ _ _ _ _ _ he,mul_zero]
 have hg:= RG10.Position.paidOut (side_even q m) v (fun i=>y i+z) (epsilon q m) t; let w:=∏ i,(v i).cost (t i) e; have hw : w=0:= Finset.prod_eq_zero (mem_univ _) hf
 dsimp only at hg; rw [show (∏ i,(v i).cost (t i) e)=0 from hw,Complex.ofReal_zero,map_zero (PowerSeries.C), show outside (X:=Unit × Dir G (LatticePT.side q m)) 0=0 from rfl,zero_mul,FlatFeed.step,mul_zero, show (feed (side_even q m) (G:=G)).average 0 = 0 from by
  ext i : 1; rw [FlatFeed.average_coeff,show row (X:=Unit × Dir G (LatticePT.side q m)) i 0=0 from funext (by intro x; simp [row]),FlatFeed.mean_zero,map_zero],zero_mul] at hg
 have H:= congr_arg (coeff k) hg
 rw [map_zero,lower,coeff_mk,into_coeff,coeff_mk] at H; exact Complex.ofReal_injective H

theorem faithful (k:ℕ) (Ψ:(I→E4)→ℝ)(h: Odd (k+∑ i,((v i).F.grades (v i).axis).2)) : polynomialTop v q m Ψ k=0:= sum_eq_zero fun _ _=> sum_eq_zero fun _ _=> sum_eq_zero fun i _=> mul_eq_zero_of_right _ (preserve_sign q m v _ _ _ i h)
end Word

local notation "r" => PertExtension.Physical.Profile.n
local notation "w"=> Deck.slots F d
local notation "ℳ" => Mark (Deck F d) PertExtension.Physical.Profile.n
lemma begins_even (v:ℳ)(k:ℕ)(h : Odd (k+ slots r w v)): coeff k (P.begins q m d v)=0 := by
 unfold Plan.begins prelude; rw [map_sum]; apply sum_eq_zero; intro i _; rw [coeff_C_mul,coeff_mk]; refine mul_eq_zero_of_right _ (faithful q m _ k _ ?_)
 have he (j): (F.level ((Deck.token F d ∘ v.2) j).1).grades (i j).val=(_,w (v.2 j)) := (i j).property
 change Odd (k+∑ j, ((F.level ((Deck.token F d ∘ v.2) j).1).grades (i j).val).2)
 simp_rw [he]; exact h
lemma begins_snooze : snooze r w (P.begins q m d)= P.begins q m d:= by
 funext i; apply PowerSeries.ext; intro k; change (fun i=>coeff k (snooze r w (P.begins q m d) i)) i= _; rw [glance]; unfold glow
 rw [Pi.smul_apply,smul_eq_mul, ← mul_assoc]; simp only [lapse,←pow_add]; by_cases h: Odd (k+slots r w i)
 · rw [begins_even q m P i k h, mul_zero]
 rw [(Nat.not_odd_iff_even.mp h).neg_one_pow,one_mul]

include P
lemma intake (hq:1<q.val) (v:ℳ) : glow r w (Physical.free (L:=Maxwell.standard F) (deck F d)) v= Physical.free (L:=Maxwell.standard F) (deck F d) v:= by
 have hh:= Plan.starts hq P v; refine tendsto_nhds_unique (hh.const_mul (lapse (slots r w v)) |>.congr' ?_) hh
 filter_upwards with m
 have hv:= congr_arg (coeff 0) (congr_fun (begins_snooze (d:=d) q m P) v); let A:= P.begins q m d; rw [show coeff 0 _= _ from congr_fun (glance r w A 0) v] at hv;
 simpa only [lapse,pow_zero,one_smul,glow, coeff_zero_eq_constantCoeff_apply] using hv
end YM.FormalOPE.RG10.Shutters
