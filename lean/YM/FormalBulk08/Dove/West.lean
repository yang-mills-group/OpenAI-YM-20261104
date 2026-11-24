import YM.FormalBulk08.Aster.Regal

/-! Prepaid bulk vacuum. Head prices at mesh J with exponential width in that mesh.
Any L later. Width order chosen all-stage a priori. Keep collision work separate. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Dove
open Lattice Laurent Bloch Exterior RG Precision Wilson Orb Reef City Filter Function Series Wick Jets Stationary Lotus Shore Lava Gorge Mesa Cork Wine Flat Glide Bank Work.F08 Next.Free Chapel Rift Aster
open scoped Topology ENNReal BigOperators Classical
variable {G:Gauge}{K:KernelChoices}{j l E:ℕ}{σ C :ℝ}
-- head price common for all advertised E
structure Flax (G:Gauge)(k:ℝ)(j E:ℕ)(σ C:ℝ) :Prop where
    plus:0<C
    width:0<σ
    price: Teller G σ C
    seat: ∀ W:Train j, Bail (fame _) σ (setkin G (pink k W)) C
    seed: ∀ e≤ E,∀ r≤ e+2,Bail (fame _) σ (Enter G e r) C
    rate: ∀ A:Levels G,∀ i N M:ℕ,i≤N → N≤M→ A.clock.J i=j → Bail (fame _) σ (setkin G (pink k (location A N i))-setkin G (pink k (location A M i))) (C*ratioR A.S N i targetPower)
    value: ∀ e≤ E,∀ m,1≤m→ m+1≤E+2 → Angler G σ C e m
lemma seat_minus (G:Gauge){R S:Row (TypeFace 2) (TypeFace 2)}(hp:0≤σ)(hc:0≤C)(H:R.strip σ C)(q:S.strip σ C): setkin G R-setkin G S= setkin G (minusRows R S):= by
    unfold setkin; rw [←ink_delta G hp H q hc hc]
    have he: couple (lands (inkling G R))-couple (lands (inkling G S))= couple (lands (minusRows (inkling G R) (inkling G S))):= by ext v; simp only [Pi.sub_apply,couple,lands,halve,minusRows]; ring
    rw [←he]; ext v; simp only [sand,Pi.sub_apply,Finset.sum_sub_distrib,sub_div]
lemma teller_raise (h:Teller G σ C){D:ℝ}(he:C≤D): Teller G σ D:= ⟨h.plus.trans he,fun i T A hx=> (h.pump i T A hx).trans (mul_le_mul_of_nonneg_left he hx.1)⟩
lemma angler_raise {e m}(h:Angler G σ C e m){D:ℝ}(he:C≤D): Angler G σ D e m:= ⟨h.plus.trans_le he,fun T ht hv H B hB hd=> (h.value T ht hv H B hB hd).mono (mul_le_mul_of_nonneg_right he hB)⟩
lemma uniform {I:Type}{P: I→ℝ→Prop}(S:Finset I)(h:∀ i∈S,∃ C,P i C)(p:∀ i∈S,∀ C,P i C→∀ A,C≤A→ P i A): ∃ C:ℝ,0<C ∧ ∀ i∈S,P i C:= by
   induction S using Finset.induction with
   | empty=> exact ⟨1,one_pos,by simp⟩
   | @insert i S u ih=>
      obtain ⟨C',c,H⟩:= ih (fun j hj=>h j (Finset.mem_insert_of_mem hj)) (fun j hj=>p j (Finset.mem_insert_of_mem hj)); obtain ⟨A,a⟩:=h i (Finset.mem_insert_self ..); refine ⟨max C' A,c.trans_le (le_max_left ..),fun j hj=>?_⟩; rcases Finset.mem_insert.mp hj with rfl|hh;exact p j hj A a _ (le_max_right ..); exact p _ hj C' (H j hh) _ (le_max_left ..)
lemma flax_width (G:Gauge)(k:ℝ)(hk:0<k)(hj:4≤j): ∃ σ:ℝ,0<σ∧σ≤1∧∀ E η,0<η → η≤ σ →∃ C:ℝ,Flax G k j E η C := by
    obtain ⟨σ,B,hσ,hB,U,V⟩:= Flat.colors G k hk hj; refine ⟨min σ 1,lt_min hσ one_pos,min_le_right ..,fun E η he hu=>?_⟩
    obtain ⟨C,c,A⟩:= setkin_pay G he.le; obtain ⟨D,d⟩:= teller_made G he
    let S:=Finset.Icc 0 E ×ˢ Finset.Icc 0 (E+2)
    obtain ⟨B',u,Q⟩:= uniform S (P:=fun (i:ℕ × ℕ) Z=> Bail (fame _) η (Enter G i.1 i.2) Z) (fun i _=> enter_width i.1 i.2 η) (fun i _ _ H _ h=>H.mono h)
    obtain ⟨A',v,Y⟩:= uniform S (P:=fun (i:ℕ × ℕ) Z=> Angler G η Z i.1 i.2) (fun i _=> anglers _ _ he.le i.1 i.2) (fun i _ _ H _ h=> angler_raise H h)
    let Z:= max (max (C*B) D) (max B' A'); have hA: C*B ≤ Z:=(le_max_left ..).trans (le_max_left ..);have hd: D≤Z:=(le_max_right ..).trans (le_max_left ..);have hq:B'≤Z:=(le_max_left ..).trans (le_max_right ..);have hb:A'≤Z:=(le_max_right ..).trans (le_max_right ..)
    have hs := hu.trans (min_le_left ..); have hh W: (pink k (W:Train j)).strip η B:= strip_mono (U W).1 hs le_rfl
    refine ⟨Z,u.trans_le hq,he,teller_raise d hd, fun W=> (A _ _ hB.le (hh W)).mono hA,fun e hx r hr=> (Q (e,r) (by simp [S,hx];omega)).mono hq,fun W i N M hn hm hJ=> ?_, fun e h m _ hm=> angler_raise (Y (e,m) (by simp [S,h];omega)) hb⟩ -- dependency t
    subst j; rw [seat_minus G he.le hB.le (hh _) (hh _)]; let R:=ratioR W.S N i targetPower; have hR:0<R:= ratioR_pos ..; refine (A _ _ (mul_pos hB hR).le (strip_mono (V W N M i hn hm rfl).1 hs le_rfl)).mono ?_; rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right hA hR.le
end YM.FormalBulk08.Dove
