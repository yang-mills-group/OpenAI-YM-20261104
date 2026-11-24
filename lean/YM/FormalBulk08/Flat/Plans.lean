import YM.FormalBulk08.Flat.Hold

/-!
# Flat primitives to book for a formal step

Cost routines can choose width & pre-prices knowing J pair, never next L.
Pre/post split is reflected in the exact APIs. Kernels on COVER, the
`Ready` test on every torus links the recurrence to the invertible
conditional, not to a stand-in damped Gaussian.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Flat
open Filter Set Function Lattice Laurent Bloch Exterior Precision RG Next.Free UVExtension.Free Work.F08 Stationary Tree
open scoped Topology BigOperators Matrix
variable {G : Gauge} {P : Patch} {j t : ℕ}
namespace Lodge

lemma subtracting (G : Gauge) (T : Lodge P) (K : KernelChoices) (W X : Cross P.L (TypeFace 1) (TypeFace 1))
    (σ C : ℝ) (hσ : 0<σ) (hC : 0<C) (hW : W.strip σ C) (hX : X.strip σ C) :
    minusRows (primaryMean G K T W) (primaryMean G K T X) = primaryMean G K T (minusRows W X) ∧
    minusRows (parkMap G K T W) (parkMap G K T X)=parkMap G K T (minusRows W X) := by
  classical
  have he := grown_budget G _ hC.le hW; have hx:=grown_budget G _ hC.le hX
  have hh (W V : Row (Co P.L (Loc G 1)) (Loc G 1)) {a : Type} [Fintype a] (M : Row a (Co P.L (Loc G 1))) (hw : Whole W) (hv : Whole V) (hm : Whole M): minusRows (composeRows M W) (composeRows M V) = composeRows M (minusRows W V) := by
    apply bank_injective (((hm.prod hw).minus (hm.prod hv)).safe) (hm.prod (hw.minus hv)).safe
    intro n; rw [(hm.prod hw).less (hm.prod hv), hm.acts (hw.minus hv), hm.acts hw, hm.acts hv,hw.less hv,Matrix.mul_sub]
  have ht : Whole (cutRow G P.L):= ⟨σ,1,hσ,cut_pay G P.L σ⟩
  let B:= startMap G (P:=P) W; let D:=startMap G (P:=P) X
  have hB : Whole B:=ht.flipped.prod ⟨_,_,hσ,he⟩; have hD : Whole D:=ht.flipped.prod ⟨_,_,hσ,hx⟩
  have hy : startMap G (P:=P) (minusRows W X)=minusRows B D := by unfold startMap; rw [← less_grown]; exact (hh _ _ _ ⟨_,_,hσ,he⟩ ⟨_,_,hσ,hx⟩ ht.flipped).symm
  have hu {α : Type} [Fintype α] (P' : Row α (ParcelG G P.L)) (h : Whole P') : minusRows (composeRows P' B) (composeRows P' D)=composeRows P' (minusRows B D) := by
    apply bank_injective (((h.prod hB).minus (h.prod hD)).safe) (h.prod (hB.minus hD)).safe; intro n
    rw [(h.prod hB).less (h.prod hD),h.acts hB,h.acts hD,h.acts (hB.minus hD), hB.less hD,Matrix.mul_sub]
  obtain ⟨_,hh,h'⟩:= T.foot_staged G K σ hσ
  obtain ⟨_,_,hA,hk⟩:=T.close_staged G K σ hσ
  unfold primaryMean parkMap; rw [hy]; exact ⟨hu _ ⟨_,_,hσ,hA⟩,hu _ ⟨_,_,hσ,hh⟩⟩
end Lodge

-- freeze kernel K and θ prescription; choose central helper via price, unique among Whole clerks.
private lemma supply_center (G : Gauge) (K : KernelChoices) (P : Patch) (hp : P.Branches K G) (V : Train P.J) : ∃ B, Whole B ∧ Clerk G P K V B := by
  obtain ⟨σ,hσ,h⟩:= center_price G K _ P.order_cut
  obtain ⟨C,hC,h⟩:=h P rfl hp
  obtain ⟨B,hb,H⟩:=h V
  exact ⟨B,⟨σ,C,hσ,H⟩,hb⟩

def center (G : Gauge) (K : KernelChoices) (P : Patch) (hp : P.Branches K G) (V : Train P.J) : Row (ParcelG G P.L) (ParcelG G P.L) := (supply_center G K P hp V).choose

def gamma (G : Gauge) (K : KernelChoices) (P : Flight j t) (l : Lodge P.patch) (h : P.patch.Branches K G) :=
    Lodge.power K l (center G K P.patch h P.wing)
lemma gamma_ready (G : Gauge) (K : KernelChoices) (P : Flight j t) (l : Lodge P.patch) (h : P.patch.Branches K G) :
    Whole (gamma G K P l h) ∧ Lodge.Ready G K l P.wing (gamma G K P l h) :=
    ⟨Lodge.whole_wallet _ _ _ (supply_center G K P.patch h P.wing).choose_spec.1,
      Lodge.catalogue_power _ G l P.wing P.legal h (supply_center G K P.patch h P.wing).choose_spec.1
        (supply_center G K P.patch h P.wing).choose_spec.2⟩

def locating (G : Gauge) (K : KernelChoices) (P : Flight j t) (l : Lodge P.patch) :=
    Lodge.primaryMean G K l (Flight.duo K.penalty P).A0

def roots (G : Gauge) (K : KernelChoices) (P : Flight j t) (l : Lodge P.patch) :=
    Lodge.parkMap G K l (Flight.duo K.penalty P).A0

structure charge (A : Levels G) (N M i : ℕ) (K : KernelChoices) (σ C : ℝ) (F : Lodge (A.clock.op i 0).patch)
    (H : (A.clock.op i 0).patch.Branches K G) : Prop where
  single : (gamma G K (destination A N i) F H).strip σ C
  mean : (locating G K (destination A N i) F).strip σ C
  root : (roots G K (destination A N i) F).strip σ C
  line :
    let P:=destination A N i; let Q:=destination A M i
    (minusRows (gamma G K P F H) (gamma G K Q F H)).strip σ (C*ratioR A.S N (i+1) targetPower)
  bend : (minusRows (locating G K (destination A N i) F) (locating G K (destination A M i) F)).strip σ (C*ratioR A.S N (i+1) targetPower)
  fix : (minusRows (roots G K (destination A N i) F) (roots G K (destination A M i) F)).strip σ (C*ratioR A.S N (i+1) targetPower)

lemma may_use (G : Gauge) (K : KernelChoices) (j t : ℕ) (hj : 4≤j) (ht : 4≤t) :
    ∃ σ B : ℝ,0<σ ∧ 0<B ∧ (∀ P : Flight j t, RepeatPrices K.penalty σ B P) ∧
      ∀ P : Patch, P.J=j → ∀ (F : Lodge P), ∃ C : ℝ,0<C ∧
        ∀ (A : Levels G) (i N M), i<N → N≤M →
           A.clock.J i=t → ∀ h : (A.clock.op i 0).patch=P, ∀ hh : (A.clock.op i 0).patch.Branches K G,
            charge A N M i K σ C (h.symm ▸ F) hh := by
  let k:=K.penalty
  obtain ⟨w,B,hw,hB,H,HL⟩:=transports G k K.penalty_pos hj ht
  obtain ⟨u,C,hu,hC,Hχ,hρ⟩:= Flat.colors G k K.penalty_pos hj
  obtain ⟨v,hv,HG⟩:= center_price G K _ hj
  let σ := min (min w u) v
  have hσ:0<σ:=lt_min (lt_min hw hu) hv
  have hw':σ≤w:=(min_le_left ..).trans (min_le_left ..); have hu':σ≤u:=(min_le_left ..).trans (min_le_right ..); have hv':σ≤v:=min_le_right ..
  refine ⟨σ,B,hσ,hB,fun P s hs=>⟨strip_mono (H P s hs).1 hw' le_rfl,strip_mono (H P s hs).2 hw' le_rfl⟩,fun P hP F=>?_⟩
  by_cases hx : P.Branches K G; swap
  · exact ⟨1,one_pos,fun A i N M h hN he ht hh=> False.elim (hx (ht ▸ hh))⟩
  obtain ⟨C',hq,H₁⟩:= HG P hP hx
  obtain ⟨Z,hZ,Hz⟩:= HL P.L
  obtain ⟨V,hV,g⟩:= center_difference G P σ C' hσ
  obtain ⟨p,hp,h⟩:=Lodge.power_pay K F _ hσ G
  obtain ⟨q,hq',h'⟩:=Lodge.bothPay G K F _ hσ
  let T:= max (max (p*C') (q*B)) (max (p*(V*C)) (q*Z))
  have hh₁ : p*C' ≤ T := (le_max_left ..).trans (le_max_left ..)
  have hh₂ : q*B≤T := (le_max_right ..).trans (le_max_left ..)
  have hh₃ : p*(V*C) ≤ T := (le_max_left ..).trans (le_max_right ..)
  have hh₄ : q*Z ≤ T := (le_max_right ..).trans (le_max_right ..)
  refine ⟨T,(mul_pos hp hq).trans_le hh₁,fun A i N M he hN ht0 ht1 hx'=>?_⟩
  subst P
  let P:=(A.clock.op i 0).patch
  change A.clock.J (i+1)=j at hP; subst t j
  have hc W (h : P.Branches K G) : (center G K P h W).strip σ C' := by
    obtain ⟨R,hR,hr⟩:= H₁ W
    unfold center; rw [unique_clerk P (supply_center G K P h W).choose_spec.2 hR ((supply_center G K P h W).choose_spec.1.safe) (Row.rights _ _ hr hv.le)]
    exact strip_mono hr hv' le_rfl
  let U:=destination A N i; let Y:=destination A M i
  let E:= ratioR A.S N (i+1) targetPower; have he':0<E:= ratioR_pos ..
  let L n := (Flight.duo k (destination A n i)).A0
  have hl n : (L n).strip σ B := by
    let g:=destination A n i
    have hT := strip_mono ((H g [] (Nat.zero_le _)).1) hw' le_rfl
    exact strip_mono hT le_rfl (div_le_self hB.le (one_le_pow₀ (by exact_mod_cast (A.S.block i).property)))
  have hi : (minusRows (L N) (L M)).strip σ (Z*E) := strip_mono ((Hz A N M i he hN rfl rfl rfl [] (Nat.zero_le _)).1) hw' le_rfl
  have hY := hρ A N M (i+1) he hN rfl
  let α:=center G K P hx U.wing; let β:= center G K P hx Y.wing
  have ha : α.strip σ C':=hc _ hx; have hb : β.strip σ C' :=hc _ hx
  have hφ:= (strip_mono hY.1 hu' le_rfl)
  have ht x : Whole (pink k (x : Train (A.clock.J (i+1)))):=⟨_,_,hu,(Hχ x).1⟩
  have hd:= g _ U.wing Y.wing K _ _ _ (supply_center G K P hx U.wing).choose_spec.2 (supply_center G K P hx Y.wing).choose_spec.2 ha hb (ht _) (ht _) (mul_pos hC he').le hφ
  have HG : (Lodge.power K F α).strip σ T := strip_mono (h α _ hq.le ha) le_rfl hh₁
  obtain ⟨hm,hr,-⟩:= h' (L N) _ hB.le (hl _)
  obtain ⟨hA,hK,-⟩:= h' _ _ (mul_pos hZ he').le hi
  have ht := Lodge.subtracting G F K _ _ _ _ hσ hB (hl N) (hl M)
  have hf : q*(Z*E)≤T*E := by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hh₄ he'.le
  refine ⟨HG,strip_mono hm le_rfl hh₂,strip_mono hr le_rfl hh₂,?_,?_,?_⟩
  · change (minusRows (Lodge.power K F α) (Lodge.power K F β)).strip σ _
    rw [Lodge.power_add _ _ _ _ ⟨_,_,hσ,ha⟩ ⟨_,_,hσ,hb⟩]
    apply strip_mono (h _ (V*(C*E)) (mul_pos hV (mul_pos hC he')).le hd) le_rfl
    calc
      _ = p*(V*C)*E:=by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hh₃ he'.le
  · change (minusRows (F.primaryMean G K (L N)) (F.primaryMean G K (L M))).strip σ (T*E)
    rw [ht.1]; exact strip_mono hA le_rfl hf
  change (minusRows (F.parkMap G K (L N)) (F.parkMap G K (L M))).strip σ (T*E)
  rw [ht.2]; exact strip_mono hK le_rfl hf
end YM.FormalBulk08.Flat
