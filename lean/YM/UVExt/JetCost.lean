import YM.UVExt.JetDelivery
/-! Delta estimates include volume count per path pairing. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths
open RG Function Filter Wilson Precision Lattice Laurent Bid Exterior Matrix Set Real
open scoped Topology ContDiff BigOperators Classical

lemma signed_nonempty : (0:ℝ)<Fintype.card Signed := by exact_mod_cast Fintype.card_pos
lemma face_lift (n : Side) : (Fintype.card (Site n):ℝ) ≤ Fintype.card (Face (Per n)) := by
  letI : Nonempty PlaqAxes := ⟨⟨⟨0,1⟩,by decide⟩⟩
  change (Fintype.card (Site n):ℝ) ≤ Fintype.card (Site n × PlaqAxes)
  rw [Fintype.card_prod]; have h := Nat.mul_le_mul_left (Fintype.card (Site n)) (Fintype.card_pos (α:=PlaqAxes))
  change Fintype.card (Site n)*1 ≤ _ at h; rw [mul_one] at h; exact_mod_cast h

variable {G:Gauge} {W : Shadow G} {e n} {C σ Λ : ℝ} (v : Dir G n) (he : (e:ℕ)=3 ∨ e=4) (hσ : 0<σ)
local notation "⨳" => ((Fintype.card Signed:ℝ)⁻¹)
lemma riser_pos (G : Gauge) : 0≤riser G := by unfold riser; have ha := curveBill_pos G; have hk := K_pos G; have hr := G.colorScale_pos; positivity
lemma riser_fee (s) : 6*curveBill G*‖dColor G n 1 (pulled v s)‖ ≤ riser G*‖dColor G n 1 v‖ ∧
     2*driftPrice (pulled v s) ≤ riser G * (‖v‖+‖dColor G n 1 v‖) := by
     let D := ‖dColor G n 1 v‖; let Y := ‖v‖; let d := ‖dColor G n 1 (pulled v s)‖; let y := ‖pulled v s‖
     have hx := paid_curl v s
     have h₁ : y≤Y := hx.1; have h₂ : d≤16*D := hx.2
     have hD : 0≤D := norm_nonneg _; have hY : 0 ≤ Y := norm_nonneg _
     let K' := K G*G.colorScale; let c := curveBill G
     have hK : 0≤K' := mul_nonneg (zero_le_one.trans <| K_pos G) G.colorScale_pos.le
     have hc : 0≤c := (curveBill_pos G).trans' zero_le_one
     change 6*c*d ≤ _ ∧ 2*((10*curveBill G*K G*G.colorScale) * y + 3*curveBill G*d) ≤ _
     unfold riser; change 6*c*d ≤ 192*c*(1+K')*D ∧ _ ≤ 192*c*(1+K')*(Y+D)
     rw [show ((10:ℝ)* curveBill G*K G*G.colorScale)*(y)=10*c*K'*y by unfold K' c; ring]
     change 6*c*d ≤ _ ∧ 2*(10*c*K'*y+3*c*d) ≤ _
     have p₁ : 0 ≤ c*(16*D-d) := mul_nonneg hc (by linarith [h₂])
     have p₂ : 0 ≤ c*K'*(Y-y) := mul_nonneg (mul_nonneg hc hK) (by linarith [h₁])
     constructor <;> nlinarith only [p₁,p₂,(by positivity : 0 ≤ c * Y),(by positivity : 0≤ c*K'*Y),(by positivity : 0≤ c*K'*D),(by positivity : 0 ≤ c*(1+K')*D),(by positivity : 0≤c*D),(by positivity : 0≤c*(1+K')*Y)]

lemma gain_larger {Q A Y D r : ℝ} {k : ℕ} (hQ : 0≤Q) (hA : 0≤A) (hD : 0≤D) (hY : 0≤Y) (hr : 0≤r) (h : Q≤r*D) (h' : A≤r*(D+Y)) (hk : k=3 ∨ k=4) : gain Q A k ≤ r^k*gain D (D+Y) k := by
   have he : gain Q A k ≤ gain (r*D) (r*(D+Y)) k := by unfold gain; split <;> gcongr
   refine he.trans_eq ?_
   rcases hk with rfl|rfl <;> unfold gain <;> norm_num only [ite_true, ↓reduceIte,ite_false] <;> ring
lemma baseCost_pos (hs : 0<σ) : 0 ≤ baseCost G e σ v := by dsimp only [baseCost]; exact mul_nonneg (by positivity [riser_pos G, allowance_pos e hs.le]) (gain_pos (by positivity) (by positivity))
include hσ he
lemma base_fee s : 3^e*levy (σ:=σ) (pulled v s) e ≤ baseCost G e σ v := by
  let Q := 6*curveBill G*‖dColor G n 1 (pulled v s)‖
  let A := 2*driftPrice (pulled v s)
  let B := gain ‖dColor G n 1 v‖ (‖dColor G n 1 v‖+‖v‖) e
  have h := (gain_larger (r:=riser G) (Y:=‖v‖) (D:=‖dColor G n 1 v‖) (k:=e) (Q:=Q) (A:=A) (by unfold Q; positivity [curveBill_pos G]) (mul_nonneg (by norm_num) (driftPrice_pos _)) (norm_nonneg _) (norm_nonneg _) (riser_pos _) (riser_fee v s).1 ((riser_fee v s).2.trans_eq (by rw [add_comm])) he)
  let C' : ℝ := 3^e*10*allowance e σ
  change 3^e*(10*allowance e σ*gain Q A e)≤ C'*(riser G)^e*B
  rw [show (3:ℝ)^e * _ = C' * gain Q A e by unfold C'; ring,mul_assoc C']
  exact mul_le_mul_of_nonneg_left h (show 0≤C' by unfold C'; positivity [allowance_pos e hσ.le])
lemma base_fee0 s : levy (σ:=σ) (pulled v s) e ≤ baseCost G e σ v := le_trans (le_mul_of_one_le_left (by unfold levy; exact mul_nonneg (by positivity [allowance_pos e hσ.le]) (gain_pos (by positivity [curveBill_pos G]) (mul_nonneg (by norm_num) (driftPrice_pos _)))) (one_le_pow₀ (show (1:ℝ)≤3 by norm_num))) <| base_fee v he hσ s

omit hσ he
local notation "𝓢" => Finset.univ
private lemma avg_budget {ι : Type*} [Fintype ι] {A : ℝ} (f : Signed→ι→ℝ) (hf : ∀ s i,|f s i|≤A) : |⨳ * ∑ s:Signed,∑ i:ι,f s i| ≤ Fintype.card ι * A := by
  rw [abs_mul,abs_of_pos (inv_pos.mpr signed_nonempty)]
  apply (inv_mul_le_iff₀ signed_nonempty).mpr
  calc
     _ ≤ ∑ s:Signed,∑ _i:ι,A := (Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum fun i _=> (Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum fun j hj=>hf i j))
     _ = _ := by simp

include he hσ
lemma candle_fee {p : Clip} (h : PaidShadow W C Λ σ) : |tag e (qulit W true v p) - tag e (qulit W false v p)| ≤ Fintype.card (Face (Per n))*baseCost G e σ v*((Fintype.card G.ColorIndex:ℝ)*C^2) := by
  let T (e' : Bool) (s : Signed) (x : Face (Per n)) := (tag e (ringLit (pulled v s) p x) + (1/2:ℝ) * tag e (liftAir (pulled v s) e' x.1 (fun i => score W x.2 i.1)))
  rw [qulit_jet e true h hσ,qulit_jet e false h hσ]
  have hg : (Fintype.card (Face (Per n)):ℝ) * (baseCost G e σ v * ((Fintype.card G.ColorIndex:ℝ)*C^2))  = _ := Eq.symm <| mul_assoc (Fintype.card (Face (Per n)):ℝ) (baseCost G e σ v) ((Fintype.card G.ColorIndex:ℝ)*C^2)
  refine le_trans ?_ hg.le
  change |⨳ * ∑ s,∑ x,T true s x - ⨳ * ∑ s,∑ x,T false s x| ≤ _ -- parser subtract
  conv in _ - _ => rw [←mul_sub,← Finset.sum_sub_distrib]
  change |⨳ * (∑ s, ((∑ x,T true s x) - ∑ x,T false s x))| ≤ _
  simp_rw [←Finset.sum_sub_distrib]
  refine avg_budget (ι:=Face (Per n)) _ fun i j=> ?_
  unfold T; simp only [add_sub_add_left_eq_sub, ←mul_sub,abs_mul]
  let R := (Fintype.card G.ColorIndex:ℝ)*C^2
  refine (mul_le_mul_of_nonneg_left (air_price (C:=R) (pulled v i) j.1 (paid_chord W h j.2) hσ he) (abs_nonneg _)).trans <| le_trans ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (base_fee v he hσ i) (show _ ≤ R by unfold R; positivity)) (abs_nonneg (1/2:ℝ)))) ?_
  have : 0≤baseCost G e σ v *R := by unfold R; positivity [baseCost_pos (e:=e) v hσ]
  norm_num only [abs_of_pos (by norm_num : (0:ℝ)<1/2)]; change (1/2:ℝ)*_≤ baseCost G e σ v *R; linarith only [this]
lemma chant_fee {p : Clip} (h : PaidShadow W C Λ σ) : |tag e (payload W v p) - tag e (bench W v p)| ≤ Fintype.card (Site n)*(2*baseCost G e σ v*C) := by
  let D s x:= tag e (song (pulled v s) x W.cubic)+tag e (song (pulled v s) x W.quartic)
  rw [payload_jet e h hσ]
  simp only [add_sub_cancel_left]; simp_rw [←Finset.sum_add_distrib]
  exact avg_budget D (fun s x=> (_root_.abs_add_le _ _).trans ((add_le_add (song_price (T:=W.cubic) _ (Or.inl rfl) h.coeffThree hσ x e he) (song_price (T:=W.quartic) _ (Or.inr rfl) h.coeffFour hσ x e he)).trans (by rw [←two_mul, ←mul_assoc]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (base_fee0 v he hσ _) (by norm_num)) ((pay_nonneg W h).1))))

lemma missing_budget {p : Clip} (h : PaidShadow W C Λ σ) : |qulitGap e v W p| ≤ (Fintype.card (Face (Per n)):ℝ)*reel G e C σ ‖v‖ ‖dColor G n 1 v‖ := by
  unfold qulitGap
  let B := baseCost G e σ v
  calc
    _ = |(tag e (payload W v p) - tag e (bench W v p)) + (tag e (bench W v p) - tag e (qulit W false v p))| := by simp only [sub_add_sub_cancel]
    _ ≤ (Fintype.card (Site n):ℝ)*(2*B*C) + (Fintype.card (Face (Per n)):ℝ)* B *((Fintype.card G.ColorIndex:ℝ)*C^2) := (_root_.abs_add_le ..).trans (add_le_add (chant_fee v he hσ h) (show _ by rw [rotated_bench W h hσ v]; exact candle_fee v he hσ h))
    _ ≤ _ := by
      let S : ℝ := Fintype.card (Face (Per n))
      let R : ℝ := Fintype.card G.ColorIndex
      have hc := (pay_nonneg W h).1; have hB : 0 ≤ B := baseCost_pos v hσ
      have hT := mul_le_mul_of_nonneg_right (face_lift n) (show 0≤2*B*C by positivity)
      change _ ≤ S * _
      calc
         _ ≤ S * (2*B*C + B*(R*C^2)) := add_le_add_left hT (S*B*((Fintype.card G.ColorIndex : ℝ)*C^2)) |>.trans_eq (by change (S:_)*_+(S*(B:_))*_=_; rw [mul_assoc S B,mul_add])
         _ ≤ _ := mul_le_mul_of_nonneg_left (α:=ℝ) (a:=S) ?_ (Nat.cast_nonneg (Fintype.card (Face (Per n))))
      unfold reel
      change 2*B*C+B*(R*C^2) ≤ _*(C+1)^2*(R+3)*_
      have hR : 0≤R := Nat.cast_nonneg _
      have hC : 0 ≤C := (pay_nonneg W h).1
      rw [show 2*B*C+B*(R*C^2) = B*(R*C^2+2*C) by ring, show (3:ℝ)^e*10*_*(riser G)^e*(C+1)^2*(R+3)*gain ‖dColor G n 1 v‖ (‖dColor G n 1 v‖+‖v‖) e =B*((C+1)^2*(R+3)) by unfold B baseCost; ring]
      apply mul_le_mul_of_nonneg_left ?_ hB
      nlinarith

end YM.UVExt.Paths
