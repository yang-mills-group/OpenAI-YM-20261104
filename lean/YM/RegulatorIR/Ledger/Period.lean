import YM.RegulatorIR.Ledger.Hold

/-! Two-size period estimates. No loss by $P^a$ at terminal data allowed
here. EPS/period interplay quantified before taking limits. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Ledger.Sky
open Budget Budget.Packet Budget.Tariff Budget.Layer Budget.Tuple Budget.Deck Uniform Uniform.Post Function Step Diagram Gradient Spatial
open scoped Topology ENNReal NNReal BigOperators Classical
variable {W:Type}{M:W→ℕ}{X Y:Page M→Type} (S:Sky X Y) (T:S.Accounts) {m:ℕ}(Z:T.Report m)
variable {k j : Choice M}{c₀ γ:ℝ}{p b q h α e r u:ℕ}{x: W→Room}{L:Meter W}{c:Flap M→ℝ≥0∞}{s:W→ℝ≥0∞}

def cushion (c₀:ℝ) (x:W→Room): Prop := ∀ w,c₀*S.P w ≤ Spatial.singular (S.P w) (x w)

def IR₀ (h b:ℕ) (w: W) : ℝ:= (S.ε w^h)⁻¹*(S.P w^b)⁻¹
def IR₁ (γ:ℝ) (w:W) : ℝ:= (S.P w ^ (γ/2))⁻¹
def transferErr (h b:ℕ)(γ:ℝ)(w:W) :ℝ := S.IR₀ h b w+S.IR₁ γ w
lemma pos₀ (w:W) : 0<S.IR₀ h b w := by have h :0<S.ε w:= S.hl _; have H:= S.hp w; unfold IR₀; positivity
lemma pos₁ (w:W) : 0<S.IR₁ γ w:= by have h:= S.hp w; unfold IR₁; positivity
lemma transfer_pos (w:W) :0<S.transferErr h b γ w:= add_pos (S.pos₀ w) (S.pos₁ w)

private def travelX (S:Sky X Y)(x:W→Room)(b:ℕ) := (S.lifts.insideRoom S.ridge S.ridge_pos).toll (step_center M x) b
private lemma tallies {P R v d:ℝ} (hR:0<R) (hP:0<P)(hv:0<v)(hd: v * P≤d) : (amount R b d)⁻¹ ≤ ENNReal.ofReal (v⁻¹^b*(R/P)^b):=by
 have h:0<(1+d/R):=by have hx:=lt_of_lt_of_le (mul_pos hv hP) hd; positivity
 have hx : (1+d/R)⁻¹ ≤ v⁻¹*(R/P) :=by
   calc
    _ ≤ (v*P/R)⁻¹:= by apply inv_anti₀ (by positivity); exact (div_le_div_of_nonneg_right hd hR.le).trans (le_add_of_nonneg_left zero_le_one)
    _ = _:= by field_simp
 unfold amount; rw [← ENNReal.ofReal_pow h.le,← ENNReal.ofReal_inv_of_pos (pow_pos h _),← inv_pow,← mul_pow]; gcongr

section Period
variable (R:S.Radiants L γ u α c k)(cx:S.cushion c₀ x)(hc:0<c₀)
include R cx hc
private lemma day (t:Flap M) (he:t.offset < k.age t.volW): S.priceStep h γ k t*(travelX S x b t)⁻¹ ≤ ENNReal.ofReal (c₀⁻¹ ^ b) * ENNReal.ofReal (S.IR₀ h b t.volW):= by
 rw [priceStep, if_neg (not_le.mpr he)]
 obtain ⟨w,rfl⟩:= Radiants.front _ he
 let i:= k.before.wing w; let d:=w.volW
 have hh : S.ridge i=1:=max_eq_left (R.crest w.next)
 change ENNReal.ofReal ((S.l i.prev ^ h)⁻¹) * (travelX S x b i)⁻¹ ≤ _
 have hz : (travelX S x b i)⁻¹ ≤ ENNReal.ofReal (c₀⁻¹ ^ b*(1/S.P d)^b):=by
    rw [← hh]; exact tallies (S.ridge_pos i) (S.hp d) hc (cx d)
 have hε:0<S.ε d := S.hl _
 have he:S.ε d ≤ S.l i.prev:= S.heads i.prev
 apply (mul_le_mul' (show ENNReal.ofReal ((S.l i.prev ^ h)⁻¹) ≤ ENNReal.ofReal ((S.ε d ^ h)⁻¹) by gcongr) hz).trans_eq
 change _= ENNReal.ofReal (c₀⁻¹ ^ b)*ENNReal.ofReal (S.IR₀ h b d);
 rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),IR₀]; congr 1; simp only [one_div, inv_pow]; ring
omit R cx hc in
private lemma how_γ (w:W) : ((Real.sqrt (S.P w))^γ)⁻¹=S.IR₁ γ w:=by
    unfold IR₁; rw [Real.sqrt_eq_rpow,← Real.rpow_mul (S.hp w).le]; ring_nf
private lemma night_low (hb:0<b)(t:Flap M)(he:k.age t.volW ≤ t.offset)(hr:S.ridge t ≤ Real.sqrt (S.P t.volW)):
 S.priceStep h γ k t*(travelX S x b t)⁻¹ ≤ ENNReal.ofReal (c₀⁻¹ ^ b) * ENNReal.ofReal (S.IR₁ γ t.volW):= by
 obtain ⟨w,rfl⟩:=Radiants.rearward _ he
 let i:= k.after.wing w; let a:=i.volW; let P:=S.P a
 have hp: 0<P:= S.hp a
 change S.priceStep h γ k i * _ ≤ _; rw [priceStep, if_pos he]
 have ht: ENNReal.ofReal ((S.l i.prev^γ)⁻¹) ≤ 1:=by
   have h' : 1≤S.l i.prev:= R.crested w.prev
   apply le_trans _ ENNReal.ofReal_one.le; exact ENNReal.ofReal_le_ofReal (inv_le_one_of_one_le₀ (Real.one_le_rpow h' R.gleams.le))
 have hh : (travelX S x b i)⁻¹ ≤ ENNReal.ofReal (c₀⁻¹ ^ b*(S.ridge i/P)^b):= tallies (S.ridge_pos i) hp hc (cx a)
 apply (mul_le_mul' ht hh).trans
 rw [one_mul, ← ENNReal.ofReal_mul (by positivity)]
 have hρ : S.ridge i/P ≤ (Real.sqrt P)⁻¹:= by
    have hroot : 0< Real.sqrt P:= Real.sqrt_pos_of_pos hp
    calc
      _ ≤ Real.sqrt P/P:=div_le_div_of_nonneg_right hr hp.le
      _ = _:= by field_simp;nlinarith [Real.sq_sqrt hp.le]
 have hA : 1≤Real.sqrt P:= (Real.le_sqrt (by norm_num) hp.le).mpr (by simpa using R.side a)
 apply ENNReal.ofReal_le_ofReal
 apply mul_le_mul_of_nonneg_left _ (by positivity)
 calc
    _ ≤ (Real.sqrt P)⁻¹ ^ b:= pow_le_pow_left₀ (div_nonneg (S.ridge_pos i).le hp.le) hρ _
    _ ≤ ((Real.sqrt P)^γ)⁻¹:= by
      rw [inv_pow,← Real.rpow_natCast]; apply inv_anti₀ (by positivity : 0<Real.sqrt P ^ γ); exact Real.rpow_le_rpow_of_exponent_le hA (by have hh:(1:ℝ)≤(b:ℝ):= (by exact_mod_cast hb); exact R.small.trans hh)
    _ = _:= S.how_γ a

omit cx hc in
private lemma night_high (t:Flap M) (he:k.age t.volW ≤ t.offset)(hr: Real.sqrt (S.P t.volW) ≤ S.ridge t): S.priceStep h γ k t*(travelX S x b t)⁻¹ ≤ ENNReal.ofReal (S.shift t)*ENNReal.ofReal (S.IR₁ γ t.volW):=by
 obtain ⟨w,rfl⟩:=Radiants.rearward _ he; let i:=k.after.wing w
 let a:=i.volW; let P:= S.P a
 have hℓ : S.ridge i=S.l i.next:=max_eq_right (R.crested w.next)
 have hp:0<P:= S.hp a; have hl:= S.hl i.prev; have hy:= S.shift_pos i
 change Real.sqrt P ≤ S.ridge i at hr; rw [hℓ] at hr
 change S.priceStep h γ k i*_≤ENNReal.ofReal (S.shift i)*ENNReal.ofReal (S.IR₁ γ a)
 rw [priceStep,if_pos he, ← ENNReal.ofReal_mul (by positivity)]
 have hh : (travelX S x b i)⁻¹ ≤ 1:= by rw [← inv_one (G:=ℝ≥0∞)]; exact ENNReal.inv_le_inv.mpr (amount_unit (S.ridge_pos i) _ (singular_nonneg ..))
 apply (mul_le_mul' le_rfl hh).trans; rw [mul_one]; apply ENNReal.ofReal_le_ofReal
 rw [← S.how_γ a]
 apply le_trans _ (mul_le_mul_of_nonneg_right (Real.rpow_le_self_of_one_le (S.one_le_shift i) R.small) (by positivity))
 calc
  _ = S.shift i ^ γ * (S.l i.next ^ γ)⁻¹:= by rw [S.shift_up i, Real.mul_rpow hy.le hl.le]; field_simp
  _ ≤ _:= mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) (Real.rpow_le_rpow (Real.sqrt_nonneg _) hr R.gleams.le)) (by positivity)

lemma covers_cost (hb:0<b): Carry (flapL M L) (fun i=> ENNReal.ofReal (S.transferErr h b γ i.volW)) fun t=> S.priceStep h γ k t * ((S.lifts.insideRoom S.ridge S.ridge_pos).toll (step_center M x) b t)⁻¹:=by
 refine ⟨_, Poly.add (Poly.standard _ (ENNReal.ofReal_ne_top (r:=c₀⁻¹ ^ b))) R.scale,?_⟩
 intro w
 have h₁ w : ENNReal.ofReal (S.IR₀ h b w)≤ ENNReal.ofReal (S.transferErr h b γ w):= ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (S.pos₁ w).le)
 have h₂ w : ENNReal.ofReal (S.IR₁ γ w)≤ ENNReal.ofReal (S.transferErr h b γ w):= ENNReal.ofReal_le_ofReal (le_add_of_nonneg_left (S.pos₀ w).le)
 rcases lt_or_ge w.offset (k.age w.volW) with hp|hp
 · exact le_trans (S.day R cx hc w hp) (mul_le_mul' (le_add_right le_rfl) (h₁ _))
 rcases le_total (S.ridge w) (Real.sqrt (S.P w.volW)) with hm|hm
 · exact le_trans (S.night_low R cx hc hb w hp hm) (mul_le_mul' (le_add_right le_rfl) (h₂ _))
 exact le_trans (S.night_high R w hp hm) (mul_le_mul' (le_add_left le_rfl) (h₂ _))
end Period
end YM.RegulatorIR.Ledger.Sky
