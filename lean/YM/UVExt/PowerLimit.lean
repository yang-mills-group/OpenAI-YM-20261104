import YM.UVExt.MapElection
/-! Full physical-volume count under the off-jet curvature gain. Only an estimate on jet discrepancies. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths
open Function RG Precision Wilson Lattice Exterior Laurent Bid Filter Real Set Bloch Matrix
open scoped BigOperators ContDiff Topology Classical

variable {G : Gauge} (A : Levels G) (P : MapPrices) {M : Horizon A} {U} {f : ℕ→ℕ}
    (Q : Discipline P A M) (HU : Follows A f M U) (hf : Tendsto f atTop atTop)

lemma mesh_ge1 (j : ℕ) : 0 < A.S.a j ∧ A.S.a j ≤ 1 := ⟨A.S.a_pos _, A.S.strictAnti.antitone (Nat.zero_le j) |>.trans_eq A.S.a_zero⟩

variable (m : ℕ)
lemma powaid_sum {a b : ℕ→ℝ} {k} (h : powaid A m k a) (hp : powaid A m k b) : powaid A m k (fun i=>a i+b i) := by
   obtain ⟨c,hC,H⟩ := h; obtain ⟨D,hD,H'⟩ := hp
   use (2^16)* max c D; constructor; · exact mul_pos (by norm_num) (lt_max_of_lt_left hC)
   intro i; refine ⟨add_nonneg (H i).1 (H' i).1, ?_⟩
   apply le_trans (pow_le_pow_left₀ (add_nonneg (H i).1 (H' i).1) (show _≤2*max (a i) (b i) by linarith [le_max_left (a i) (b i),le_max_right (a i) (b i)]) 16)
   rw [mul_assoc,mul_pow]
   apply mul_le_mul_of_nonneg_left ?_ (by norm_num)
   obtain ho|ho:=le_total (a i) (b i)
   · rw [max_eq_right ho]; exact (H' i).2.trans (mul_le_mul_of_nonneg_right (le_max_right c D) (pow_nonneg (A.S.a_pos _).le _))
   rw [max_eq_left ho]; exact (H i).2.trans (mul_le_mul_of_nonneg_right (le_max_left c D) (pow_nonneg (A.S.a_pos _).le _))
   /-
      simp only [max_eq_right_if?,max_def]; split_ifs <;> nlinarith [H i,H' i,A.S.a_pos (m+i)]) -/
lemma powaid_promote {x : ℕ→ℝ} {i j} (h : i≤j) (hq : powaid A m j x) : powaid A m i x := by
   rcases hq with ⟨c,hc,ht⟩; exact ⟨c,hc,fun t => ⟨(ht t).1, (ht t).2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one ((mesh_ge1 A (m+t)).1.le) ((mesh_ge1 A _).2) h) hc.le)⟩⟩
lemma boot_cap {D Y : ℕ→ℝ} (hD : powaid A m 31 D) (hY : powaid A m 15 Y) (e : ℕ) (he : e=3∨e=4) : powaid A m 76 (fun i=> gain (D i) (D i+Y i) e) := by
  let Z := powaid_sum A m (powaid_promote A m (i:=15) (j:=31) (by decide) hD) hY
  rcases hD with ⟨c,hc,h⟩; obtain ⟨d,hd,ht⟩ := Z
  /-have h' {i j n : ℕ} {r} (hr : 0≤r) (hi : r≤1) : (r^i)^j ≤ r^n ↔ r^n≥(r^i)^j := Iff.rfl -/
  rcases he with rfl|rfl
  · apply powaid_promote A m (show 76≤93 by decide) _
    use c^3; constructor;· positivity
    intro n
    unfold gain; rw [if_pos rfl]; have he := h n
    refine ⟨pow_nonneg he.1 _, ?_⟩
    convert pow_le_pow_left₀ (pow_nonneg he.1 16) (he.2) 3 using 1 <;> first|rfl|ring
  use c*d^3; constructor; · positivity
  intro n; unfold gain; dsimp only []; rw [if_neg (by decide : ¬(4:ℕ)=3)]; obtain ⟨he,he'⟩:=ht n
  refine ⟨mul_nonneg (h n).1 (pow_nonneg he _), ?_⟩
  convert mul_le_mul (h n).2 (pow_le_pow_left₀ (pow_nonneg he 16) he' 3) (pow_nonneg (pow_nonneg he 16) 3) (mul_nonneg hc.le (pow_nonneg (A.S.a_pos _).le 31)) using 1 <;> first|rfl|ring

lemma true_vol (m p : ℕ) : (Fintype.card (Face (Per (A.S.side m p))) : ℝ) = ((A.S.period p).val:ℝ)^4 * ((A.S.a m)⁻¹)^4 * Fintype.card PlaqAxes := by
   haveI : NeZero (A.S.side m p).val := ⟨(A.S.side m p).property.ne'⟩
   change (Fintype.card ((Fin 4→ ZMod (A.S.side m p).val) × PlaqAxes):ℝ)=_
   rw [Fintype.card_prod,Fintype.card_pi_const,ZMod.card]; simp only [Schedule.side, Schedule.a, inv_inv, PNat.mul_coe, Nat.cast_mul, Fintype.card_pi,Nat.cast_pow, mul_pow, ZMod.card, Fintype.card_fin]
private def towel (G : Gauge) (q : ℕ) := ((q.factorial:ℝ)*(Real.exp 1)*16) * (3^(q:ℕ)) *10 *(riser G)^q *(Fintype.card G.ColorIndex+3:ℝ)
private lemma towel_pos (G : Gauge) (q) : 0 ≤ towel G q := by unfold towel; positivity [riser_pos G]
private def tallCup (q i) := 3^q * 10*allowance q (A.params i).width*(riser G)^q * ((A.params i).paths+1)^2 *(Fintype.card G.ColorIndex+3:ℝ)
private lemma tallCup_pay i q (hq : q≤4) : 0 ≤ tallCup A q i ∧ tallCup A q i ≤ towel G q * (stageCost A i)^6 := by
  let f := (A.params i).paths; let w := (A.params i).width
  have hf : 0 ≤ f := (A.params i).paths_pos.le
  have hw : 0 ≤ w := (A.params i).width_pos.le
  have he := allowance_pos q hw
  constructor
  · unfold tallCup; rw [show (A.params i).width = w from rfl]; positivity [riser_pos G]
  have h := paths_width A i; let X := stageCost A i; have ho : 1≤X := stage_one A i
  have hA : allowance q w * (f+1)^2 ≤ ((q.factorial:ℝ)* Real.exp 1 * 16)* X^6 := by
      unfold allowance
      change (q.factorial:ℝ)*Real.exp 1 * (1+2/w)^q * _ ≤ _
      have ht : (0:ℝ) ≤ (1+2/w) ^ q := by positivity
      have bt := mul_le_mul ((pow_le_pow_left₀ (show (0:ℝ)≤1+2/w from by positivity) h.2 (n:=q)).trans (pow_le_pow_right₀ (show (1:ℝ)≤2*X from by linarith) hq)) (pow_le_pow_left₀ (show (0:ℝ)≤ f+1 by positivity) h.1 2) (sq_nonneg _) (show 0≤(2*X)^4 from by positivity)
      convert mul_le_mul_of_nonneg_left bt (show 0≤ (q.factorial:ℝ)*Real.exp 1 from by positivity) using 1 <;> first|rfl|ring
  unfold tallCup towel
  have hg : 0≤3^q*10*(riser G)^q * (Fintype.card G.ColorIndex+3:ℝ) := by positivity [riser_pos G]
  convert mul_le_mul_of_nonneg_left hA hg using 1 <;> first|rfl|ring

def unmaskedInvoice (q m p : ℕ) (x D : ℝ) := (2*(Fintype.card (Face (Per (A.S.side m p))):ℝ)) * reel G q (A.params m).paths (A.params m).width x D
lemma true_intercept (q) {Y D : ℕ→ℝ} (h : powaid A m 76 (fun n=>gain (D n) (D n+Y n) q)) (hq : q≤4) (p : ℕ) : Tendsto (fun i=>(unmaskedInvoice A (q:=q) (m+i) p (Y i) (D i))^16) atTop (𝓝 0) := by
  obtain ⟨c,hc,ht⟩ := h
  let C : ℝ := 2* ((A.S.period p).val:ℝ)^4 * (Fintype.card PlaqAxes:ℝ)
  have hC : 0≤C := by unfold C; positivity
  let K := towel G q
  have he (i) : unmaskedInvoice A q (m+i) p (Y i) (D i) ≤ (C*((A.S.a (m+i))⁻¹)^4 * (K*(stageCost A (m+i))^6)*gain (D i) (D i+Y i) q) ∧ 0 ≤ unmaskedInvoice A q (m+i) p (Y i) (D i) := by
    unfold unmaskedInvoice reel; rw [true_vol]
    have hQ : (2:ℝ) * (((A.S.period p).val:ℝ)^4 * ((A.S.a (m+i))⁻¹)^4 * (Fintype.card PlaqAxes:ℝ))=C*((A.S.a (m+i))⁻¹)^4 := by unfold C; ring
    change 2 * (((A.S.period p).val:ℝ)^4 * ((A.S.a (m+i))⁻¹)^4 * _) * (tallCup A q (m+i) * gain (D i) (D i+Y i) q) ≤ _ ∧ _
    rw [hQ]
    change _ ≤ _ ∧ 0 ≤ (C*((A.S.a (m+i))⁻¹)^4) * (tallCup A q (m+i) * gain (D i) (D i+Y i) q) -- second already rewritten, use hQ and change via multiplication
    have hw := tallCup_pay A (m+i) q hq
    have hZ := (ht i).1
    constructor
    · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hw.2 hZ) (mul_nonneg hC (pow_nonneg (inv_nonneg.mpr (mesh_ge1 A _|>.1).le) 4))
    exact mul_nonneg (by positivity) (mul_nonneg hw.1 hZ)
  let α := fun i:ℕ=> A.S.a (m+i)
  have hf (i : ℕ) (hi : i≥1) : (unmaskedInvoice A q (m+i) p (Y i) (D i))^16 ≤ (C*K)^16*c*(α i)^6 := by
    have hT : (stageCost A (m+i))^(6*16:ℕ) ≤ ((α i)⁻¹)^6 := by
       rw [show 6*16=(16*6:ℕ) by decide,pow_mul]
       refine pow_le_pow_left₀ (pow_nonneg (show (0:ℝ) ≤ stageCost A (m+i) from zero_le_one.trans <| stage_one A _) 16) ?_ 6
       have hJ : m+i=(m+i-1)+1 := by omega
       unfold α; rw [hJ]; exact stage_fee A _
    let a := α i
    let g := gain (D i) (D i+Y i) q
    calc
      _ ≤ ((C*K)^16 * ((a⁻¹)^(64:ℕ)) * (stageCost A (m+i)^96)) * g^16 := (pow_le_pow_left₀ (he i).2 (he i).1 16).trans_eq (by unfold a α g; ring)
      _ ≤ ((C*K)^16 * ((a⁻¹)^64) * ((a⁻¹)^6)) * (c * a^76) := mul_le_mul (mul_le_mul_of_nonneg_left hT (by positivity)) (ht i).2 (by positivity) (by positivity)
      _ = _ := by have ha : a ≠ 0 := (mesh_ge1 A (m+i) |>.1).ne'; field_simp; ring
  have htop : Tendsto (m+·) atTop atTop := tendsto_atTop_mono (fun i=> show id i ≤ m+i from Nat.le_add_left ..) tendsto_id
  exact squeeze_zero' (Eventually.of_forall fun i=>by positivity) ((eventually_ge_atTop (1:ℕ)).mono hf) (by have h := Tendsto.const_mul ((C*K)^16*c) ((A.S.shrinks.comp htop).pow 6);  simpa only [α,Function.comp_apply,show ((0:ℝ)^6)=0 from by norm_num, mul_zero] using h)
end YM.UVExt.Paths
