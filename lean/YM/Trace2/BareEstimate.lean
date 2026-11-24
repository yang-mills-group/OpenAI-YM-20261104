import YM.Cells.Embedded
import YM.Cells.Margins
import YM.Gauge.Size

/-!
# Cutoff chessboard estimate at a raw plaquette

Use link seams of width two, so that the translated and reflected bad events force distinct
plaquettes in the positive Wilson energy (the period in a `Schedule` is a multiple of four).
This gives a Gaussian exponent uniform in volume at the actual bare coupling, with a power
of beta lost in the prefactor. This module does *not* change the cutoff law to a formal
Gaussian and does not run new blocked kernels.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Trace2.BareEstimate
open Filter Function Set Lattice Wilson Cells MeasureTheory Metric
open scoped Matrix.Norms.Frobenius BigOperators ENNReal Topology ContDiff Classical
variable {G : Gauge} {n : Side}

lemma elementary_partition {r : ℝ} (hr : 0<r) (h₁ : r ≤ 1) (β : ℝ) (hb : 0 ≤ β) :
    Real.exp (-β * (Fintype.card (Face (Per n)) : ℝ) * ((4*r)^2/2)) *
      ((r/4)^(Module.finrank ℝ G.Mat))^(Fintype.card (Edge (Site n))) ≤ partition G n β := by
  let E := (univ : Set (Edge (Site n))).pi (fun _ => G.shell r)
  let μ := prior G n
  let M := Real.exp (-β * (Fintype.card (Face (Per n)) : ℝ) * ((4*r)^2/2))
  have hp {U} (hu : U∈E) (x : Site n) (w : Walk) : G.chord (travel U x w) ≤ w.length*r := by
    induction w generalizing x with
    | nil => simp [travel]
    | cons i w ih =>
      have hw (e) : G.chord (U e) ≤ r := hu e (mem_univ _)
      have hi : G.chord (i.read U x) ≤ r := by rw [Step.read]; split
                                               · rw [G.chord_inv]; exact hw _
                                               exact hw _
      exact (G.chord_triangle _ _).trans ((add_le_add hi (ih (x+i.vec))).trans_eq (by simp [List.length_cons, Nat.cast_add, Nat.cast_one]; ring))
  have hE : MeasurableSet E := MeasurableSet.univ_pi fun _ => G.shell_meas r
  have hl := setIntegral_mono_on (μ:=μ) (s:=E) (f:=fun _=>M) (integrableOn_const (measure_ne_top _ _)) (bare_integrable β|>.integrableOn) hE (fun u hu=>show M ≤ bare β u from by
    unfold bare M
    apply Real.exp_le_exp.mpr
    rw [mul_assoc]; apply mul_le_mul_of_nonpos_left _ (neg_nonpos.mpr hb)
    unfold energy
    calc
      _ ≤ ∑ _ : Face (Per n), ((4*r)^2/2) := Finset.sum_le_sum (fun p _ => by
        have he := hp hu p.1 (square p.2.val.1 p.2.val.2)
        change G.chord _ ≤ (([posDir p.2.val.1,_,_,_].length:ℕ):ℝ)*r at he
        have hh : ([posDir p.2.val.1,posDir p.2.val.2,negDir p.2.val.1,negDir p.2.val.2].length:ℕ)=4 := rfl
        rw [hh] at he; norm_num1 at he
        change G.chord (faceValue u p) ≤ _ at he
        nlinarith only [G.chord_price (faceValue u p), he, G.chord_nonneg (faceValue u p)])
      _ = _ := by simp)
  rw [setIntegral_const, smul_eq_mul, mul_comm _ M] at hl
  have hv : μ.real E = (G.probHaar.real (G.shell r))^(Fintype.card (Edge (Site n))) := by
    unfold Measure.real μ E prior; rw [Measure.pi_pi, ENNReal.toReal_prod]
    simp only [Finset.prod_const, Finset.card_univ]
  exact le_trans (mul_le_mul_of_nonneg_left (hv.symm ▸ pow_le_pow_left₀ (by positivity) (G.shell_ge r hr h₁) _) (Real.exp_pos _).le) (hl.trans (setIntegral_le_integral (bare_integrable β) (Eventually.of_forall (by exact fun x=> (bare_pos _ x).le))))

lemma face_lower {T : Tiling n} {p: Face (Per n)} {i:T.Cell} (hp : ∀ x∈visits p.1 (square p.2.val.1 p.2.val.2), x∈T.chamber 0) :
    (Face.send (T.omega i) (T.translateBy i) p).1 ∈ T.chamber i := by
  let s := T.omega i; let t := T.translateBy i
  have hf (j k : Axis) : affine s t (p.1+step j+step k) = (affine s t p.1 + ((posDir j).rotate s).vec) + ((posDir k).rotate s).vec := by
    simp [affine, Signed.act_add,Step.vec_rotate]; abel
  have hg (j : Axis) : affine s t (p.1+step j) = affine s t p.1 + ((posDir j).rotate s).vec := by
    simp [affine, Signed.act_add,Step.vec_rotate]; abel
  simp only [visits,square,Step.vec_pos,Step.vec_neg] at hp
  have ha := hp p.1 (by simp)
  have hb := hp _ (List.Mem.head .. |> List.Mem.tail p.1)
  let j := p.2.val.1; let k:=p.2.val.2
  have hc : p.1+step j+step k ∈ T.chamber 0 := hp _ (by simp [j,k])
  have he : p.1+step k ∈ T.chamber 0 := hp _ (by
    have H : p.1+step k=p.1+step j + step k+ -step j := by abel
    rw [H]; simp [j,k])
  change atFace (affine s t p.1) ((posDir j).rotate s) ((posDir k).rotate s) ∈ _
  unfold atFace
  split_ifs
  · have h := T.enumerate i hc
    change affine s t _ ∈ _ at h
    rwa [hf] at h
  · have h := T.enumerate i hb; change affine s t _ ∈ _ at h; rw [hg] at h; rwa [add_zero]
  · have h := T.enumerate i he; change affine s t _ ∈ _ at h; rw [hg] at h; rwa [add_zero]
  · rw [add_zero,add_zero]; exact T.enumerate i ha

lemma bad_plaquette {T : Tiling n} {p: Face (Per n)} {β r:ℝ} (hr : 0 < r) (hb : 0 ≤ β)
    (hp : ∀ x∈visits p.1 (square p.2.val.1 p.2.val.2), x∈T.chamber 0) :
    (law G n β).real {U | r ≤ G.chord (faceValue U p)} ≤
      (Real.exp (-β * (Fintype.card T.Cell : ℝ) * (r^2/2)) / partition G n β)^(Fintype.card T.Cell:ℝ)⁻¹ := by
  let D := {U : Config G n | r ≤ G.chord (faceValue U p)}
  have hd : MeasurableSet D := measurableSet_le measurable_const ((G.continuous_chord.comp (continuous_travel ..)).measurable)
  let f := D.indicator (fun _ => (1:ℂ))
  have hf : Interior (T.chamber 0) f :=
    ⟨fun k U => by unfold f D; simp_rw [indicator, mem_setOf]; simp only [face_gauge, G.chord_conj], measurable_const.indicator hd,
      fun U V huv => by unfold f D; simp only [Set.indicator, mem_setOf_eq, faceValue]; rw [show travel U p.1 _=travel V p.1 _ from travel_local _ _ _ _ (agrees_mono huv ?_)]; exact fun _ hx => hp _ hx,
      1,fun U=>by unfold f; by_cases H:U∈D <;> simp [H]⟩
  have hi := T.planted (laws G n β hb) (fun _ : Unit => 0) (fun x y _ => rfl) (fun _ => f) (fun _ => hf)
  simp only [Fintype.prod_unique,T.copy_zero] at hi
  have hμ : ‖moment β f‖ = (law G n β).real D := by
    unfold moment f; rw [integral_indicator hd, setIntegral_const, norm_smul, Real.norm_of_nonneg measureReal_nonneg, norm_one, mul_one]
  apply le_trans (hμ ▸ hi)
  unfold Tiling.rootTest
  apply Real.rpow_le_rpow (norm_nonneg _) _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  change ‖moment β (T.fullAt (fun _ => f))‖ ≤ _
  rw [moment_formula β _ (T.manyIntegral β _ (fun _=>hf))]
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (partition_pos _).le, div_eq_inv_mul]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (partition_pos _).le)
  have he := calc
    ‖∫ U, ↑(bare β U)*∏ i, T.copy i f U ∂prior G n‖ ≤ ∫ U, ‖↑(bare β U)*(∏ i, T.copy i f U : ℂ)‖ ∂prior G n := norm_integral_le_integral_norm _
    _ ≤ ∫ _ : Config G n, Real.exp (-β * (Fintype.card T.Cell : ℝ) * (r^2/2)) ∂prior G n := by
      -- integrability checked by continuity/boundedness too, here integral_mono_of_nonneg avoids complicated product.
      apply integral_mono_of_nonneg (Eventually.of_forall fun _=> norm_nonneg _) (by exact integrable_const _) (Eventually.of_forall fun U=>?_)
      by_cases h : ∀ i, (pull (T.omega i) (T.translateBy i) U)∈D
      · simp only [Tiling.copy,f, D, mem_setOf_eq] at h ⊢
        have hz (i:T.Cell) := h i
        simp only [Set.indicator_of_mem,Set.mem_setOf_eq,hz,star_one,ite_self,Finset.prod_const_one, mul_one,Complex.norm_real,Real.norm_of_nonneg (bare_pos ..).le]
        have hl i : r^2/2 ≤ G.price (faceValue U (Face.send (T.omega i) (T.translateBy i) p)) := by
          rw [← Face.send_price U p _ _ G.price G.price_inv (fun k g => G.price_conj g k)]
          nlinarith only [h i,hr.le,G.chord_price (faceValue (pull (T.omega i) (T.translateBy i) U) p)]
        let u (i : T.Cell) := Face.send (T.omega i) (T.translateBy i) p
        have hh : Injective u := fun i j e => calc
          i = T.which (u j).1 := T.which_chamber (e ▸ (face_lower hp (T:=T)) : (u j).1∈ _)|>.symm
          _ = j := T.which_chamber (face_lower hp)
        unfold bare
        rw [mul_assoc (-β)]
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonpos_left _ (neg_nonpos.mpr hb)
        have hsub : Finset.univ.image u ⊆ Finset.univ := Finset.subset_univ _
        apply le_trans _ <| Finset.sum_le_sum_of_subset_of_nonneg (f:=fun p=>G.price (faceValue U p)) hsub (fun j _ _ => (G.price_range _).1)
        rw [Finset.sum_image hh.injOn]
        convert Finset.sum_le_sum (s:=Finset.univ) (fun i _=>hl i) using 1
        simp
      push Not at h
      obtain ⟨j,h⟩ := h
      change ‖(bare β U:ℂ) * ∏ i, T.copy i f U‖ ≤ _
      rw [Finset.prod_eq_zero (Finset.mem_univ j) (show T.copy j f U=0 from by simp [Tiling.copy,f,h])]
      rw [mul_zero, norm_zero]; exact (Real.exp_pos _).le
    _ = Real.exp (-β * (Fintype.card T.Cell : ℝ) * (r^2/2)) := by simp
  exact he

def levy (G : Gauge) (β : ℝ) := 8*Fintype.card PlaqAxes+4*Module.finrank ℝ G.Mat*Real.log (4*Real.sqrt β)

lemma partition_bill (G : Gauge) (n : Side) {β:ℝ} (hb : 1 ≤ β) :
    Real.exp (-(n.val:ℝ)^4 * levy G β) ≤ partition G n β := by
  let R:= Real.sqrt β
  have hR : 1 ≤ R := Real.one_le_sqrt.mpr hb
  have h0 : 0 < R := zero_lt_one.trans_le hR
  have h := elementary_partition (n:=n) (inv_pos.mpr h0) ((inv_le_one₀ h0).mpr hR) β (zero_le_one.trans hb) (G:=G)
  have hc : Fintype.card (Face (Per n))= n.val^4 * Fintype.card PlaqAxes := by simp [Face,Four,Per,ZMod.card]
  have hd : Fintype.card (Edge (Site n))= n.val^4 * 4 := by simp [Edge,Site,Four,Per,ZMod.card]
  have he : R⁻¹/4 = Real.exp (-Real.log (4*R)) := by rw [Real.exp_neg,Real.exp_log (by positivity)]; field_simp
  rw [hc,hd,he,← Real.exp_nat_mul,← Real.exp_nat_mul,← Real.exp_add] at h
  push_cast at h
  apply le_trans _ h
  apply Real.exp_le_exp.mpr
  apply le_of_eq
  change -_ * _ = -β*_*((4*R⁻¹)^2/2)+_
  rw [mul_pow,inv_pow,show R^2=β from Real.sq_sqrt (by linarith)]
  unfold levy; dsimp [R]
  field_simp
  ring

def halfSide (n:Side) (h:4∣n.val) : Side := ⟨n.val/2,by obtain ⟨t,ht⟩:=h; have hp : 0<n.val:=n.prop; change n.val=4*t at ht; omega⟩
def couple : Side := ⟨2,by norm_num⟩
def duplet (z:Site n) (h:4∣n.val) : Tiling n where
  period := halfSide n h
  units := ⟨couple, by have :=n.prop; change n.val = (n.val/2)*2; omega⟩
  widthHalf := ⟨n.val/4, by obtain ⟨t,ht⟩:=h; have hp : 0<n.val:=n.prop; change n.val=4*t at ht; omega⟩
  even := by change n.val/2=2*(n.val/4); omega
  kind := .link
  base := z

lemma face_duplet (z:Site n) (h:4∣n.val) (i j : Axis) (he : i≠j) (v)
    (hv:v∈visits z (square i j)) : v∈(duplet z h).chamber 0 := by
  intro k
  simp only [visits,square,Step.vec_pos,Step.vec_neg,List.mem_cons,List.not_mem_nil,or_false] at hv
  rw [show (duplet z h).starts 0=z from Tiling.starts_zero _]
  change (v k-z k).val < 2
  have ho : (1:Per n).val=1 := by simpa using ZMod.val_natCast_of_lt (n:=n) (a:=1) (by obtain ⟨t,ht⟩:=h; have hp : 0<n.val:=n.prop; change n.val=4*t at ht; omega)
  have ht : (0:Per n).val < 2 := by simp
  rcases hv with t|t|t|t|t <;> subst v
  all_goals try simp only [Pi.add_apply,Pi.neg_apply,step_apply]
  all_goals try split_ifs <;> simp_all
  simp

lemma bare_tail (G : Gauge) (p : Face (Per n)) (h : 4∣n.val) {r β:ℝ} (hr : 0<r) (hβ : 1≤β) :
    (law G n β).real {U | r ≤ G.chord (faceValue U p)} ≤ Real.exp (16*levy G β-β*r^2/2) := by
  let T:=duplet p.1 h
  have hP x : x∈visits p.1 (square p.2.val.1 p.2.val.2) → x∈T.chamber 0 := face_duplet p.1 h _ _ p.2.prop.ne x
  have hx := bad_plaquette (G:=G) hr (by linarith) hP (β:=β)
  have hc : (n.val:ℝ)^4 = 16 * Fintype.card T.Cell := by
    have hv : n.val=T.period.val*2 := T.units.exact_size
    have hC : Fintype.card T.Cell=T.period.val^4 := by simp [Tiling.Cell,Site,Four,Per,ZMod.card]
    rw [hv,hC]; push_cast; ring
  let N := (Fintype.card T.Cell:ℝ)
  have h0 : 0<N:= by unfold N; exact_mod_cast Fintype.card_pos
  apply hx.trans
  rw [Real.rpow_def_of_pos (by positivity [partition_pos (G:=G) (n:=n) β])]
  apply Real.exp_le_exp.mpr
  have hl := partition_bill G n hβ
  have hl : N*(-(16*levy G β)) ≤ Real.log (partition G n β) := by
    apply le_trans _ (Real.log_le_log (Real.exp_pos _) hl); rw [Real.log_exp,hc]; unfold N; ring_nf; rfl
  change Real.log (Real.exp (-β*N*(r^2/2)) / partition G n β) * N⁻¹ ≤ _
  rw [Real.log_div (Real.exp_pos _).ne' (partition_pos _).ne',Real.log_exp,←div_eq_mul_inv,div_le_iff₀ h0]
  nlinarith only [hl]

def cutoff (G:Gauge) (β:ℝ) (k:ℕ) := Real.sqrt (1+32*levy G β+k*Real.log β)
def tax (G:Gauge) (β:ℝ) (k:ℕ) := (cutoff G β k)^k + k*(2:ℝ)^k

lemma cutoff_pos (G : Gauge) {β:ℝ} (k:ℕ) (hb:1≤β) : 1 ≤ (cutoff G β k) := by
  apply Real.one_le_sqrt.mpr
  have he : 1 ≤ 4*Real.sqrt β := one_le_mul_of_one_le_of_one_le (by norm_num) (Real.one_le_sqrt.mpr hb)
  have hv : 0≤levy G β:=by unfold levy; positivity [Real.log_nonneg he]
  linarith only [hv, mul_nonneg (Nat.cast_nonneg k) (Real.log_nonneg hb)]

lemma tax_pos (G : Gauge) {β:ℝ} (k:ℕ) (hb:1≤β) : 0<tax G β k :=
  add_pos_of_pos_of_nonneg (pow_pos (zero_lt_one.trans_le (cutoff_pos G k hb)) _) (by positivity)

lemma bare_moment (G : Gauge) {k:ℕ} (p : Fin k→Face (Per n)) {β:ℝ} (h:4∣n.val) (hb : 1≤β) :
    ∫ U, ∏ i, (Real.sqrt β * G.chord (faceValue U (p i))) ∂law G n β ≤ tax G β k := by
  let C := cutoff G β k
  let t := Real.sqrt β
  have ht : 0<t := Real.sqrt_pos.mpr (zero_lt_one.trans_le hb)
  have hc : 0<C := zero_lt_one.trans_le (cutoff_pos G k hb)
  let s:=C/t
  have hs : 16*levy G β-β*s^2/2 ≤ -Real.log t*k := by
    have he : 1 ≤ 4*Real.sqrt β := one_le_mul_of_one_le_of_one_le (by norm_num) (Real.one_le_sqrt.mpr hb)
    have hv : 0≤levy G β:=by unfold levy; positivity [Real.log_nonneg he]
    have hR : β*s^2=C^2 := by unfold s; rw [div_pow,show t^2=β from Real.sq_sqrt (by linarith)]; field_simp
    rw [hR,show C^2=_ from Real.sq_sqrt (by have ho:=mul_nonneg (Nat.cast_nonneg k) (Real.log_nonneg hb); linarith : 0≤1+32*levy G β+k*Real.log β)]
    unfold t; rw [Real.log_sqrt (by linarith)]; ring_nf; linarith
  let f v := fun U : Config G n => G.chord (faceValue U (p v))
  let B i := {U|s ≤ f i U}
  let e (i:Fin k) := (B i).indicator (fun _=>(1:ℝ))
  have he : ∀ i, MeasurableSet (B i) := fun i=> measurableSet_le measurable_const ((G.continuous_chord.comp (continuous_travel ..)).measurable)
  let D := law G n β
  have hf (i) : Integrable (e i) D := ((integrable_const (1:ℝ)).indicator (he i))
  have hI (i:Fin k) : (2*t)^k*D.real (B i) ≤ (2:ℝ)^k := by
    have hE := bare_tail G (p i) h (div_pos hc ht) hb
    have hD : (2*t)^k*Real.exp (-Real.log t*k) = (2:ℝ)^k := by
      rw [show -Real.log t *(k:ℝ)=(k:ℝ)*(-Real.log t) by ring, Real.exp_nat_mul, Real.exp_neg, Real.exp_log ht, ← mul_pow, mul_inv_cancel_right₀ ht.ne']
    exact mul_le_mul_of_nonneg_left (hE.trans (Real.exp_le_exp.mpr hs)) (by positivity) |>.trans_eq hD
  let f' := fun U => ∏ i, t*f i U
  calc
    ∫ U, f' U ∂D ≤ ∫ U, C^k + (2*t)^k*(∑ i, e i U) ∂D := by
      apply integral_mono_of_nonneg (Eventually.of_forall (fun U=>Finset.prod_nonneg (fun _ _=>mul_nonneg ht.le (G.chord_nonneg _)))) ((integrable_const _).add ((integrable_finsetSum _ (fun i _=>hf i)).const_mul _)) (Eventually.of_forall fun U=>?_)
      by_cases hx : ∀ i, f i U < s
      · have hM : ∀ i : Fin k, t*f i U ≤ C := fun i=> (by rw [mul_comm]; exact (lt_div_iff₀ ht|>.mp (hx i)).le : t*f i U ≤ C)
        apply le_add_of_le_of_nonneg _ (by exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun i _=>Set.indicator_nonneg (fun _ _=>zero_le_one) U)))
        exact (Finset.prod_le_prod (fun i _=>mul_nonneg ht.le (G.chord_nonneg _)) (fun i _=>hM i)).trans_eq (by simp)
      push Not at hx
      obtain ⟨z,hz⟩:=hx
      have hv : 1≤∑ i, e i U := by
        calc
          1 = e z U := ((B z).indicator_of_mem hz (fun _ => (1 : ℝ))).symm
          _ ≤ _ := Finset.single_le_sum (fun i _=>Set.indicator_nonneg (fun _ _=>zero_le_one) _) (Finset.mem_univ _)
      apply le_add_of_nonneg_of_le (pow_nonneg hc.le _) ((le_mul_of_one_le_right (by positivity) hv).trans' ?_)
      exact (Finset.prod_le_prod (fun i _=>mul_nonneg ht.le (G.chord_nonneg _)) (fun i _ => mul_le_mul_of_nonneg_left (G.chord_le_two _) ht.le)).trans_eq (by simp; ring)
    _ ≤ _ := by
      rw [integral_add (integrable_const _) ((integrable_finsetSum _ (fun i _=>hf i)).const_mul _),integral_const,probReal_univ,one_smul,integral_const_mul,
        integral_finsetSum _ (fun i _=>hf i), Finset.mul_sum]
      have hE i : ∫ U, e i U ∂D = D.real (B i) := by unfold e; rw [integral_indicator (he i),setIntegral_const,smul_eq_mul,mul_one]
      unfold tax
      apply add_le_add le_rfl
      simp_rw [hE]; apply (Finset.sum_le_sum (fun i _=>hI i)).trans_eq; simp
end YM.Trace2.BareEstimate
