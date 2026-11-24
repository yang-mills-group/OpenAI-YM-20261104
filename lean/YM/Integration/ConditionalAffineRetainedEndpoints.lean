import YM.Integration.ConditionalAffinePlaquetteJets
import YM.AnalyticBridge.SECTOR_AFFINE_JETS.Drift
import YM.AnalyticBridge.SECTOR_AFFINE_JETS.Tracks

/-! Rooted response of the original complete coarse plaquette minus its
physical radius cutoff, on the signed independently varied coarse field. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.ConditionalAffineCoarsePlaquettes
open Filter Set Metric Function Lattice Wilson RG Precision Exterior Tree Matrix Pressure Pressure.Tube
open AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset ProjectorNext.Equivariance
open Push.AbsoluteSums Push.Uniform FreeResolvent FreeResolvent.Stars FreeResolvent.TestD
open PhysicalAffineScalarUncut.PathTail
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

def turn {G : Gauge} {c : Side} (s : Signed) (V : Config G c) (B : PriceCoords G c) := pull s 0 (field V B)

theorem turn_flat {G : Gauge} {c : Side} (s : Signed) :
    turn s (1:Config G c) (0:PriceCoords G c)=1 := by
  funext e
  change pull s 0 (field (1:Config G c) 0) e = 1
  rw [field_zero,pull_formula]
  split <;> simp

theorem unit_face {G : Gauge} {c : Side} (i : Cell c) : faceValue (1:Config G c) i = 1 := by
  simp [faceValue,square,travel,Step.pos_read,Step.neg_read]

private def summand {G : Gauge} {c : Side} (s : Signed) (V : Config G c) (W : PathData G)
    (i : Cell c) (R b j : ℕ) (B : PriceCoords G c) :=
  tailWeight W i R b j • (W.row i.2 j).2.atSite (turn s V B) i.1

private theorem regular (G : Gauge) (n : ℕ) {σ : ℝ} (hσ : 0<σ) :
    ∃ r J : ℝ, 0<r ∧ 0<J ∧ ∀ {c : Side} (s : Signed) (V : Config G c) (W : PathData G)
      (i : Cell c) (R b j : ℕ) (B : PriceCoords G c), B∈ball 0 r →
      Allows n (summand s V W i R b j) B ((|tailWeight W i R b j| *Real.exp ((σ/2)*(W.row i.2 j).2.length))*J) := by
  obtain ⟨r,D,hr,hD,H⟩ := coordinates G n
  obtain ⟨N,hN,hN'⟩ := travel_coupon G n D hD.le (δ:=σ/4) (by positivity)
  let B4 := curvatureCost G*travelCost G n 4 D
  let K := G.colorScale⁻¹*(2^n*(2^n*(G.colorScale*B4)))
  let J := 1+|K| *N^2
  refine ⟨r,J,hr,by positivity,?_⟩
  intro c s V W i R b j B hB
  let U := turn s V
  let q := (W.row i.2 j).2
  have hU (e : Bond c) : Allows n (fun y => G.mat (U y e)) B D := by
    have hh := (H B (le_of_lt (by simpa [mem_ball_zero_iff] using hB)) V).1
    dsimp only [U,turn]
    simp_rw [pull_formula]
    split
    · exact (hh _).inverse (f:=fun y => field V y (bonds s 0 e))
    exact hh _
  let o := Work.F03.slotFace q i.1
  have hF : Allows n (fun y => G.curvature (faceValue (U y) o)) B B4 :=
    curvature_price (U:=fun y => faceValue (U y) o) (travel_jets (U:=U) hU _ (le_refl 4))
  have hA := adjoint_cost (travel_jets (U:=U) hU i.1 (w:=q.walk) (show q.walk.length≤q.length from Nat.le_add_right ..)) hF
  let P := Real.exp ((σ/4)*q.length)
  have hp : 0≤travelCost G n q.length D := (travel_jets (U:=U) hU i.1 (w:=q.walk) (show q.walk.length≤q.length from Nat.le_add_right ..)).nonneg
  have hpow : (travelCost G n q.length D)^2≤(N*P)^2 := by gcongr; exact hN' q.length
  have he : P^2=Real.exp ((σ/2)*q.length) := by rw [pow_two,←Real.exp_add]; congr 1; ring
  unfold summand
  simp_rw [Work.F03.atSite_path]
  apply (hA.smul (tailWeight W i R b j)).mono
  have hk := mul_le_mul_of_nonneg_left hpow (abs_nonneg K)
  rw [mul_pow,he] at hk
  have hk' : K*(travelCost G n q.length D)^2≤J*Real.exp ((σ/2)*q.length) := by
    apply (mul_le_mul_of_nonneg_right (le_abs_self K) (sq_nonneg _)).trans
    apply hk.trans
    dsimp only [J]; nlinarith [Real.exp_pos ((σ/2)*q.length)]
  have hw := mul_le_mul_of_nonneg_left hk' (abs_nonneg (tailWeight W i R b j))
  dsimp only [K] at hw
  simpa only [mul_assoc,mul_comm,mul_left_comm,pow_two] using hw

/-- Each actual long path pays its signed endpoint curvature, all original
external derivatives, and the physical truncation in the same coefficient. -/
theorem weighted (G : Gauge) (n : ℕ) {σ : ℝ} (hσ : 0<σ) :
    ∃ δ J : ℝ, 0<δ ∧ 0<J ∧ ∀ {c f : Side} (_S : StepData c f) (s : Signed) (W : PathData G)
      (i : Cell c) (R b : ℕ), 0<b → ∀ {p : Clip} {C Λ : ℝ}, W.Bounds p σ C Λ →
      Point 0 (s.act i.1) δ n (fun B => W.ell (turn s 1 B) i - shorten W R b (turn s 1 B) i)
        (J*(Real.exp (-(σ/2)*((R:ℝ)/b))*C)) := by
  obtain ⟨D,hD,hletters⟩ := field_letters G n
  let K := 1+|curvatureCost G*travelCost G n 4 D|
  let A := Real.exp (n*(1:ℝ)*5)*K
  have hA : 0<A := by unfold A K; positivity
  obtain ⟨d,J,hd,hJ,hcarry⟩ := carried G (κ:=σ/2) (half_pos hσ) n D A hD.le hA
  let δ := min d 1
  have hδ : 0<δ := lt_min hd zero_lt_one
  refine ⟨δ,J,hδ,hJ,?_⟩
  intro c f S s W i R b hb p C Λ hW
  let u j := summand s (1:Config G c) W i R b j
  let w := tailWeight W i R b
  let q j := (W.row i.2 j).2
  let Q j := |w j| *Real.exp ((σ/2)*(q j).length)
  have hp := tail_budget W i R b hb hW
  obtain ⟨r,L,hr,hL,hreg⟩ := regular G (n+1) hσ
  have hreg' (j : ℕ) (B : PriceCoords G c) (hB : B∈ball 0 r) : Allows (n+1) (u j) B (Q j*L) := hreg s 1 W i R b j B hB
  have hQ : Summable (fun j => Q j*L) := hp.2.1.mul_right L
  have h0 : (0:PriceCoords G c)∈ball 0 r := mem_ball_self hr
  have full : (fun B => W.ell (turn s 1 B) i-shorten W R b (turn s 1 B) i) = fun B => ∑' j, u j B :=
    funext fun B => (removed W i R b hW (turn s 1 B)).symm
  rw [full]
  refine ⟨(ConditionalAffineSeries.sum_smooth isOpen_ball (convex_ball (0:PriceCoords G c) r).isPreconnected hQ hreg').contDiffAt (ball_mem_nhds _ hr),?_⟩
  intro l hl
  let U := turn s (1:Config G c)
  have hU : Letters U s.act n D := (hletters S 1 s).1
  have hh (j : ℕ) : Point (0:PriceCoords G c) (s.act i.1) δ n (u j) (Q j*J) := by
    let o := Work.F03.slotFace (q j) i.1
    have hs : o.1=stop i.1 (q j).walk := by
      unfold o Work.F03.slotFace RG.Slot.offset
      rw [wrap_stop_cover,map_zero,add_comm,←Work.E03.stop_add_left]; simp
    have hflat : U 0=1 := turn_flat s
    have hf := face_cost (s:=1) (t:=1) (σ:=1) hU o zero_le_one le_rfl zero_le_one
      (show ‖G.curvature (faceValue (U 0) o)‖≤K*1 by
        rw [hflat,unit_face,G.curvature_unit,norm_zero,mul_one]
        unfold K
        positivity)
      (show (curvatureCost G*travelCost G n 4 D)*1≤K*1 by unfold K; linarith [le_abs_self (curvatureCost G*travelCost G n 4 D)])
    have hf' : Point (0:PriceCoords G c) (s.act (stop i.1 (q j).walk)) δ n (fun B => G.curvature (faceValue (U B) o)) (A*1) := by
      rw [←hs]; simpa only [δ,A,mul_one,one_smul] using hf.mono (min_le_right d 1) (le_refl _)
    have h := hcarry U s.act hU 1 1 zero_le_one zero_le_one le_rfl i.1 (q j).walk _ δ hδ.le (min_le_left ..) hf'
    have hv : ((q j).walk.length:ℝ)≤(q j).length := by exact_mod_cast (show (q j).walk.length≤(q j).length from Nat.le_add_right ..)
    have hh' := (h.mono le_rfl (show J*Real.exp ((σ/2)*(q j).walk.length)*1≤J*Real.exp ((σ/2)*(q j).length) by
      rw [mul_one]
      exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_left hv (half_pos hσ).le)) hJ.le)).scale (w j)
    have hu : u j = fun y => w j • G.adjoint (travel (U y) i.1 (q j).walk)
        (G.curvature (faceValue (U y) o)) := by
      funext y
      change w j • (q j).atSite (U y) i.1 = _
      rw [Work.F03.atSite_path]
    rw [hu]
    simpa only [Q,one_smul,mul_comm,mul_assoc,mul_left_comm] using hh'
  have HE : HasSum (fun j => jet bolt (u j) l 0) (jet bolt (fun B => ∑' j,u j B) l 0) := by
    let k := l.length
    have H' := iterated_at_sum isOpen_ball (convex_ball (0:PriceCoords G c) r).isPreconnected hQ hreg' h0 k (by omega)
    have hsum := (Summable.of_norm_bounded hQ (fun j => (hreg' j 0 h0).norm_le k (by omega))).hasSum
    rw [←H'] at hsum
    exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => PriceCoords G c) G.Color (bolt∘l.get)).hasSum hsum
  let P := (marks G c δ).pay l (s.act i.1)
  have hP : 0<P := (marks G c δ).pay_pos ..
  have hB : SumBudget (fun j => P*‖jet bolt (u j) l 0‖) (J*(Real.exp (-(σ/2)*((R:ℝ)/b))*C)) := by
    refine budget_mono (budget_scale hJ.le hp) (fun _ => mul_nonneg hP.le (norm_nonneg _)) ?_
    intro j; simpa only [mul_comm] using (hh j).bound l hl
  have hN : Summable (fun j => ‖jet bolt (u j) l 0‖) := by
    have H' := hB.2.1.mul_left P⁻¹
    simpa only [←mul_assoc,inv_mul_cancel₀ hP.ne',one_mul] using H'
  rw [←HE.tsum_eq]
  exact (mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hN) hP.le).trans (by rw [←tsum_mul_left]; exact hB.2.2)

end YM.Integration.ConditionalAffineCoarsePlaquettes

/-! The exact retained face and noise matrices carry the original varying
truncation error at each coarse endpoint. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ConditionalAffineRetainedEndpoints
open Lattice Wilson RG Precision Exterior Tree Pressure Pressure.Tube AnalyticBridge.SectorAffine
open AnalyticBridge.SectorAffine.Offset ConditionalAffineCoarsePlaquettes
open scoped BigOperators Classical Topology ContDiff

variable {G : Gauge} {c f : Side} {S : StepData c f}

def endpoint (T : Tube G S) (s : Signed) (R : ℕ) (j : Twin c) (B : PriceCoords G c) :=
  PhysicalAffineScalarUncut.plaquetteRows T.down T.low (turn s 1 B) j-T.Xn R (turn s 1 B) j

def value (T : Tube G S) (s : Signed) (j : Twin c) (B : PriceCoords G c) :=
  PhysicalAffineScalarUncut.plaquetteRows T.down T.low (turn s 1 B) j

def cut (T : Tube G S) (s : Signed) (R : ℕ) (j : Twin c) (B : PriceCoords G c) := T.Xn R (turn s 1 B) j

/-- The direct plaquette cancels identically. The transported arm keeps
its genuine signed path datum and the scale of the omitted fine length. -/
theorem endpoint_price (G : Gauge) (P : Teller G) (n : ℕ) : ∃ d A : ℝ, 0<d ∧ 0<A ∧
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), P.Funds S T → ∀ (s : Signed) (R : ℕ) (j : Twin c),
      Point 0 (s.act j.1.1) d n (endpoint T s R j) (A*Real.exp (-(P.below.width/2)*((R:ℝ)/S.patch.L.val))) := by
  obtain ⟨d,J,hd,hJ,H⟩ := weighted G n P.below.width_pos
  refine ⟨d,J*P.below.paths,hd,mul_pos hJ P.below.paths_pos,?_⟩
  intro c f S T hP s R j
  obtain ⟨a,b,ha,hb⟩ := hP.feeds
  rcases j with ⟨i,q⟩
  cases q
  · change Point 0 (s.act i.1) d n (fun B => shoot T.low (turn s 1 B) i-shoot T.low (turn s 1 B) i) _
    have hz : (fun B : PriceCoords G c => shoot T.low (turn s 1 B) i-shoot T.low (turn s 1 B) i) =
        (0:PriceCoords G c → G.Color) := by funext B; exact sub_self _
    rw [hz]
    exact Point.zero (mul_nonneg (mul_nonneg hJ.le P.below.paths_pos.le) (Real.exp_pos _).le)
  change Point 0 (s.act i.1) d n (fun B => T.down.ell (turn s 1 B) i-
    Pressure.shorten T.down R S.patch.L.val (turn s 1 B) i) _
  simpa only [mul_assoc,mul_comm,mul_left_comm] using H S s T.down i R S.patch.L.val S.patch.L.property hb

/-- All genuine coarse plaquette rows of the uncut source on the same
signed stencil have a finite entry price before the period is chosen. -/
theorem whole (G : Gauge) (P : Teller G) (n : ℕ) : ∃ d A : ℝ, 0<d ∧ 0<A ∧
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), P.Funds S T → ∀ (s : Signed) (j : Twin c),
      Point 0 (s.act j.1.1) d n (value T s j) A := by
  obtain ⟨d,A,hd,hA,H⟩ := endpoint_price G P n
  obtain ⟨D,hD,hletters⟩ := field_letters G n
  obtain ⟨e,J,he,hJ,Q⟩ := bound_plotted G P.below.width_pos n (D:=1) (L:=P.below.paths) P.below.clip hD.le zero_lt_one
  refine ⟨min d e,A+J,lt_min hd he,add_pos hA hJ,?_⟩
  intro c f S T hP s j
  obtain ⟨a,b,ha,hb⟩ := hP.feeds
  have h1 : Point 0 (s.act j.1.1) (min d e) n (endpoint T s 0 j) A := by
    simpa only [Nat.cast_zero,zero_div,mul_zero,Real.exp_zero,mul_one] using (H S T hP s 0 j).mono (min_le_left d e) (le_refl _)
  have h2 : Point 0 (s.act j.1.1) (min d e) n (cut T s 0 j) J := by
    have hp := Q (turn s (1:Config G c)) s.act (hletters S 1 s).1 T.down b hb 1 1 zero_le_one zero_le_one le_rfl
      (by norm_num) 0 S.patch.L.val S.patch.L.property j (fun y _ => by simp [toll,turn_flat,unit_face,G.chord_one])
    have hcut : cut T s 0 j = (fun z : PriceCoords G c => plotted T.down P.below.clip 0
        S.patch.L.val (turn s 1 z) j) := by
      funext z
      unfold cut Tube.Xn
      rw [hP.low]
    rw [hcut]
    simpa only [one_smul,mul_one] using hp.mono (min_le_right d e) (le_refl _)
  apply (h1.add h2).germ
  filter_upwards with B
  exact sub_add_cancel _ _

/-- The small physical endpoint is carried by precisely the two retained
transport sums appearing in the affine row. -/
theorem carried_endpoint (G : Gauge) (P : Teller G) (L : Side) (n : ℕ) :
    ∃ δ M : ℝ, 0<δ ∧ 0<M ∧ ∀ {c f : Side} (S : StepData c f) (T : Tube G S), P.Funds S T → S.patch.L=L →
    ∀ (s : Signed) (R : ℕ), let t := Real.exp (-(P.below.width/2)*((R:ℝ)/L.val))
      (∀ i : Twin f, Point 0 (s.act (S.ratio.parent i.1.1)) δ n
        (fun B => Pressure.zip (T.Φ R (turn s 1 B)) (fun j => endpoint T s R j B) i) (M*t)) ∧
      (∀ i : Bond c, Point 0 (s.act i.1) δ n
        (fun B => Pressure.zip (T.Φ' R (turn s 1 B)) (fun j => endpoint T s R j B) i) (M*t)) := by
  obtain ⟨d,A,hd,hA,H⟩ := endpoint_price G P n
  obtain ⟨Q,hQ,hletters⟩ := field_letters G n
  obtain ⟨e,J,he,hJ,hf⟩ := wide G P L n Q A hQ.le hA
  obtain ⟨r,K,hr,hK,hm⟩ := noise G P n Q A hQ.le hA
  let δ := min d (min e r)
  have hδ : 0<δ := lt_min hd (lt_min he hr)
  refine ⟨δ,max J K,hδ,hJ.trans_le (le_max_left ..),?_⟩
  intro c f S T hP hL s R t
  let U := turn s (1:Config G c)
  have hy (j : Twin c) : Point 0 (s.act j.1.1) δ n (endpoint T s R j) (A*t) := by
    have h := (H S T hP s R j).mono (min_le_left d (min e r)) (le_refl _)
    simpa only [t,hL] using h
  constructor
  · intro i
    have h := hf S T hP hL U (endpoint T s R) s.act (hletters S 1 s).2 R 1 t δ (Real.exp_pos _).le
      zero_le_one le_rfl hδ.le ((min_le_right ..).trans (min_le_left ..)) i (fun j _ => hy j)
    simpa only [Pressure.zip,one_smul,U] using h.mono le_rfl (mul_le_mul_of_nonneg_right (le_max_left ..) (Real.exp_pos _).le)
  intro i
  have h := hm S T hP U (endpoint T s R) s.act (hletters S 1 s).1 R 1 t δ (Real.exp_pos _).le
    zero_le_one le_rfl hδ.le ((min_le_right ..).trans (min_le_right ..)) i (fun j _ => hy j)
  simpa only [Pressure.zip,one_smul,U] using h.mono le_rfl (mul_le_mul_of_nonneg_right (le_max_right ..) (Real.exp_pos _).le)

end YM.Integration.ConditionalAffineRetainedEndpoints
