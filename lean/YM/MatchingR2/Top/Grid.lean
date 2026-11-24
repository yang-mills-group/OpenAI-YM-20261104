import YM.MatchingR2.Top.WireCost
import YM.Trace2.BareEstimate
import YM.Work.E02
import YM.Work.F01

/-! Post-L payments at arbitrary torus regulator. These are *integrated* charges against
Wilson input and its true conditional on the same tree/labels. Every flag and orientation is
there. Here tolls assigned in actual `t` units. Keep all labels even if later using only in a
particular clear box. Only admissibility hypotheses `Larger`, four-divisor and positive scales as
indicated (and e.g. eventual diameter for tying the frame at the winding seam later).
-/

set_option autoImplicit false
noncomputable section
namespace YM.MatchingR2.Top
open RG Function Wilson Lattice MeasureTheory Filter Set Finset Tree Push.SectorMeasure Pressure
open scoped Topology BigOperators ContDiff ENNReal Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f : Side}
variable (S : StepData c f) (F : Forest S.ratio) (β : ℝ) (o : Site c)
variable {p : ℕ}
set_option quotPrecheck false
local notation "X" => All S F G
local notation "t₀" => Real.sqrt β
local notation "V₀" => Config G c
local notation "V₁" => Config G f
local notation "P" => full S F β o G
local notation "j" => S.patch.J
local notation "L" => S.patch.L
local notation "R" => macroR S.patch
variable {n : Side}

def markFace (β : ℝ) (x : Face (Per n)) (U : Config G n) := Real.sqrt β * G.chord (faceValue U x)
lemma markFace_nn (u : Face (Per n)) (U : Config G n) : 0 ≤ markFace β u U := mul_nonneg (Real.sqrt_nonneg _) (G.chord_nonneg _)
lemma markFace_env (u : Face (Per n)) : Envelope (markFace (G:=G) β u) := by
  apply envelope_cart; unfold markFace faceValue; fun_prop
def fineFace (u : Face (Per f)) (x : X) := markFace β u (F.drape x.2.2)
def coarseFace (u : Face (Per c)) (x : X) := markFace β u x.1
lemma coarse_at (u : Face (Per c)) (x : X) : coarseFace S F β u x = markFace β u (turned o x.1) := by
  simp [coarseFace, markFace, turned]

variable (H : S.patch.Branches S.kernel G)
include H
lemma usable_ae : ∀ᵐ x∂ (P), 0 < S.likelihood (F.drape x.2.2) ((tag S).symm x.2.1) := by
  have he : ∀ᵐ x∂ (P), 0 < stamp S F β o x := fromWeight_active _ (stamp_env S F β o H).meas
  apply he.mono
  intro x hx
  change 0 < fineWeight β _*(S.likelihood _ _*_) at hx
  exact pos_of_mul_pos_left (pos_of_mul_pos_right hx (fine_weight_pos ..).le) (noise_pos S β ..).le

-- constant formulas (not containing period order etc): Q0, a1 bind chosen uniform at L, j.
def cost1 (G : Gauge) (K : KernelChoices) (j' : ℕ) (L₀ : Side) := (Pressure.qdc G K j').choose / ((L₀.val : ℝ)^2)
def copCost (G : Gauge) (L₀ : Side) (K : KernelChoices) (j' : ℕ) := (Work.E02.answer G L₀ j' K).choose
def widthPort (U : Patch) : ℝ := ↑(box (macroR U)).card * Fintype.card PlaqAxes
omit H
lemma cost1_pos (G : Gauge) (K : KernelChoices) (j' : ℕ) (L₀ : Side) : 0 ≤ cost1 G K j' L₀ :=
  div_nonneg (Pressure.qdc G K j').choose_spec.1.le (sq_nonneg _)
lemma copCost_pos (G : Gauge) (L₀ : Side) (K : KernelChoices) (j' : ℕ) : 0 ≤ copCost G L₀ K j' :=
  (Work.E02.answer G L₀ j' K).choose_spec.1.le

open Trace2.BareEstimate
variable (h4 : 4∣f.val) (hb : 1 ≤ β) (hp : 0 < p)
include H h4 hb hp
omit h4 in
lemma suffices_slack (u : Edge (Site c)) : LpCharge (P) p (slack S F β o u) (1+collected S β p G) := by
  letI := full_prob S F β o H
  let B:= collected S β p G
  have hg : 1 ≤ 1+B := by
    unfold B collected quartile; have h : 0 ≤ Real.sqrt (2 * (SectorNext.Vacuum.shellBill G S β + ↑p * Real.log t₀) / S.kernel.penalty) := Real.sqrt_nonneg _
    exact le_add_of_nonneg_right (by positivity)
  refine LpCharge.of_integral (slack_env _ _ _ _ _ H) (zero_le_one.trans hg) hp ?_
  simp_rw [Real.norm_of_nonneg (slack_pos S F β o u _), gap_power S F β o p u H]
  exact (weight_power S β p hb).trans (le_trans (le_add_of_nonneg_left zero_le_one)
    ((le_of_eq (pow_one (1+B)).symm).trans (pow_le_pow_right₀ hg hp)))
lemma fineFace_bill (u : Face (Per f)) : LpCharge (P) p (fineFace S F β u) (1 + tax G β p) := by
  letI := full_prob S F β o H
  have ht : 1 ≤ 1 + tax G β p := by have he := tax_pos G p hb; linarith
  let w := markFace (G:=G) β u
  have hg : Envelope (fineFace S F β u (G:=G)) := by
    exact envelope_comp (f:=w) (markFace_env β u) (fullSlice_meas S F)
    
  refine LpCharge.of_integral hg (zero_le_one.trans ht) hp ?_
  let W U := w U ^ p
  have hw : GaugeInvariant W:= by intro k U; simp [W,w,markFace]
  have hV : Envelope W:= envelope_pow (markFace_env β u) _
  simp_rw [fineFace, Real.norm_of_nonneg (markFace_nn β u _)]
  change (∫ i,W (F.drape i.2.2) ∂(P)) ≤ _
  rw [original S F β o H W hw hV]
  have hz := bare_moment G (fun (_:Fin p)=>u) h4 hb
  simp only [Finset.prod_const, Finset.card_univ,Fintype.card_fin] at hz
  exact hz.trans (le_trans (le_add_of_nonneg_left zero_le_one)
    ((le_of_eq (pow_one _).symm).trans (pow_le_pow_right₀ ht hp)))

local notation "t₁" => 1+tax G β p
local notation "t₂" => 1+collected S β p G
local notation "r" => S.ratio
local notation "E" => (box (R))

def basket (a : Site c) (x : X) := ∑ z ∈ box (macroR S.patch), ∑ k : PlaqAxes, fineFace S F β (wrap f z + S.ratio.embed a, k) x
lemma basket_bill (a : Site c) : LpCharge (P) p (basket S F β a) (widthPort S.patch * (t₁)) := by
  letI := full_prob S F β o H
  let b (z:Cover) (k:PlaqAxes) := fineFace S F β (wrap f z + S.ratio.embed a,k) (G:=G)
  let C := ∑ _z ∈ (E), ∑ _ : PlaqAxes, ((t₁) : ℝ)
  have h1 : LpCharge (P) p (basket S F β a) C := LpCharge.fsum (s:=box (R)) (fun z x=> ∑ k, b z k x)
    (fun _=> ∑ _ : PlaqAxes, (t₁)) (fun z _ => LpCharge.fsum _ _ (fun _ _=> fineFace_bill S F β o H h4 hb hp _) hp) hp
  apply h1.relax
  apply le_of_eq; simp only [widthPort,C,sum_const,Finset.card_univ,nsmul_eq_mul, mul_assoc]
omit H h4 hb hp in
lemma basket_port (a : Site c) (x : X) :
    t₀ * Pressure.port S a (F.drape x.2.2) ≤ basket S F β a x := by
  apply (mul_le_mul_of_nonneg_left (Work.F01.port_le S (F.drape x.2.2) a) (Real.sqrt_nonneg β)).trans_eq
  simp_rw [Finset.mul_sum]; rfl

def rainFee (G : Gauge) (p : ℕ) := 4*(1+collected S β p G) + cost1 G S.kernel S.patch.J S.patch.L *
    (widthPort S.patch*(1+tax G β p))

lemma coarseFace_bill (u : Face (Per c)) : LpCharge (P) p (coarseFace S F β u) (rainFee S β G p) := by
  letI := full_prob S F β o H
  let a := u.1; let k := u.2; let d := k.val.1; let e:= k.val.2
  let C := cost1 G S.kernel (j) (L); have hC : 0 ≤ C := cost1_pos ..
  let v (x:X) := slack S F β o (a,d) x + slack S F β o (a+step d,e) x + slack S F β o (a+step e,d) x + slack S F β o (a,e) x + C * basket S F β a x
  have hz (i:Edge (Site c)) := suffices_slack S F β o H hb hp i
  have ht : LpCharge (P) p v (rainFee S β G p) :=
    ((((hz (a,d)).add (hz _)).add (hz (a+step e,d))|>.add (hz (a,e))).add
      ((basket_bill S F β o H h4 hb hp a).scale C)).relax (le_of_eq (by rw [Real.norm_of_nonneg hC]; unfold rainFee C; ring))
  refine ht.monoReal (envelope_comp (markFace_env β u) (measurable_fst (β:=Drawer S F G))) ?_
  filter_upwards [usable_ae S F β o H] with x hx
  let U:= F.drape x.2.2; let V:= turned o x.1; let κ := (tag S).symm x.2.1
  have hh := (Pressure.qdc G S.kernel S.patch.J).choose_spec.2 c f S rfl rfl U V a κ (Pressure.wraps S κ hx a) k
  rw [coarse_at S F β o, Real.norm_of_nonneg (markFace_nn β u V)]
  apply (mul_le_mul_of_nonneg_left hh.2 (Real.sqrt_nonneg β)).trans
  have hs : t₀*fuel (S.prediction U κ) V a k= slack S F β o (a,d) x + slack S F β o (a+step d,e) x + slack S F β o (a+step e,d) x+slack S F β o (a,e) x := by unfold slack pullRead gap; unfold fuel; ring
  unfold v
  rw [mul_add, hs]; apply add_le_add_right -- convention uses right
  rw [show (Pressure.qdc G S.kernel _).choose/ ((S.patch.L.val:ℝ)^2)=C from rfl, mul_left_comm]
  exact mul_le_mul_of_nonneg_left (basket_port S F β a x) hC

end YM.MatchingR2.Top
