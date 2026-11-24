import YM.Integration.WilsonLocalKernelWindow
import YM.Pressure.Cost

/-! Local physical plaquette excursions measured relative to their original prediction. -/
noncomputable section
namespace YM.Integration.WilsonLocalPlaquetteWindow
open YM RG Lattice Wilson MeasureTheory Set Filter WilsonLocalKernelConcentration WilsonLocalKernelWindow
open PertExtension.Series PertExtension.Series.Tested
open scoped BigOperators Topology Classical
variable {c f : Side} {G : Gauge} (S : StepData c f)

def bonds (x : Site c) (p : PlaqAxes) : Finset (Edge (Site c)) :=
  {(x,p.val.1),(x+step p.val.1,p.val.2),(x+step p.val.2,p.val.1),(x,p.val.2)}

theorem bond_count (x : Site c) (p : PlaqAxes) : (bonds x p).card ≤ 4 := by
  let B : Finset (Edge (Site c)) := {(x,p.val.2)}
  let e : Edge (Site c) := (x+step p.val.2,p.val.1)
  let d : Edge (Site c) := (x+step p.val.1,p.val.2)
  let a : Edge (Site c) := (x,p.val.1)
  change (insert a (insert d (insert e B))).card ≤ 4
  have hB : B.card = 1 := Finset.card_singleton _
  have he := Finset.card_insert_le e B
  have hd := Finset.card_insert_le d (insert e B)
  have ha := Finset.card_insert_le a (insert d (insert e B))
  omega

theorem wire (A : Finset (Edge (Site c))) (Q V : Config G c) {u : ℝ} (hu : 0 ≤ u)
    (hs : score S A Q V ≤ u) (i : A) :
    Pressure.wire Q V i.val ≤ Real.sqrt (2*u/S.kernel.penalty) := by
  have h := Finset.single_le_sum (s:=Finset.univ) (f:=fun j : A =>
    S.kernel.penalty * G.price (V j.val * (Q j.val)⁻¹))
    (fun j _ => mul_nonneg S.kernel.penalty_pos.le (G.price_range _).1) (Finset.mem_univ i)
  have hprice := h.trans hs
  apply (sq_le_sq₀ (G.chord_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [G.chord_price, Real.sq_sqrt (div_nonneg (by linarith) S.kernel.penalty_pos.le),
    le_div_iff₀ S.kernel.penalty_pos]
  nlinarith only [hprice]

def excursion (x : Site c) (p : PlaqAxes) (Q : Config G c) (u : ℝ) : Set (Config G c) :=
  {V | G.chord (faceValue Q (x,p))+4*Real.sqrt (2*u/S.kernel.penalty) < G.chord (faceValue V (x,p))}

theorem supported (x : Site c) (p : PlaqAxes) (Q : Config G c) {u : ℝ} (hu : 0 ≤ u) :
    excursion S x p Q u ⊆ {V | u ≤ score S (bonds x p) Q V} := by
  intro V hv
  change u ≤ score S (bonds x p) Q V
  by_contra! h
  have hp (e : Edge (Site c)) (he : e ∈ bonds x p) := wire S (bonds x p) Q V hu h.le ⟨e,he⟩
  have H : Pressure.fuel Q V x p ≤ 4*Real.sqrt (2*u/S.kernel.penalty) := by
    unfold Pressure.fuel
    linarith only [hp (x,p.val.1) (by simp [bonds]), hp (x+step p.val.1,p.val.2) (by simp [bonds]),
      hp (x+step p.val.2,p.val.1) (by simp [bonds]), hp (x,p.val.2) (by simp [bonds])]
  exact (not_lt_of_ge ((Pressure.comp Q V x p).trans (add_le_add (le_refl _) H))) hv

theorem conditional (x : Site c) (p : PlaqAxes) (Q : Config G c) (b : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    (∫ V in excursion S x p Q u, S.noise b Q V ∂prior G c) ≤
      ∫ V in {V | u ≤ score S (bonds x p) Q V}, S.noise b Q V ∂prior G c := by
  apply setIntegral_mono_set (S.noise_integrable b Q).integrableOn _ (ae_of_all _ (fun V =>
    supported S x p Q hu (a:=V)))
  exact ae_of_all _ fun V => Finset.prod_nonneg fun i _ =>
    mul_nonneg (inv_pos.mpr (S.penaltyZ_pos b)).le (Real.exp_pos _).le

def observed (x : Site c) (p : PlaqAxes) (b u : ℝ) (U : Config G f) : ℝ :=
  ∑ z, S.likelihood U z * ∫ V in excursion S x p (S.prediction U z) u,
    S.noise b (S.prediction U z) V ∂prior G c

theorem joint (x : Site c) (p : PlaqAxes) (b : ℝ) {u : ℝ} (hu : 0 ≤ u) (U : Config G f) :
    observed S x p b u U ≤ probability S (bonds x p) b u U :=
  Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (conditional S x p _ b hu) (S.likelihood_pos U z)

theorem logarithmic {G : Gauge} (D : Calendar G) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ n : ℕ, ∀ᶠ (t : ℝ) in Tested.germ, ∀ m p : ℕ, (D.op m p).patch.Branches D.kernel G →
    ∀ (x : Site (D.schedule.side m p)) (q : PlaqAxes) (U : Config G (D.schedule.side (m+1) p)),
      observed (D.op m p) x q (t^2)⁻¹ (t^2*(Real.log t)^2) U ≤ C*t^n := by
  choose C hC H using fun k => WilsonLocalKernelWindow.logarithmic D k
  let B := ∑ j ∈ Finset.range 5, C j
  refine ⟨B, Finset.sum_nonneg (fun j _ => (hC j).le),fun n => ?_⟩
  have hall := (Filter.eventually_all_finset (Finset.range 5)).mpr (fun i _ => H i n)
  filter_upwards [hall,Tested.eventually_pos] with t ht hp m p hB x q U
  let k := (bonds x q).card
  have hk : k ∈ Finset.range 5 := Finset.mem_range.mpr (Nat.lt_succ_of_le (bond_count x q))
  have hcost : C k ≤ B := Finset.single_le_sum (fun j _ => (hC j).le) hk
  exact (joint (D.op m p) x q _ (mul_nonneg (sq_nonneg _) (sq_nonneg _)) U).trans
    ((ht k hk m p hB (bonds x q) rfl U).trans (mul_le_mul_of_nonneg_right hcost (pow_nonneg hp.le _)))

end YM.Integration.WilsonLocalPlaquetteWindow
