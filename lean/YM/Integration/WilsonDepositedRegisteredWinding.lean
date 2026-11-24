import YM.Integration.WilsonRegisteredBareMarkedWinding
import YM.Integration.WilsonFiniteBareHistory

/-! The first registered curvature insertion after its genuine block and
address sum. Every old mark subset is retained with its deposited kernel. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonDepositedRegisteredWinding
open Function Finset Lattice Wilson RG Source Labels Marker WilsonCoeffUV
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp
open WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Blue WilsonCoeffUV.Soil
open WilsonCoeffUV.Embroider WilsonCoeffUV.Winding IndependentSourcePathFamily
open scoped Classical BigOperators
variable {G : Gauge} {ι : Type} [DecidableEq ι] [Fintype ι]
variable {D k : ι → ℕ} {I : ι → Type} [∀ i, Fintype (I i)]

omit [DecidableEq ι] [Fintype ι] in
private theorem tested {V U α : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup U] [NormedSpace ℝ U] {n : Side} {r : ℕ}
    {z : ι → Cover} {S : Finset ι} {A σ c : ℝ} {Q : Ten V (Site n × α) r}
    {F : Ten V (Cloth α) r} (L : V →L[ℝ] U) (hc : ‖L‖ ≤ c)
    (h : MarkU z S Q F σ A) : MarkU z S (L ∘ Q) (L ∘ F) σ (c*A) := by
  have h0 := L.opNorm_nonneg.trans hc
  have apply_bound (v : V) : ‖L v‖ ≤ c*‖v‖ :=
    (L.le_opNorm v).trans (mul_le_mul_of_nonneg_right hc (norm_nonneg _))
  refine ⟨⟨mul_nonneg h0 h.access.1, fun x => (apply_bound _).trans ?_⟩,
    ⟨mul_nonneg h0 h.bill.1, fun x => (apply_bound _).trans ?_⟩,
    ⟨mul_nonneg h0 h.gulf.coal, fun x hx => ?_⟩⟩
  · exact (mul_le_mul_of_nonneg_left (h.access.2 x) h0).trans_eq (mul_assoc ..).symm
  · exact (mul_le_mul_of_nonneg_left (h.bill.2 x) h0).trans_eq (mul_assoc ..).symm
  · change ‖L (Q _) - L (F _)‖ ≤ _
    rw [← map_sub]
    exact (apply_bound _).trans ((mul_le_mul_of_nonneg_left (h.gulf.local_w x hx) h0).trans_eq
      (mul_assoc ..).symm)

omit [Fintype ι] in
/-- Sum the original back addresses, including the engineering factor and
the actual maps on the deposited external test coordinates. -/
theorem addressed (P : Patch) (K : ι → ℕ) (X : Outerm G D) (p : ι → Cover)
    (S : Finset ι) (n : Side) (a r : ℕ) (σ : ℝ) (fee : backRow P.L S → ℝ)
    (h : ∀ j, MarkU p S ((X (splitQ P p S j) S).1 n a r) ((X (splitQ P p S j) S).2 a r)
      σ (fee j)) :
    MarkU p S ((unite P K X p S).1 n a r) ((unite P K X p S).2 a r) σ
      (scalesK P K S * ∑ j, fee j) := by
  classical
  let c := scalesK P K S
  let L (j : backRow P.L S) := c • mend P (inflate P S j) D S
  have hc : 0 ≤ c := scalesBound P K S
  have hL (j) : ‖L j‖ ≤ c := by
    change ‖c • mend P (inflate P S j) D S‖ ≤ c
    apply le_trans (ContinuousLinearMap.opNorm_smul_le c (mend P (inflate P S j) D S))
    rw [Real.norm_eq_abs, abs_of_nonneg hc]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (mend_norm P (inflate P S j) D S) hc
  have each (j) : MarkU p S ((portV P K X p S j).1 n a r) ((portV P K X p S j).2 a r)
      σ (c*fee j) := by
    convert tested (L j) (hL j) (h j) using 1 <;> funext t <;> rfl
  have all := MarkU.sum (g:=Finset.univ) (fun j _ => each j)
  simpa only [unite, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Finset.mul_sum] using all

/-- Finite and cover kernels of the deposited marked row after the first
Wilson block from the actual bare top. Its constants precede the period and
the positions of every parent source. -/
theorem first {e m a r : ℕ} (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m)
    (X : ∀ i, I i → Seed G (D i)) (w : Gear G → ℝ) (hw : ∀ B, 0 < w B)
    (hX : ∀ i b, (X i b).rank ≤ k i + (X i b).head) (K : ι → ℕ)
    (Z S : Finset ι) (hS : S ⊆ Z) (ha : a ≤ e) :
    let Y := Gears Q.draws Q.paid K k (m+1) (m+1) m (independent X)
    ∃ σ B : ℝ, 0 < σ ∧ 1 ≤ B ∧ ∀ (n : Side) (p : ι → Cover),
      MarkU p S ((Y p S).1 n a r) ((Y p S).2 a r) σ B := by
  intro Y
  let P := loose Q.draws m
  let h := (Q.mint (m+1) (by omega)).σ
  have hh : 0 < h := (Q.mint (m+1) (by omega)).width
  let A := diamond G e (mass k Z) h * OriginalIssuedMarkedRows.fee (k:=k) X Q hm w
  have hf := (preblock X (k:=k) (fun _ => 0) Z e
    (w:=4 * max (w (Q.mint m hm).gear) h)
    (mul_pos (by norm_num) ((hw _).trans_le (le_max_left ..))) hX).1
  have hA : 0 ≤ A := mul_nonneg (zero_le_one.trans (diamond_nn G hh)) hf
  obtain ⟨V,hV,quiet⟩ := WilsonFiniteBareHistory.income Q hm hh
  obtain ⟨d,C,σ,_,hσ,step⟩ := WilsonFiniteIncomingMarkedWinding.original
    (D:=D) (k:=k) (r:=r) Q hm hS ha hh
  let B := C*V^d*A^S.card * rimJ (ratioHigh Q.draws Q.paid (m+1) m) a r
  let T := scalesK P K S * ∑ _ : backRow P.L S, B
  refine ⟨σ, max 1 T, hσ, le_max_left .., fun n p => ?_⟩
  change MarkU p S ((Gears Q.draws Q.paid K k (m+1) (m+1) m (independent X) p S).1 n a r)
    ((Gears Q.draws Q.paid K k (m+1) (m+1) m (independent X) p S).2 a r) _ _
  rw [gearUp _ _ _ (Nat.lt_succ_self m), gearTop]
  apply MarkU.more _ (le_max_right 1 T)
  apply addressed P K (fun x => logO Q.draws Q.paid m (m+1) (independent X x) k) p S n a r σ
    (fun _ => B)
  intro j
  let cell := inflate P S j
  let x := chartIn P p cell
  have marked := WilsonRegisteredBareMarkedWinding.registered Q hm (Nat.lt_succ_self m) X w hw Z
    (fun _ => cell) hX p n
  exact step (m+1) (Nat.lt_succ_self m) n (independent X x) p cell
    (IndependentSourcePathFamily.empty X x) (legal X x hX) V A hV hA (quiet n) marked

end YM.Integration.WilsonDepositedRegisteredWinding
end
