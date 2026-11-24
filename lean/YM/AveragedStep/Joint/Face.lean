import YM.AveragedStep.Joint.Read
import YM.Trace2.BareEstimate
set_option autoImplicit false
noncomputable section
namespace YM.AveragedStep
open Filter Function MeasureTheory Lattice Wilson RG Trace2.BareEstimate
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable (G : Gauge)
/- All powers in the same length convention. Avoid rates C_m → ∞ claims.
τ²=actual β. Not using a continuity hypothesis about the density per volume.
Note our exponent on the log is coarser for convenience in local errors. -/
def lag (τ:ℝ):=1+Real.log τ
lemma lag_ge {τ:ℝ}(h:1≤τ):1≤lag τ:=le_add_of_nonneg_right (Real.log_nonneg h)
lemma lag_mono {τ:ℝ}(h:1≤τ){i j:ℕ}(he:i≤j): lag τ^i ≤ lag τ^j :=
  pow_le_pow_right₀ (lag_ge h) he
lemma bare_paid (k:ℕ) : ∃ C:ℝ, 0 ≤ C ∧
    ∀ τ:ℝ,1≤τ → ∀ (n:Side),4∣n.val→∀ p:Fin k→ Face (Per n),
    (∫ U, ∏ i, (τ*G.chord (faceValue U (p i))) ∂law G n (τ^2)) ≤ C*lag τ^k := by
  let A : ℝ := 8*Fintype.card PlaqAxes + 4*Module.finrank ℝ G.Mat*Real.log 4
  let B : ℝ := 4*Module.finrank ℝ G.Mat
  have hA : 0 ≤ A:=by unfold A; positivity [Real.log_nonneg (by norm_num :(1:ℝ)≤4)]
  have hB : 0 ≤ B:=by unfold B; positivity
  let D:ℝ:=1+32*(A+B)+2*k
  refine ⟨D^k+k*(2:ℝ)^k,by unfold D; positivity,fun τ h n hN p=>?_⟩
  have ht:0<τ:=zero_lt_one.trans_le h
  let l:=lag τ
  have he:1≤l := lag_ge h
  apply le_trans (by simpa only [Real.sqrt_sq ht.le] using bare_moment G p hN (β:=τ^2) (one_le_pow₀ h))
  have hh: levy G (τ^2)=A+B*Real.log τ:= by
    unfold levy; rw [Real.sqrt_sq ht.le,Real.log_mul (by norm_num) ht.ne']; unfold A B; ring
  have hx: cutoff G (τ^2) k ≤ D*l := by
    unfold cutoff; rw [hh,Real.log_pow]
    apply Real.sqrt_le_iff.mpr ⟨by unfold D l; have hl:=lag_ge h; positivity,?_⟩
    push_cast
    have hy : 1≤D*l:=one_le_mul_of_one_le_of_one_le (by unfold D; have he:=Nat.cast_nonneg (α:=ℝ) k; linarith) he
    have hb : B*Real.log τ ≤ B*l:=mul_le_mul_of_nonneg_left (by unfold l lag; linarith) hB
    have hk : (k:ℝ)*(2*Real.log τ) ≤ (k:ℝ)*(2*l):=by gcongr; unfold l lag; linarith
    have ha : A ≤ A*l := le_mul_of_one_le_right hA he
    unfold D at *; nlinarith
  unfold tax
  refine (add_le_add_left (pow_le_pow_left₀ (Real.sqrt_nonneg _) hx k) _).trans ?_
  rw [mul_pow,add_mul (D^k)]
  apply add_le_add (le_rfl)
  exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ he)

variable {c f : Side} (S : StepData c f)
-- any placements, any contacts; this is an *absolute* estimate not
-- Gaussian mgf of a spatial linear combination.
def scaledFace (τ:ℝ) (p:Face (Per f)):Query S G:=fun _ x => τ*G.chord (faceValue x.1 p)
lemma face_admits (τ:ℝ) (p:Face (Per f)):Admits (scaledFace G S τ p):=fun _=>
  env_continuous (continuous_const.mul (G.continuous_chord.comp ((continuous_travel ..).comp continuous_fst)))
lemma scaledFace_pos {τ:ℝ}(ht:0≤τ) (p:Face (Per f)) (i : S.Choices)
    (x : Board G c f) : 0 ≤ scaledFace G S τ p i x := mul_nonneg ht (G.chord_nonneg _)

omit S in
lemma face_paid (m:ℕ) : ∃ C:ℝ,0≤C ∧∀ τ:ℝ,1≤τ →∀ (c f:Side) (S : StepData c f),
    S.patch.Branches S.kernel G→4∣f.val→ ∀ p:Face (Per f),
    readQ S (τ^2) (fun i x=> scaledFace G S τ p i x ^ m) ≤ C*lag τ^m := by
  obtain ⟨C,hC,H⟩:=bare_paid G m
  refine ⟨C,hC,fun τ h c f S hs hf p=>?_⟩
  let X:= fun U:Config G f=>(τ * G.chord (faceValue U p))^m
  have he : Envelope X:=env_continuous ((continuous_const.mul (G.continuous_chord.comp (continuous_travel ..))).pow m)
  change readQ S (τ^2) (fun _ x=>X x.1) ≤ _
  rw [read_fine_marginal S (τ^2) hs he]
  simpa [X] using H τ h f hf (fun _=>p)
end YM.AveragedStep
