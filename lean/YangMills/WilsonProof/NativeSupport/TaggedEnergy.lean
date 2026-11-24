import YangMills.WilsonProof.NativeSupport.FrozenPicture
import YM.Push.GRID_APPROXIMATION.Cone

/-! The literal fresh energy of a counted path cell, including every tag branch. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.InletSusceptibility
open RG Tree Lattice Wilson Cells RGComparison.Core16 YM.Pressure
open Push.BetaTransport Push.GridApprox WilsonUniformUnmarkedInletEnergySites
open scoped Classical
variable {G : Gauge} {n c f : Side}

theorem fresh_local (S : StepData c f) (T : Forest S.ratio) (d : Descent n f)
    (h : S.patch.Branches S.kernel G) (b : Bond c) (s t : (d.push S T).Tags)
    (x y : Descent.Fields G (d.push S T)) (V W : Config G c)
    (left : s.1.1 b.1 = t.1.1 b.1) (right : s.1.1 (b.1+step b.2) = t.1.1 (b.1+step b.2))
    (tag : s.1.2 b = t.1.2 b) (held : V b = W b)
    (p : Agrees (window (S.ratio.embed b.1) (reach S.patch))
      (T.drape (x ∘ Sum.inl)) (T.drape (y ∘ Sum.inl)))
    (q : Agrees (window (S.ratio.embed (b.1+step b.2)) (reach S.patch))
      (T.drape (x ∘ Sum.inl)) (T.drape (y ∘ Sum.inl))) :
    cell G (d.push S T) s V x (Sum.inl b) = cell G (d.push S T) t W y (Sum.inl b) := by
  have conn := connector_dep S h b s.1.1 t.1.1 left right p q
  simp only [cell,Sum.elim_inl,StepData.prediction,conn,tag,held]

/-- A disk estimate for the actual multiplicative reweighting of a fresh bond. -/
theorem fresh_disk (S : StepData c f) (T : Forest S.ratio) (d : Descent n f)
    (b : Bond c) (t : (d.push S T).Tags) (x : Descent.Fields G (d.push S T))
    (V : Config G c) (z : ℂ) (small : ‖z‖ * (2*S.kernel.penalty) ≤ 1) :
    ‖Complex.exp (z * (cell G (d.push S T) t V x (Sum.inl b) : ℂ)) - 1‖ ≤
      2 * (‖z‖ * (2*S.kernel.penalty)) := by
  let a := V b * (S.prediction (T.drape (x ∘ Sum.inl)) t.1 b)⁻¹
  change ‖Complex.exp (z * (linkEnergy S a : ℂ)) - 1‖ ≤ _
  have he : ‖z * (linkEnergy S a : ℂ)‖ ≤ ‖z‖ * (2*S.kernel.penalty) := by
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg ((link_estimate S).nonneg a)]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    simpa [linkCap,mul_comm] using (link_estimate S).bound a
  exact (Complex.norm_exp_sub_one_le (he.trans small)).trans
    (mul_le_mul_of_nonneg_left he (by norm_num))

end YM.Integration.InletSusceptibility
