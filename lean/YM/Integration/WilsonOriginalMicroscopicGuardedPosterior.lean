import YM.Integration.WilsonOriginalMicroscopicGuardedTrial

/-! Each occupied guard withdrawal is measured against a single original
positive Wilson law. The number of possible failed plaquettes comes from
the original finite stencils and is independent of cutoff, side and sites. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicGuardedPosterior
open Filter Finset MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open PhysicalNext.Repeat.Legato OPE.Therm Push.AbsoluteSums.Animals Pert.Asymptotics
open WilsonOriginalMicroscopicGuardedTrial
open scoped Classical BigOperators Topology

variable {G:Gauge} (R:Run G) (d:Fin 3 → ℕ)
local notation "H" => R.family.path
local notation "κ" => R.family.path.levels.clock.forcedAllowance
def stencils (s:Finset (Fin 3)):ℕ:=(∑a∈s,(R.family.localSection (d a)).stencil.card)*ballCost 2*Fintype.card PlaqAxes
def gross (N p K:ℕ)(v:∀a:Fin 3,R.family.label (d a))(s:Finset (Fin 3)):ℝ:=
  2*∏a∈s,cap R d N p K v a

theorem bill (p K:ℕ)(o:Fin 3→Site (R.family.side K p))(s:Finset (Fin 3)):
    ((footprint R d p K o s).card*ballCost 2*Fintype.card PlaqAxes:ℕ) ≤ stencils R d s:=by
  apply Nat.mul_le_mul_right;apply Nat.mul_le_mul_right
  exact Finset.card_biUnion_le.trans (Finset.sum_le_sum fun a _=>Finset.card_image_le)

theorem paid (simple:G.Simple)(quote:Poetry (H).levels):
    ∀ᶠ K:ℕ in atTop,∀N,K ≤ N→∀p (o:Fin 3→Site (R.family.side K p))
      (v:∀a:Fin 3,R.family.label (d a))(s:Finset (Fin 3)) j (hj:j ≤ K),
      (∫U,‖actualTransport R.family (N:=N) (gap R d N p K o v s) hj U‖ ∂scene (H) N p j) ≤
        gross R d N p K v s*(stencils R d s:ℝ)*(κ) K:=by
  filter_upwards [PhysicalWilsonHotIntegral.divided R simple quote (ρ:=1) zero_lt_one 0] with K all
  intro N nk p o v s j hj
  let X:=footprint R d p K o s
  let E:=SelectedCofactorAnchoredRegister.hot (G:=G) ((H).rep N p K).p.threshold X
  obtain ⟨borel,range,_,signed⟩:=occupied R d N p K o v s
  have mp:0 ≤ gross R d N p K v s:=(norm_nonneg _).trans (range 1)
  have checked:=all N nk p X E (SelectedCofactorAnchoredRegister.measurable _ _)
    (by rw [one_mul]) 0 le_rfl _ mp (gap R d N p K o v s) borel (fun U _=>range U) j hj
  simp only [pow_zero,inv_one,signed] at checked
  exact checked.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by exact_mod_cast bill R d p K o s) mp)
    (Real.exp_nonneg _))

theorem all_orders (simple:G.Simple)(quote:Poetry (H).levels){C ε:ℝ}(hC:0 ≤ C)(ep:0 < ε)(a D:ℕ):
    ∀ᶠ K:ℕ in atTop,∀N,K ≤ N→∀p (o:Fin 3→Site (R.family.side K p))
      (v:∀z:Fin 3,R.family.label (d z))(s:Finset (Fin 3)),
      gross R d N p K v s*(stencils R d s:ℝ) ≤ C/(regulatorRun R.family N p K)^D →
      ∀j (hj:j ≤ K),
        (∫U,‖actualTransport R.family (N:=N) (gap R d N p K o v s) hj U‖ ∂scene (H) N p j) ≤
          ε*(regulatorRun R.family N p K)^a:=by
  filter_upwards [PhysicalWilsonHotIntegral.all_orders R simple quote (ρ:=1) zero_lt_one hC ep a D 0] with K all
  intro N nk p o v s charge j hj
  let X:=footprint R d p K o s
  let E:=SelectedCofactorAnchoredRegister.hot (G:=G) ((H).rep N p K).p.threshold X
  obtain ⟨borel,range,_,signed⟩:=occupied R d N p K o v s
  have mp:0 ≤ gross R d N p K v s:=(norm_nonneg _).trans (range 1)
  have checked:=all N nk p X E (SelectedCofactorAnchoredRegister.measurable _ _)
    (by rw [one_mul]) 0 le_rfl _ mp
    ((mul_le_mul_of_nonneg_left (by exact_mod_cast bill R d p K o s) mp).trans charge)
    (gap R d N p K o v s) borel (fun U _=>range U) j hj
  simpa only [pow_zero,inv_one,signed] using checked

end YM.Integration.WilsonOriginalMicroscopicGuardedPosterior
end
