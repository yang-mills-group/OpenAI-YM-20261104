import YM.Integration.FVA1Physical.TwoReset.CopyLetters
import YM.QuadraticLocal.Sunrise.Fruit

/-! Probe separated club responses at the actual fine sites, retaining
subdivision offsets on every repetition cover. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.FVA1Physical.TwoReset
open Function Filter Finset Lattice RG Precision Tree YM.Wilson QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Sunrise Comparison Comparison.RG02 Comparison.RG02.Bulk
open Next.SectorChange Marker Multi PertExtension.Series Extra.Trajectories
open AllOrder AllOrder.Floe Further.PhysicalPeriodLimitF933 Macrame Shingle
open Primitives.TwoWave Primitives.TwoWave.RealSlice QuadraticLocal.Aperture AllOrder.Ker
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {V ι α : Type} [DecidableEq V] {c C f F ℓ : Side}
  {J : Passport f V} {R : Census V} (hc : c.val ∣ C.val) (h : f.val ∣ F.val)
  (u : f.val=c.val*ℓ.val) (v : F.val=C.val*ℓ.val)
variable (M : ι→Row J R G α) (S : Club M)
    (L : Layout G) (T : Finset Age)
local notation "s" => Ratio.mk ℓ u
local notation "s'" => Ratio.mk ℓ v
local notation "keys" => Club.Keys M S
local notation "row" j:max => Club.troops M S j
local notation "loan₁" => (fun j:keys=> (row j).lamp)
local notation "lamp₁" => (fun j:keys=> (row j).atom)
local notation "seat₁" => (fun (j:keys) (b:Site C)=>
    (s').assemble (b,(s).residue (row j).center))
local notation "test₁" => convey (coverWin hc) (Bunch.mapC (Club.site M S s))
local notation "eq₁" => LinearLetters.edition univ (QuadraticLocal.Fk.money L T) (copiesLetter h M ∘ Club.stamp M S)
    (fun i => (Club.troops M S i).lamp.toll)

lemma seats_copy : eq₁ = Balcony.displayC loan₁ lamp₁ seat₁ L T test₁ := by
  refine ScatterR.extC _ _ _ (funext fun i=>?_ ) rfl rfl
  funext x U
  unfold LinearLetters.edition LinearLetters.colors Balcony.displayC Balcony.feed Fk.grant Balcony.feedM
  simp_rw [Finset.sum_apply]
  change ∑ k∈univ.filter (fun k:keys=> i.val=(Focus.detailI k).val), ((1:ℂ) • copiesLetter h M (Club.stamp M S k) x U) =
    ∑ k∈univ.filter (fun k:keys=> i.val=(Focus.detailI k).val), ∑ j:Site C, Balcony.pigment loan₁ lamp₁ seat₁ test₁ 1 k j x U
  apply Finset.sum_congr rfl
  intro j _
  unfold copiesLetter
  let F₀ := parcel (splitter hc) ((s).parent (row j).center)
  have he : Function.Injective ((seat₁) j) := fun a b he=> congr_arg Prod.fst ((s').assemble_bijective.1 he)
  rw [one_smul, subdiv_marks u v hc h]
  change (∑ z∈F₀.image ((seat₁) j),_) = _
  rw [sum_image he.injOn]; unfold F₀ parcel
  simp_rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _
  let X:= ((s).parent (row j).center)
  unfold Balcony.pigment
  change (@ite ℂ (splitter hc k=X) (Classical.propDecidable _) _ _) = ↑((if splitter hc k=X then (1:ℝ) else 0)*_)*(1:ℂ)
  split_ifs <;> simp only [one_mul, zero_mul, mul_one, Complex.ofReal_zero]
end YM.Integration.FVA1Physical.TwoReset
