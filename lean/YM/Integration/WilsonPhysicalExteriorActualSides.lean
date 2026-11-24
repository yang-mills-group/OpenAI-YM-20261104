import YM.Integration.WilsonPhysicalExteriorMeshStops
import YM.Integration.WilsonPhysicalExteriorPrescribedSide
import YM.Integration.WilsonEpochPhysicalFront

/-! The very same normalized ultraviolet geometry on every sufficiently
large original Wilson period and on the independently prescribed auxiliary
torus. Both lower period thresholds precede all positions and labels. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorActualSides
open Function Filter Set Real Lattice RG RG16 PhysicalNext.Repeat.Legato
open MS MS.Tide MS.Fleet MS.Orbit MS.Dial MS.Rake MS.Vista MS.Tone
open WilsonPhysicalExteriorResolvedReadout WilsonPhysicalExteriorResolvedCutoff
open WilsonPhysicalExteriorUVStory WilsonPhysicalExteriorMeshStops
open scoped Topology Classical
variable {G:Gauge} (R:Run G)
local notation "C₀" => R.family
local notation "S₀" => R.family.S.scale
local notation "Λ₀" => RG16.Lambda R.family.path.levels

def time (c:ℝ) (k:ℕ) := S₀ (ultraviolet C₀ c k)-S₀ k

theorem time_at_least (c:ℝ) (k:ℕ) : (Λ₀ k)^c≤time R c k := by
  have h:S₀ k+(Λ₀ k)^c≤S₀ (ultraviolet C₀ c k) := by
    unfold ultraviolet crossing
    exact Nat.find_spec (p:=fun j:ℕ=>S₀ k+(Λ₀ k)^c≤S₀ j) _
  unfold time; linarith

theorem time_up (hG:G.Simple) {c:ℝ} (hc:0<c) : Tendsto (time R c) atTop atTop :=
  tendsto_atTop_mono (time_at_least R c) ((tendsto_rpow_atTop hc).comp (Literal.lambda_leads C₀ hG))

theorem time_at_most (hG:G.Simple) (slow:∀m,((R.family.S.block m).val:ℝ)≤log (Λ₀ m))
    {c:ℝ} (hc:1≤c) : ∀ᶠ k:ℕ in atTop,time R c k≤3*(Λ₀ k)^c := by
  filter_upwards [ultraviolet_window C₀ hG slow c] with k hk
  have pos:=Literal.lambda_up C₀ k
  have hpow:=rpow_le_rpow_of_exponent_le (by linarith : 1≤Λ₀ k) hc
  rw [rpow_one] at hpow
  have h2:log (2:ℝ)≤2:=log_le_self (by norm_num)
  have hx:0≤log (Λ₀ k+log 2):=log_nonneg (by linarith [log_nonneg (show (1:ℝ)≤2 by norm_num)])
  unfold time
  linarith [hk.2.2,log_le_self hx,log_le_self (show 0≤Λ₀ k+log 2 by linarith [log_nonneg (show (1:ℝ)≤2 by norm_num)])]

def actual (N per:ℕ) : ℕ := (R.family.side N per).val/4-1

theorem side_value (N per:ℕ) : (dimT walkway (actual R N per)).val=(R.family.side N per).val := by
  rw [fullC];unfold actual
  have hd:4∣(R.family.side N per).val:=R.family.S.side_four N per
  have hp:0<(R.family.side N per).val:=(R.family.side N per).pos
  omega

abbrev Point := ℕ×ℕ
def floor (c:ℝ) (lo:ℕ→ℕ) (k:ℕ) :=
  max (WilsonEpochPhysicalFront.entrance R lo (ultraviolet C₀ c k))
    (4*(WilsonPhysicalExteriorPrescribedSide.count (Λ₀ k)+1))
def channel (c:ℝ) (lo:ℕ→ℕ) : Filter Point :=
  comap Prod.fst atTop ⊓ principal {z|floor R c lo z.1≤z.2}

theorem taking (c:ℝ) (lo:ℕ→ℕ) : Tendsto (Prod.fst:Point→ℕ) (channel R c lo) atTop :=
  tendsto_iff_comap.mpr inf_le_left

theorem all_later {c:ℝ} {lo:ℕ→ℕ} {P:Point→Prop}
    (h:∀ᶠ z in channel R c lo,P z) : ∀ᶠ k:ℕ in atTop,∀ p≥floor R c lo k,P (k,p) := by
  rw [channel,eventually_inf_principal,eventually_comap] at h
  filter_upwards [h] with k hk p hp
  exact hk (k,p) rfl hp

def geometry (c ν:ℝ) : Geo Point :=
  ⟨fun z=>time R c z.1,fun z=>ν-time R c z.1,fun z=>
    (rpow_nonneg (Literal.lambda_pos C₀ z.1).le c).trans (time_at_least R c z.1)⟩
def field {n:ℕ} (c ν:ℝ) (W:Fin n→ℕ→ Cover) : Trial Point (Fin n) where
  profile:=geometry R c ν
  side z:=walkway (actual R (ultraviolet C₀ c z.1) z.2)
  off w z:=W w z.1
  head z:=crane (actual R (ultraviolet C₀ c z.1) z.2)

theorem actual_size {n:ℕ} (c ν:ℝ) (W:Fin n→ℕ→ Cover) (z:Point) :
    (dimT (field R c ν W).side z).val=(R.family.side (ultraviolet C₀ c z.1) z.2).val :=
  side_value R _ _

theorem rooms {n:ℕ} (hG:G.Simple) (slow:∀m,((R.family.S.block m).val:ℝ)≤log (Λ₀ m))
    {c:ℝ} (hc:1≤c) (hc₂:c<2) (lo:ℕ→ℕ) (ν:ℝ) (W:Fin n→ℕ→ Cover)
    (reach:Reach (geometry R c ν) (field R c ν W).off)
    (apart:Resolved (geometry R c ν) (info (field R c ν W).off)) :
    Domain (field R c ν W) (channel R c lo) ν ∧
      Domain (WilsonPhysicalExteriorPrescribedSide.change (field R c ν W) (fun z=>Λ₀ z.1))
        (channel R c lo) ν := by
  let T:=field R c ν W
  let Λ:Point→ℝ:=fun z=>Λ₀ z.1
  have proj:=taking R c lo
  have up:= (time_up R hG (by linarith : 0<c)).comp proj
  have large: Tendsto Λ (channel R c lo) atTop := (Literal.lambda_leads C₀ hG).comp proj
  have bound:∀ᶠ z in channel R c lo,T.profile.θ z≤3*(Λ z)^c :=proj.eventually (time_at_most R hG slow hc)
  have aux:=WilsonPhysicalExteriorPrescribedSide.geometry T Λ reach apart (fun _=>rfl) up large hc₂ bound
  refine ⟨⟨reach,apart,fun _=>rfl,up,?_,fun z=>Cleared _,centered_size _ _ (fun z=>centerD _)⟩,aux⟩
  intro m
  have late:∀ᶠ z:Point in channel R c lo,floor R c lo z.1≤z.2 :=
    mem_inf_of_right (by simp)
  filter_upwards [aux.super m,late] with z hz hl
  apply hz.trans (log_le_log (Vista.δ_p _ _) ?_)
  change ((dimT (WilsonPhysicalExteriorPrescribedSide.site Λ) z).val:ℝ)≤(dimT T.side z).val
  rw [WilsonPhysicalExteriorPrescribedSide.exact_size,actual_size]
  exact_mod_cast (le_max_right _ _).trans (hl.trans ((R.family.S.period_strict.id_le z.2).trans
    (Nat.le_mul_of_pos_right _ (R.family.S.denominator (ultraviolet C₀ c z.1)).pos)))

end YM.Integration.WilsonPhysicalExteriorActualSides
end
