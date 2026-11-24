import YM.Integration.OPEMSReport
import YM.Integration.OPETraceCoupling
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! On the actual compact physical experiment, the whole scalar reader
and the full measured product differ by less than every perturbative
power of the calibrated coupling. The ordinary MS coefficient test for
the two observations is therefore equivalent at every finite order. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.OPEScalarAsymptotic
open Filter Set Asymptotics FVA2 OPE OPE.Orbits PhysMS Spec Trace.Pilot Trace.Sundial
open Pert.Position Maxwell
open scoped Topology BigOperators Classical

variable {G : Gauge} {n i : ℕ}

theorem log_tower (k : ℕ) : Tendsto (fun r : ℝ => r^3*(LogV r)^k) trail (𝓝 0) := by
  have h := (isLittleO_abs_log_rpow_rpow_nhdsGT_zero (k:ℝ)
    (show -(3:ℝ) < 0 by norm_num)).tendsto_div_nhds_zero
  apply h.congr' 
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ)<1 by norm_num)] with r hr
  have hl : |Real.log r| = LogV r := by
    rw [LogV,Real.log_inv,abs_of_nonpos (Real.log_nonpos hr.1.le hr.2.le)]
  change |Real.log r|^(k:ℝ) / r^(-(3:ℝ)) = r^3*(LogV r)^k
  rw [hl,Real.rpow_natCast,Real.rpow_neg hr.1.le,
    show r^(3:ℝ) = r^(3:ℕ) by norm_num,div_inv_eq_mul,mul_comm]

theorem power_flat {g : ℝ → ℝ} (hg : Coupling G g) (hG : G.Simple) (N : ℕ) :
    Tendsto (fun r : ℝ => r^3 / (g r)^N) trail (𝓝 0) := by
  have h := (((log_tower N).mul ((hg.conforms hG).pow N)).div
    (hg.running.pow N) (pow_ne_zero N (inv_ne_zero (Gauge.slopeConstant_pos hG).ne')))
  have he : Tendsto (fun r : ℝ => r^3*(LogV r)^N*(g r)^N / (LogV r*(g r)^2)^N)
      trail (𝓝 0) := by simpa only [Pi.div_def,zero_mul,zero_div] using h
  have hl : Tendsto LogV trail atTop := Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  apply he.congr'
  filter_upwards [hg.positive,hl.eventually_gt_atTop 0] with r hp hz
  rw [mul_pow, ← pow_mul]
  rw [show 2*N = N+N by omega,pow_add]
  field_simp [hp.ne',hz.ne']

def fits {P : Type*} (K : Set (Points n)) (g : ℝ → ℝ) (N : ℕ)
    (a b : ℝ → Points n → P → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ r in trail, ∀ x ∈ K, ∀ p, ‖a r x p-b r x p‖ ≤ ε*(g r)^N

theorem reverse {P : Type*} {K : Set (Points n)} {g : ℝ → ℝ} {N : ℕ}
    {a b : ℝ → Points n → P → ℂ} (h : fits K g N a b) : fits K g N b a := by
  intro ε hε
  filter_upwards [h ε hε] with r hr x hx p
  rw [norm_sub_rev]
  exact hr x hx p

theorem compose {P : Type*} {K : Set (Points n)} {g : ℝ → ℝ} {N : ℕ}
    {a b c : ℝ → Points n → P → ℂ} (h : fits K g N a b) (h' : fits K g N b c) :
    fits K g N a c := by
  intro ε hε
  filter_upwards [h (ε/2) (half_pos hε),h' (ε/2) (half_pos hε)] with r hr hr' x hx p
  calc
    _ ≤ ‖a r x p-b r x p‖ + ‖b r x p-c r x p‖ := norm_sub_le_norm_sub_add_norm_sub .. 
    _ ≤ ε/2*(g r)^N + ε/2*(g r)^N := add_le_add (hr x hx p) (hr' x hx p)
    _ = _ := by ring

variable {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (hJ : Leading F J) (hG : G.Simple) (X : Climb.Scaling S)
    (hR : Foundation F R) (v : Fin n → E C.labels i) (K : Set (Points n))
    (hK : IsCompact K) (hsep : K ⊆ conf n)

def scalar (r : ℝ) (x : Points n) (_ : Viewers F) : ℂ :=
  Short.scalar F R (r • x).ofLp (tags (Frame.born (d := fun _ : Fin n => i) J r v)) 0

def full (r : ℝ) (x : Points n) (p : Viewers F) : ℂ :=
  measured F p (J r) (d := fun _ : Fin n => i) v r x

include hJ hG X hR hK hsep

theorem flat {g : ℝ → ℝ} (hg : Coupling G g) (N : ℕ) :
    fits K g N (full F J v) (scalar F R J v) := by
  obtain ⟨b,hb,a,ha,room⟩ := compact_within K hK hsep
  have hs := Frame.singleton_head (F := F) (R := R) (J := J) (H := hJ)
    (h := hR) (v := v) (M := b) (η := a) (ε := 1) (hM := hb) (hη := ha)
    (he := zero_lt_one) (hg := hG) (X := X)
  intro ε hε
  have ht := Metric.tendsto_nhds.mp (power_flat hg hG N) ε hε
  filter_upwards [hs,ht,hg.positive] with r hr ht hp x hx p
  rw [dist_zero_right,Real.norm_eq_abs] at ht
  have hbound : r^3 ≤ ε*(g r)^N := (div_le_iff₀ (pow_pos hp N)).mp
    ((le_abs_self _).trans ht.le)
  apply le_trans _ hbound
  have hsmall := hr x (room x hx) p
  change ‖full F J v r x p-scalar F R J v r x p‖ ≤ r^((4:ℝ)-1) at hsmall
  norm_num at hsmall ⊢
  exact hsmall

theorem equivalent {g : ℝ → ℝ} (hg : Coupling G g) (N : ℕ) (B : ℝ → Points n → Viewers F → ℂ) :
    fits K g N (scalar F R J v) B ↔ fits K g N (full F J v) B := by
  have h := flat F R J hJ hG X hR v K hK hsep hg N
  exact ⟨compose h,compose (reverse h)⟩

def truncation (V : Warehouse G) {B : MS.Land.Booked (ColorCode.wings G)}
    (M : MS.Land.MS_Data G B) (μ : ℝ) (g : ℝ → ℝ) (N : ℕ) (v : Fin n → E V.F i)
    (r : ℝ) (x : Points n) : ℂ :=
  ∑ k ∈ Finset.range (N+1), (g r : ℂ)^k*Fountain.phys V M μ k x i v

theorem selected (hC : C.Makes) (hV : ∀ a, Bid.pop (C.localSection a))
    {B : MS.Land.Booked (ColorCode.wings G)} (M : MS.Land.MS_Data G B) (μ : ℝ)
    {k : ℝ} (T : PositionX.Bend.Booth k C.labels)
    (W : Pic.pass (Atoll.share C hC hV) hG M T)
    {H : (Climb.Bel C.book).Hierarchy} {Z : Trace.Terrace.Arch C}
    {P P' : ℝ → Spin.change S 4} {a d e : ℝ → ℝ}
    (hf : Trace.Target.FieldComparison F H Z P P' a d e) (j N : ℕ) :
    let V := Atoll.share C hC hV
    let g := fun r => OPETraceCoupling.finiteCoupling (Forge.transfer V M T μ W) j (glo P' r)
    let target := fun r x (_ : Viewers F) => truncation V M μ g N v r x
    fits K g N (scalar F R J v) target ↔ fits K g N (full F J v) target :=
  equivalent F R J hJ hG X hR v K hK hsep
    (OPETraceCoupling.selected_trace hC hV M T μ hG W hf j).1 N _

end YM.Integration.OPEScalarAsymptotic
end
