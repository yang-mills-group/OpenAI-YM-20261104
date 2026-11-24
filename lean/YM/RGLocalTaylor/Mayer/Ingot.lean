import YM.RGLocalTaylor.Mayer.Tariff

/-!
# Prices even on mixed moments, evaluated before any re-assembly. Coupling
power from in-Head Taylor truncation and across the molecule, purchased ALSO
after the ordered V-derivatives.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F F' : Forest S.ratio} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {X : Coat T F} {η r q a Y W d C' A b s μ C v B : ℝ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R}

open Blaze.March PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt

namespace Mayer
variable {ρ discount θ K α uJ vJ e : ℝ} {M : ℕ} {p z : Molecule S}
    {Ξ : Utopia H j v d r C' χ} (h : Awning H Ξ A b discount e uJ vJ k l)
    (he : Approved K θ j M) (ht : Q.goal L s ≤ K) (hr:ρ*Q.goal L s≤1)
    {f' : Head S→ Insert T} {w : Head S→ℝ} (hb : ∀ i∈p \ z, EstFactor Ξ i (f' i) A (w i) α) (hf : ∀ i∈p \ z, 0≤ w i)
    (hF:∀ i∈p \ z,Fits H (f' i) (H.supportP i) j)
    (hp:z⊆p) (hL:∀ i∈z,Exponential i)
    (hz : (M+4:ℝ)*r≤α)
    {N : Captain H j C' d v Y A b r B q n χ} (hn : N.conduit=Ξ) (hρ: 1≤ρ)
local notation "ρ₀" => (((M+1:ℕ):ℝ)*(θ*ρ))
local notation "f₀" => speedBill e uJ α j
-- public denomination includes discount and valence
abbrev stipend (Ξ : Utopia H j v d r C' χ) (p z : Molecule S) (α uJ e discount s : ℝ) (l : ℕ) (w : Head S→ℝ) :=
  speedBill e uJ α j * hitFace Ξ p z w * (1+H.shapeW p)^(l+j) * ((discount * Ξ.rad) ^ (blaze p).card) * s^z.card

include h he ht hr hb hf hF hp hL hz hn hρ
omit ht hr hb hF hp hL hz hn in
lemma stip_check (ha:1≤α) : 0≤ stipend Ξ p z α uJ e discount ρ₀ l w:= by
  unfold stipend; have hx := hitFace_nonneg hf Ξ
  have ht:= h.bSc; have hv:= h.nonneg; have hb:=Ξ.awake
  have hu:= H.positive_volume p; have hθ := he.nonneg; have hc:= h.earn
  unfold speedBill; positivity

lemma coin (ha:1≤α) {V:Config G c} (h' : (roster p).flags=∅)
    (hy:Healthy (Pressure.temp s) (H.unionP p) V) (m:ℕ) (W:Finset (Decors z M)) (hw:∀ u∈W,m ≤ decorOrder u):
    Ore V (fun V=> ∑ u∈W,(tagged H p f' u).onLog H χ p V) v ((ρ^m)⁻¹ * stipend Ξ p z α uJ e discount ρ₀ l w) j := by
  intro E _ _ _ U x hx hu
  by_cases hX : authorized H p
  swap; · have he : ∀ u:Decors z M,∀ V,(tagged H p f' u).onLog H χ p V=0:=fun u V=> Insert.onLog_of_forbidden hX _ _
          refine Brush.zi (Eventually.of_forall (fun i=>?_)) (mul_nonneg (by positivity) (stip_check h ‹Approved ..› hf hρ ha)) zero_le_one
          dsimp only [Function.comp_apply]; simp_rw [he,sum_const_zero]
  let Q(u : Decors z M) y:= (tagged H p f' u).onLog H χ p (U y)
  let Z:= (1+H.shapeW p)^(l+j); let T:= (discount*Ξ.rad)^(blaze p).card; let u:=(ρ^m)⁻¹ * (f₀ *(hitFace Ξ p z w*(θ*ρ)^z.card)*Z*T)
  have H' i (hi:i∈W) : Brush j u 1 (Q i) x:= cluster_cost h he ht hr hb hf hF hp hL hz hn hρ h' ha hX hy i m (hw i hi) E U x hx hu
  have ht : 0 ≤ u:= by
    have hh:= hitFace_nonneg hf Ξ; have ht:= h.bSc; have hv:=h.nonneg; have hb:=Ξ.awake
    have hV:= H.positive_volume p; have hθ:= he.nonneg; have hc := h.earn
    unfold u speedBill Z T; positivity
  apply (Brush.spree W Q (fun _=>u) zero_le_one H').climb _ le_rfl
  rw [sum_const,nsmul_eq_mul]
  have hH : W.card ≤ (M+1)^z.card :=
    (Finset.card_le_card (subset_univ W)).trans_eq (by simp [Decors])
  apply (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hH) ht).trans_eq
  unfold stipend u Z T; push_cast; simp_rw [mul_pow]; ring

lemma coeff_cost (ha:1≤α) {V:Config G c} (h' : (roster p).flags=∅)
    (hy:Healthy (Pressure.temp s) (H.unionP p) V) (m:ℕ) :
    Ore V (coefficient p z H f' χ M m) v ((ρ^m)⁻¹ * stipend Ξ p z α uJ e discount ρ₀ l w) j :=
  coin h he ht hr hb hf hF hp hL hz hn hρ ha h' hy m _ (fun _ hi=> (mem_filter.mp hi).2.ge)

lemma remainder_cost (ha:1≤α) {V:Config G c} (h': (roster p).flags=∅)
    (hy:Healthy (Pressure.temp s) (H.unionP p) V) :
    Ore V ( (original H p z f').onLog H χ p - ∑ m:Fin (M+1),coefficient p z H f' χ M m)
      v ((ρ^(M+1))⁻¹ * stipend Ξ p z α uJ e discount ρ₀ l w) j := by
  intro E _ _ _ U x hx hu
  have ht' : Healthy (Pressure.temp s) (H.unionP p) (U x) := hx.symm ▸ hy
  have hh:= decor_near hp hF M N h' hu ht' 
  have hfQ(V): (∑ m:Fin (M+1),coefficient p z H f' χ M m) V=retained p z H f' χ M V := by rw [Finset.sum_apply]; exact (retained_eq H f' p z M V).symm
  simp_rw [← hfQ] at hh
  exact ((coin h he ht hr hb hf hF hp hL hz hn hρ ha h' hy (M+1) (Finset.univ.filter (fun u:Decors z M=> ¬decorOrder u≤M)) (fun _ hi=> (Nat.not_le.mp (mem_filter.mp hi).2))) E U x hx hu).shimmy hh

end Mayer
end YM.RGLocalTaylor
