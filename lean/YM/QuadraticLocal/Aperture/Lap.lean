import YM.QuadraticLocal.Aperture.Slate
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Aperture.Sage
open Function MeasureTheory Filter Finset Lattice Wilson RG Marker
open scoped Topology ENNReal ContDiff BigOperators Classical
open AllOrder AllOrder.Fire AllOrder.Laplace AllOrder.Laplace.SigmaP Response PertExtension PertExtension.Series Radial
open Sunrise Focus Comparison.Cumulants Extra.Trajectories Toggle Drawer
open Multi Comparison.RG02 Comparison.RG02.Order Primitives.GCC PositionX.Gauss
variable {X V:Type} [Fintype V][DecidableEq V]
variable [MeasurableSpace X] (W:X→ℝ) (μ:Measure X) [IsFiniteMeasure μ] (ρ:V→X→ℝ)
variable (hW:RG.Envelope W) (hM:0≤W) (hZ:0<∫ i,W i ∂μ)(hρ:∀ i,RG.Envelope (ρ i))
local notation "𝕊"=> univ
local notation "V₁"=> Knife V
local notation "Z"=> Sage.moment W μ
local notation "P"=> (Knife V × X)
variable {k n:ℕ}
local notation "Region"=> entry_d X
local notation "φ"=> ratioN W μ ρ
local notation "ℱ"=> member ρ
local notation "Fr"=> Sunrise.Focus.census V
set_option quotPrecheck false
local notation "U"=> (Fr).Mode
local notation "Ψ"=> Scatter.transmit (Sunrise.Focus.census V) pose
variable {p:X→ℝ} {f:(V→ℝ)×X→ℝ}
open PowerSeries Comparison.RG02 Assembly
-- data before ANY analytic Lens estimates. Always FULL normalized weighted polynomial.Term polynomial degree witnesses.Order λ.Det.K.Weight ACT study. occupant normalized.
abbrev draft : Poly (Sunrise.Focus.census V):= Poly.inject fun r=> ↑(draws W μ ρ r)
local notation "Pt"=> Focus.onto (univ:Finset V)
local notation "κ"=> (fun _ : V=> (1:ℕ))
local notation "Q"=> draft W μ ρ
local notation "H"=> Fintype.card V
local notation "K"=> C (Q)
local notation "Θ"=> Reveal.tag Fr Focus.pose (φ)
lemma price_space (v:(Focus.census V).Mode) : Launch.index Fr κ v=v.val.card:=by simp [Launch.index]
include hZ
lemma elite : (Q).part (Fr).quiet=1:= by change ↑(Z _)=(1:ℂ); change Complex.ofReal (draws W μ ρ (Fr).quiet)=_; unfold draws; simp_rw [show (Fr).quiet.val=∅ from rfl,Finset.prod_empty,Sage.price_one W μ hZ,Complex.ofReal_one]
omit hZ
include hρ hW
lemma leap : Reveal.tag Fr pose (φ)= Launch.hom Fr (fun _=>1) (PowerSeries.C Q):= by
 ext1 i; ext1 j; rw [Reveal.pointer,Tag_bill W μ ρ hW hρ j i]; let f:= C Q; change _=Launch.see Fr (Launch.slow Fr κ f) j i; rw [Launch.timing]; simp_rw [price_space,f,Launch.see, PowerSeries.coeff_C]; split_ifs with h h' H' <;> first|rfl|omega -- Nat.sub_eq_zero.mpr etc
include hZ
local notation "Δ"=> (Extra.Trajectories.connected (Q))
local notation "C₀"=> LOG φ
local notation "U'"=> Focus.onto (univ:Finset V)
lemma observed_model (r:(Focus.census V).Mode)(hv:r.val.Nonempty): (Scatter.transmit Fr pose (C₀ r.val.card)).part r = (Δ).part r:= by
 have he(i:ℕ) : First.buc (series Fr i (PowerSeries.C Q))= Q:= by rw [First.buc,Order.observation Fr i _ (Nat.zero_le _), coeff_zero_C]
 have hh(i:ℕ) : UnitLeading (series Fr i K):= (First.buc_vac _).symm.trans ((congr_arg (fun i: Marker.Poly Fr=> i.part (Fr).quiet) (he i)).trans (elite W μ ρ hZ))
 have hp:= Reveal.reports_hot Fr pose (φ) (clearR W μ ρ hW hρ) K κ (present W μ ρ hZ) hh (leap W μ ρ hW hρ) r (fun e=> hv.ne_empty (congr_arg Subtype.val e)) (Nat.zero_le 0)
 rw [price_space,Nat.zero_add] at hp; rw [hp]; change (First.buc _).part _=_; rw [Comparison.RG02.Cumulants.orphan (show Order.Symmetric (series Fr 0 K) from ⟨_,rfl⟩) (hh 0),he] -- syntax symmetric
lemma voted (ht:Nonempty V): Complex.ofReal (Toggle.alt (C₀ H))= (Δ).part Pt:= by
 have he:=Toggle.handover (crystal W μ ρ hW hZ hρ H) (0:ℝ) ((Nat.div_one H).le); exact he.symm.trans (observed_model W μ ρ hW hZ hρ Pt Finset.univ_nonempty)
lemma unripe (hk:k<Fintype.card V) : Toggle.alt (C₀ k)=0:= Drawer.seen_s V _ (0:ℝ) (crystal W μ ρ hW hZ hρ k) ((Nat.div_one k).trans_lt hk) -- argument order
end YM.QuadraticLocal.Aperture.Sage
