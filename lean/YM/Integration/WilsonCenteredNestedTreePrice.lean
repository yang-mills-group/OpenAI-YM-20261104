import YM.Integration.WilsonCenteredNestedTreeWallet
import YM.Integration.WilsonCenteredNestedOrbitWallet

/-! The complete two-vertex raw OPE, with both deposited fields on their
original single rotated and reflected frame.  The terminal projection kills
lower output bands only after every child band has entered the second OPE. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedTreePrice
open Function Filter Set Spec Extraction Table OPE OPE.Orbits OPE.Orbits.Reader OPE.Prescription
open OPE.Log WilsonCenteredNestedLoggedRow WilsonCenteredNestedRealOrbit WilsonCenteredNestedSharedField
open OPE.Nesting OPE.Nesting.Atom WilsonCenteredNestedPairTicket WilsonCenteredNestedPairConvoy
open WilsonCenteredNestedTwoVertex WilsonCenteredNestedProjectedShadow WilsonCenteredNestedRawPair
open WilsonCenteredNestedTerminalOrbit WilsonCenteredNestedRawDiagram WilsonCenteredNestedTicketSites
open WilsonCenteredNestedTreeWallet WilsonCenteredNestedOrbitWallet WilsonCenteredNestedShadowBasis
open WilsonCenteredNestedOrbit WilsonCenteredNestedGross WilsonCenteredNestedThreeArms
open scoped Classical Topology BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

private lemma mass_nonneg {d:Fin 3→ℕ} (v:Labels S d) : 0 ≤ mass v := Finset.sum_nonneg (fun _ _=>norm_nonneg _)

private lemma rates (fac : Facilities C f S) {u : Filter (ℕ×ℕ)} [u.NeBot] (lo : u ≤ f.fuse)
    (ticket : MatrixTicket (C:=C) S F.sector.derivatives u) (d:Fin 3→ℕ) (D m:ℕ) {M η:ℝ}
    (Mn:0≤M) (ηp:0<η) : ∃ j:ℕ,∀ᶠ r:ℝ in 𝓝[>]0,∀(a:ℝ)(z:full.Plot),
      Accept r M η (dates r a) z→∀w∈bands F.sector.derivatives m,∀(k:Ortho)(v:Labels S d),
      toll d w.1 a r * ‖row F Q d D w (Ortho.move k ∘sites z) v‖ ≤
        mass v * ((shell r * shell a)^j * (a/r)^(D+1)) := by
  have src (w:↥(bands F.sector.derivatives m)) :=
    WilsonCenteredNestedTreeWallet.original F Q fac lo ticket d w.val D Mn ηp
  choose j priced using src
  refine ⟨∑w,j w,?_⟩
  filter_upwards [eventually_all.mpr priced] with r atR a z ok w hw k v
  let i : ↥(bands F.sector.derivatives m) := ⟨w,hw⟩
  have hi := Finset.single_le_sum (f:=j) (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)
  have one := one_le_mul_of_one_le_of_one_le (shell_one r) (shell_one a)
  have rp : 0<r := ok.levels.1
  have ap : 0<a := (ok.levels.2.2 (0:Fin 2)).1
  exact (atR i a z ok k v).trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ one hi) (pow_nonneg (div_nonneg ap.le rp.le) _)) (mass_nonneg v))

private lemma scaled_sum {ι:Type} (s:Finset ι) (f:ι→ℂ) (C:ι→ℝ) (u L:ℝ)
    (hn:0≤u) (h:∀i∈s,u*‖f i‖≤C i*L) : u*‖∑i∈s,f i‖ ≤ (∑i∈s,C i)*L := by
  calc
    _ ≤ u*(∑i∈s,‖f i‖) := mul_le_mul_of_nonneg_left (norm_sum_le ..) hn
    _ = ∑i∈s,u*‖f i‖ := Finset.mul_sum ..
    _ ≤ ∑i∈s,C i*L := Finset.sum_le_sum h
    _ = _ := (Finset.sum_mul ..).symm

theorem original (fac : Facilities C f S) {u : Filter (ℕ×ℕ)} [u.NeBot] (lo : u ≤ f.fuse)
    (ticket : MatrixTicket (C:=C) S F.sector.derivatives u) (v:Fin 3→S.Tag) (D m:ℕ) (c:Q.channels m)
    {M η:ℝ} (Mn:0≤M) (ηp:0<η) : ∃(j:ℕ)(A:ℝ),0≤A ∧ ∀ᶠ r:ℝ in 𝓝[>]0,∀(a:ℝ)(z:full.Plot),
      Accept r M η (dates r a) z→∀(k:Ortho)(b:Bool),
      toll (degrees v) m a r * ‖read F Q m m c (restored F Q.port m (trio (sites z)) (voices v) (sites z 0) k b) -
        joined F Q Q.port D m m c (head v) (v 2) (pair (sites z) 2 3) (pair (sites z) 1 4) (sites z 0) k b‖ ≤
      A*((shell r * shell a)^j * (a/r)^(D+1)) := by
  obtain ⟨j,priced⟩ := rates F Q fac lo ticket (degrees v) D m Mn ηp
  obtain ⟨B,Bn,inputs⟩ := input F Q v
  obtain ⟨T,Tn,terminal⟩ := output F Q m c
  let Cw (w:Mode F.sector.derivatives) := B*(T*‖Q.port.loaded w m‖)
  refine ⟨j,∑w∈bands F.sector.derivatives m,Cw w,
    Finset.sum_nonneg (fun w _=>mul_nonneg Bn (mul_nonneg Tn (norm_nonneg _))),?_⟩
  filter_upwards [priced] with r atR a z ok k b
  have rp : 0<r := ok.levels.1
  have ap : 0<a := (ok.levels.2.2 (0:Fin 2)).1
  have fee : 0≤toll (degrees v) m a r := by unfold toll;positivity
  have pos := mul_nonneg (pow_nonneg (mul_nonneg (zero_le_one.trans (shell_one r))
    (zero_le_one.trans (shell_one a))) j) (pow_nonneg (div_nonneg ap.le rp.le) (D+1))
  rw [WilsonCenteredNestedSharedField.original]
  apply scaled_sum _ _ _ _ _ fee
  intro w hw
  by_cases low : w.1 < m
  · rw [WilsonCenteredNestedTerminalOrbit.lower F Q c w low k b,mul_zero,norm_zero,mul_zero]
    exact mul_nonneg (mul_nonneg Bn (mul_nonneg Tn (norm_nonneg _))) pos
  have we : w.1=m := le_antisymm ((full_bands ..).mp hw) (Nat.le_of_not_gt low)
  have bound := atR a z ok w hw k⁻¹ (voices (entrants F v k b))
  rw [WilsonCenteredNestedThreeArms.original,we] at bound
  rw [norm_mul,scalar_norm,←mul_assoc]
  have mixed := mul_le_mul bound (terminal k b (Q.port.loaded w m)) (norm_nonneg _) (mul_nonneg (mass_nonneg _) pos)
  exact mixed.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (inputs k b) pos)
    (mul_nonneg Tn (norm_nonneg _))).trans_eq (by unfold Cw;ring))

end YM.Integration.WilsonCenteredNestedTreePrice
