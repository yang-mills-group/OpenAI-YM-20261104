import YM.RG02.Degree.Capacity
import YM.Work.G05.Taylor

/-!
`Draw.formal` truncation coherence. Uses exactly the input germs through
the corresponding grades. Screens/naming, and any later input basis
normalization affecting vertices must meet this *through every column*;
we don't infer equality from coincident tests or a changed phase prescription.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG02.Fk.Draw
open Filter Function MeasureTheory Set Metric Lattice Wilson RG Precision Tree Supply Bid Marker Extra.Trajectories
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Therm Asym Tangent Grade PowerSeries
open scoped ContDiff Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge}{I J : Type}[Fintype J][DecidableEq J][DecidableEq I][Fintype I]{B : Census I}{C : Census J}{c f : Side}{S : StepData c f}
variable (T : Forest S.ratio) {p : Clip}{R : PathData G}{A A' : Space G f→ℝ}{m m' : ℕ}{W : Space G f→ Poly B}{W' : Space G f→Poly C}
    {η : ChartRatio G} {w : ℝ}{ρ : Dir G c → AxisChart G T}(i : S.Choices)(hp : 0<w)(hr:PriceGap T p R w)(h : Critical T p R ρ)
variable (x : Dir G c)

abbrev VGraph (i : S.Choices)(η : ChartRatio G)(p : Clip)(R : PathData G)(x : Dir G c)(A : Space G f→ℝ)(m : ℕ)(W : Space G f→ Poly B)(ρ : Dir G c→AxisChart G T) := pre T i η p R x A m W ρ

theorem ascends (e : Names C B)(s : ℕ)(hU : Ink m W)
    (H : ∀ z, Through s (PowerSeries.map e.restriction (pre T i η p R x A m W ρ z)) (pre T i η p R x A' m' W' ρ z)) :
    Through s (PowerSeries.map e.restriction (formal T i hp hr h η x A m W)) (formal T i hp hr h η x A' m' W') := by
   let g := pre T i η p R x A m W ρ; let g' := pre T i η p R x A' m' W' ρ
   let V := Grade.restrict e
   have hv (z : AxisChart G T) : Through s (PowerSeries.map e.restriction (Grade.exponential (g z))) (Grade.exponential (g' z)) := by
      change Through s (PowerSeries.map V.toRingHom _) _
      have ht := show basepoint (g z)=0 from (ready T i x ρ hU).2 z
      rw [respects_exp V (restrict_blank e) (g z) ht];
      exact (H z).exponent ((Grade.respects_basepoint V (restrict_blank e) _).trans ht)
   intro k hk; ext a
   rw [PowerSeries.coeff_map]
   change (Grade.restrict e _).part a=_
   rw [Grade.restrict_part,formal,formal, Wick.made_part,Wick.made_part]
   congr 1; funext u
   have he := congr_arg (fun z : Poly C=> z.part a) (hv u k hk)
   rw [PowerSeries.coeff_map] at he; exact he

omit [Fintype I] in
lemma new_power (m d : ℕ){x : Space G f → Poly B}{W : Space G f→Poly B}(ht : Ink m x)(hr : Ink d W)
    (H : ∀ t:ℝ, t>0 → ∀ (u:Config G f), (t:ℂ)^d • x (t,u)=(t:ℂ)^m • W (t,u)) (y : Dir G c) (u : AxisChart G T) :
    Therm.rises m (Pins.ink T y x) u = Therm.rises d (Pins.ink T y W) u := by
   have ha : (fun t => Therm.pins m (Pins.ink T y x) t u)=ᶠ[Tested.germ] fun t=> Therm.pins d (Pins.ink T y W) t u := by
      filter_upwards [Tested.eventually_pos] with t hT
      let U:= Pins.visits T y (t,t • u)
      have ht1:= Complex.ofReal_ne_zero.mpr hT.ne'
      apply smul_right_injective (r:=(t:ℂ)^(m+d)) _ (pow_ne_zero _ ht1)
      change (t:ℂ)^_ • (((t:ℂ)^m)⁻¹ • _)=(t:ℂ)^_ • (((t:ℂ)^d)⁻¹ • _)
      rw [pow_add, mul_comm _ ((t:ℂ)^d),mul_smul,smul_inv_smul₀ (pow_ne_zero _ ht1),mul_smul, smul_comm ((t:ℂ)^d) ((t:ℂ)^m), smul_inv_smul₀ (pow_ne_zero _ ht1)]
      exact H t hT U.2
   exact ((Pins.jobs T y ht).unscale u |>.same (fun i=> ha.mono (fun _ h => congr_arg (fun z => z.part i) h))).uniquely ((Pins.jobs T y hr).unscale u)

-- Through-price test directly on `visits`.
lemma part_way (j : Names C B)(r : ℕ) {d' : ℕ}(w':Space G f→ Poly C)
    (hQ : ∀ k≤ r+2,∀ u, Radial.jet (track T i η p R x A) k u=Radial.jet (track T i η p R x A') k u)
    (hK : ∀ k≤r,∀ l u, PowerSeries.coeff k (onMode (Therm.rises m (Pins.ink T x W) u) (j.share l)) =
      PowerSeries.coeff k (onMode (Therm.rises d' (Pins.ink T x w') u) l)) (H : Ink m W) :
    Through r (PowerSeries.map j.restriction (formal T i hp hr h η x A m W)) (formal T i hp hr h η x A' d' w') := by
   apply ascends T i hp hr h x j r H
   intro z k he; let u := z+Tangent.crest T ρ x
   ext l
   rw [Grade.restrict_coeff]; unfold pre Therm.board
   simp only [map_add,Poly.part_plus,scalar,PowerSeries.coeff_map,Poly.bead,RingHom.coe_mk,MonoidHom.coe_mk,
       OneHom.coe_mk,Poly.part_send]
   simp only [show (j.share l=B.quiet) = (l=C.quiet) from propext ((by rw [← j.quiet]; exact j.inj.eq_iff) : _ ↔ _)]
   congr 1
   · have hh := hK k he l u; simp only [mode_coeff] at hh; exact hh
   split
   next _ => simp only [driven,PowerSeries.coeff_mk,Radial.layers,hQ (k+2) (by omega), hQ 2 (by omega)]
   rfl

-- When no changed exponent order, ordinary restriction.
theorem narrows (j : Names C B)(H : Ink m W) :
    PowerSeries.map j.restriction (formal T i hp hr h η x A m W) = formal T i hp hr h η x A m (fun t=> Grade.restrict j (W t)) := by
   let f:= fun v=> Grade.restrict j (W v)
   ext1 k; refine part_way T i hp hr h x j k (d':=m) f (fun _ _ _=>rfl) ?_ H k le_rfl
   intro r _ l u; rw [mode_coeff,mode_coeff, Therm.rise_coeff,Therm.rise_coeff]; rfl

-- scalar report includes no modes at positive arity; pure vacuum
-- extracted at s=∅ gives the usual log recursion with the explicit Hessian-leading term put back.
lemma vacated (H : Ink m W) :
    den (Grade.logarithm (formal T i hp hr h η x A m W))=lg (den (formal T i hp hr h η x A m W)) := by
   let z := formal T i hp hr h η x A m W
   change den (logarithm z)=_
   have he : basepoint z = 1 := configured T i hp hr h η x H
   have hh := vacuum_cancel (x:=z) (he.trans_ne one_ne_zero)
   have hl:= Grade.vacuum_graphs (x:=z) he
   rw [hl,map_sub] at hh
   rw [sub_eq_zero.mp hh, ← Asym.full_scalar_log B (show coeff 0 (den z)=1 from (PowerSeries.coeff_zero_eq_constantCoeff_apply _).trans he), Grade.den_scalar]
end YM.RG02.Fk.Draw
