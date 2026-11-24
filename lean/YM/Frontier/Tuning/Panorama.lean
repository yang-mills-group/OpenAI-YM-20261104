import YM.Frontier.Tuning.StampBounds
set_option autoImplicit false
noncomputable section
namespace YM.Frontier.Tuning.Voice.SheetEstimate
open Function Filter Set Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Bid Reserves Ursell Trees
open ConnectedActivityE6 Shell Channel SliceRows Control Window Census Mask Pulse Itinerary Coat
open Packets Presented Sector Raw ProbabilityTheory Poll Pond ComplexVertex GaussContour LocalContour
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical ENNReal
variable {G : Gauge} {P : Teller G} {c f n : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {α t e d g b : ℝ} {ι : Type*} {R:Rep G f} {Q Q': YM.ConnectedActivityE6.Target G P}{C x μ W:ℝ}{o:Target.Order G W} {L:Side} {H: Cash W x μ L Q o C T R}
variable (E : SheetEstimate H Q' b)
lemma prices_antitone (z β:ℝ) (hOb: μ≥ 0) (hz: β≤z) i : E.pricesAt z i ≤ E.pricesAt β i:=by
    rcases i with i|i <;> unfold pricesAt paidWith Mixed.costs
    · dsimp only [Sum.elim]; split_ifs; unfold packet' steamP Packets.income Target.costs Buy.quote Grant.credit
      dsimp; gcongr
      rfl
    all_goals rfl
local notation "Π" => Q'.costs L μ (b/2) x C
local notation "optional" => rates E.dk (logPrice E.ve E.de) E.warningPaid
local notation "born" => footprints T R Q.halo (radiusB x)
local notation "len" => ConnectedActivityE6.lengths T R
local notation "B₀" => radiusB x
local notation "W₀" => W
-- non-data arguments kept to test at different V.
include H
lemma connect_zero (s:Molecule S) : Mixed.Allowed S Q.halo B₀ Π born len 0 0 0 s ↔ Ac.Spark (Mixed.foot S Q.halo B₀ born) s:=by
  have hp: Mixed.charges S Q.halo B₀ born Π len s≥ 0 := H.positive_volume _
  exact ⟨fun h=> h.1,fun h=>⟨h,Nat.zero_le _,Nat.zero_le _,hp⟩⟩

def rootCost (s:Molecule S):= (∏ i∈s, E.pricesAt (b/2) i)*Real.exp (Q'.ε * H.shapeW s)

def aperture (G : Gauge) (L : Side)(x ε:ℝ) := { z:ℂ| ‖z‖<2*betaF G x L ∧ betaF G x L/2<z.re ∧ strainG G L x*Real.log (‖z‖/z.re) < ε }
lemma price_stamp (X:Coat T F) (K : Molecule S) {z:ℂ} (hx:X.x=x)(hk:X.width=o.K)(hm:X.manifest) {v l : Payload G f} {k:Finset ℕ}(I:BoundAt R v l E.de E.dk) (η:ℝ)
    (hw:0<z.re) (hv: z.re∈Icc (b/2) (2*b)) (hl: μ≥0) (hz : ‖z‖≤ 2*b) (he:strainG G L x*Real.log (‖z‖/z.re) ≤ Q'.ε) : ∀ (H' : Cash W x μ L Q o C T (resetBeta R z.re)), H'.alarms*topStorm S.patch ≤ E.warningPaid →
    ‖stamp (podium S G (H.unionP K) X.B) X k K R v l Q.table z W o.a Q.halo‖ ≤ rootCost E K:= by
   intro N hN
   have hn : Nonempty (Cash W x μ L Q o C T (resetBeta R z.re)):=⟨N⟩
   let J:=podium S G (H.unionP K) X.B
   change ‖∫ Y, rawAt J X k K R v l Q.table z W o.a Q.halo Y ∂F.order G‖ ≤ _
   refine (norm_integral_le_integral_norm _).trans ?_
   let c0:=Real.log (‖z‖/z.re)
   have hb:0≤ strainG G L x:=by unfold strainG; positivity
   have ht : 0≤c0:= Real.log_nonneg (one_le_div hw|>.mpr ((le_abs_self _).trans (Complex.abs_re_le_norm z)))
   have hR := H.laws.data
   have hC Y: ‖rawAt J X k K R v l Q.table z W o.a Q.halo Y‖ ≤ E.rootCost K:=by
     have hf': ∀ i,0≤ E.pricesAt z.re i:=by
       rintro (i|i|i|i)
       · exact E.price_pos (X:=X) hx hk hm hv hz hn I (.inl i)
       · exact E.price_pos (X:=X) hx hk hm hv hz hn I (.inr (.inl i))
       · exact E.price_pos (X:=X) hx hk hm hv hz hn I (.inr (.inr (.inl i)))
       exact (mul_nonneg N.pos ((zero_le_one.trans (topStorm_one _)))).trans hN
     unfold rawAt; apply (evaluate_cap _ _ hw).trans
     unfold markup; rw [Fintype.card_coe]
     apply le_trans (b:=Real.exp (J.card/2*c0) * (Real.exp ((∑ i∈K.toLeft,massPower X i)*c0) * ∏ i∈K, E.pricesAt z.re i))
     · exact mul_le_mul_of_nonneg_left (E.scaledBody (X:=X.wrapY Y) (X':=X) (Q0:=J) hx hk hm hv hz hn N rfl rfl rfl K k I hN) (Real.exp_nonneg _)
     rw [← mul_assoc, ← Real.exp_add,← add_mul (J.card/2:ℝ)]; unfold rootCost; rw [mul_comm (∏ i∈K,_)]
     apply mul_le_mul ?_h (Finset.prod_le_prod (fun _ _=> hf' _) (fun i _=> E.prices_antitone _ _ hl hv.1 _)) (Finset.prod_nonneg fun i _=> hf' i) (by positivity)
     case _h=>
       apply Real.exp_monotone
       have hg := Voice.gain_sum H X K hx (show 0<X.B by unfold Coat.B; rw [hx]; exact lt_of_lt_of_le (by decide : 0<100) hR.room.sight.1)
       dsimp only at hg; dsimp only [J,c0] at *
       exact le_trans (b:= H.shapeW K * strainG G L x * c0) (mul_le_mul_of_nonneg_right (by rw [add_comm,hR.funds.length_eq] at hg;exact hg) ht) (by rw [mul_assoc,mul_comm Q'.ε]; exact mul_le_mul_of_nonneg_left he (H.positive_volume _))
   by_cases hg : Integrable (fun Y=> ‖rawAt J X k K R v l Q.table z W o.a Q.halo Y‖) (F.order G)
   · exact (integral_mono hg (integrable_const _) hC).trans_eq (integral_const _|>.trans (by simp only [probReal_univ,one_smul]))
   rw [MeasureTheory.integral_undef hg]; exact (norm_nonneg _).trans (hC (fun _=>1))

end YM.Frontier.Tuning.Voice.SheetEstimate
