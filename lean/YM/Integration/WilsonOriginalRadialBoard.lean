import YM.Integration.WilsonOriginalRadialDecoderSpring

/-! The same original spring controls every incident plaquette at the real decoder. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalRadialBoard
open Finset Filter Lattice Wilson RG Source Push.Local PhysicalNext PhysicalNext.Repeat Legato
open Pressure
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)
local notation "H" => R.family.path.levels.clock.hatBeta
local notation "spring" => R.family.path.levels.clock.kernel.penalty

private theorem plaquette {n:Side}(V:Config G n)(p:Face (Per n)):
    G.chord (faceValue V p) ≤ 4*(∑e:Bond n,G.chord (V e)):=by
  let S:=∑e:Bond n,G.chord (V e)
  have each (e:Bond n):G.chord (V e)≤S:=single_le_sum (fun e _=>G.chord_nonneg (V e)) (mem_univ e)
  have travelPrice (w:Walk)(x:Site n):G.chord (travel V x w) ≤ w.length*S:=by
    induction w generalizing x with
    | nil => simp [travel,G.chord_one]
    | cons d w ih =>
      have letter:G.chord (d.read V x)≤S:=by
        by_cases back:d.neg
        · rw [Lattice.Step.read,if_pos back,G.chord_inv];exact each _
        · rw [Lattice.Step.read,if_neg back];exact each _
      simpa only [travel,List.length_cons,Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_comm]
        using (G.chord_triangle ..).trans (add_le_add letter (ih (x+d.vec)))
  exact travelPrice (square p.2.val.1 p.2.val.2) p.1

theorem clear (simple:G.Simple):∀ᶠ i:ℕ in atTop,∀{N per:ℕ}(_live:i<N)
    (W:Config G (R.family.side i per)),
    (Real.exp (WilsonOriginalDecoderSpring.bill (R.family.path.levels.clock.op i per)
      (R.family.path.β N per (i+1)) W))^2≤2 →
    flags (R.family.path.rep N per i).p.threshold W=∅:=by
  have rise:=Next.Rank.Station.hat_rate R.family.path.levels simple
  have sp:0<spring:=R.family.path.levels.clock.kernel.penalty_pos
  let c:=Real.log 2/spring
  have price:0≤c:=div_nonneg (Real.log_nonneg (by norm_num)) sp.le
  filter_upwards [(Real.tendsto_sqrt_atTop.comp rise).eventually_ge_atTop (2*c)] with i cash
  intro N per live W small
  change 2*c≤Real.sqrt (H i) at cash
  let β:=R.family.path.β N per (i+1)
  let sum:=∑e:Bond (R.family.side i per),G.chord (W e)
  have hp:0<H i:=zero_lt_one.trans (R.family.path.levels.fits.delayed i)
  have bp:0<β:=Overlay.beta_positive R.makes.wilson live
  have hβ:H (i+1)/2 ≤ β:=(R.makes.wilson.represents N per (i+1) live).band.1
  have hb:H i/2 ≤ β:=(div_le_div_of_nonneg_right (WilsonStartup.Timing.hat_mono R.family.path.levels
    (Gauge.slopeConstant_pos simple).le (Nat.le_succ i)) (by norm_num)).trans hβ
  have θ:(Real.sqrt (H i))⁻¹ ≤ (R.family.path.rep N per i).p.threshold:=by
    rw [show (R.family.path.rep N per i).p=R.family.path.levels.budget i from (R.makes.wilson.represents N per i live.le).vac]
    change _≤(Real.sqrt (H i))⁻¹*Real.exp ((Real.log (Real.log (H i)))^2)
    exact le_mul_of_one_le_right (by positivity) (Real.one_le_exp (sq_nonneg _))
  have lower:c ≤ β*(R.family.path.rep N per i).p.threshold:=by
    calc _ ≤ (Real.sqrt (H i))/2:=by linarith only [cash]
         _ = (H i/2)*(Real.sqrt (H i))⁻¹:=by
           rw [←(Real.sq_sqrt hp.le)] at ⊢
           rw [Real.sqrt_sq (Real.sqrt_nonneg _)]
           field_simp [(Real.sqrt_pos.mpr hp).ne']
         _ ≤ _:=mul_le_mul hb θ (by positivity) bp.le
  rw [←Real.exp_nat_mul,←Real.exp_log (by norm_num:0<(2:ℝ))] at small
  have val:=Real.exp_le_exp.mp small
  change 2*(|β| *(2*spring*sum))≤Real.log 2 at val
  rw [abs_of_pos bp] at val
  have sumCost:(4*sum)*β ≤ c:=(le_div_iff₀ sp).mpr (by nlinarith only [val])
  have ready:4*sum ≤ (R.family.path.rep N per i).p.threshold:=
    (le_of_mul_le_mul_right ((sumCost.trans lower).trans_eq (mul_comm β _)) bp)
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨p,_,bad⟩:=(flags_spec ..).mp hx
  exact (not_lt_of_ge ((plaquette W p).trans ready)) bad

theorem original (simple:G.Simple)(d target:ℕ):
    ∀ᶠ i in atTop,∀{N per D:ℕ}(_live:i<N),1≤(R.family.path.levels.budget i).supportExponent →
      ∀a∈tests (R.family.labels.level d),∀j≤D,
      let W:=WilsonCapturedPrimaryWeakTrialRadial.field R d N per i target D a j
      flags (R.family.path.rep N per i).p.threshold W=∅ ∧
      (Real.exp (WilsonOriginalDecoderSpring.bill (R.family.path.levels.clock.op i per)
        (R.family.path.β N per (i+1)) W))^2≤2:=by
  filter_upwards [clear R simple,WilsonOriginalRadialDecoderSpring.original R simple d target] with i health sell
  intro N per D live fee a ha j hj W
  have ticket:=sell (N:=N) (per:=per) (D:=D) live fee a ha j hj
  exact ⟨health live W ticket,ticket⟩

end YM.Integration.WilsonOriginalRadialBoard
