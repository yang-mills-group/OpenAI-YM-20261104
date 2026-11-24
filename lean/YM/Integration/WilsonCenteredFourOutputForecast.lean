import YM.Integration.WilsonCenteredFourOutputRank
import YM.Integration.WilsonCenteredFourOutputReading
import YM.Integration.WilsonThermometerWeakRunningCoordinates
import YM.Integration.WilsonNormalizedReflectedForm

/-! Engineering and logarithmic price of the independently appointed
four-actor in the common physical frame and on one original MatrixTicket. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredFourOutputForecast
open Function Filter Set Spec Table Climb Extraction Trace Trace.Pilot Trace.Terrace
open GapsContact GapsContact.Ascent GapsContact.Seams Frontier6 OPE OPE.Orbits OPE.Log
open PhysicalNext.Repeat.Legato Next.UVStress PhysMS MeasureTheory XSpace XSpace.Normalize
open FVA2 FVA2.Scale FVA2.Register FVA2.O FVA2.O.Score MS MS.Land MS.Fleet RG17
open WilsonCenteredFourOutputSensor WilsonMSDictionaryVector
open scoped Topology Classical BigOperators
open private clock from YM.Integration.WilsonThermometerWeakRunningCoordinates
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book}
    (F:Final R.family f S) (Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

theorem ticket {simple:G.Simple} {𝓛:Ultrafilter (ℕ×ℕ)} {arch:Arch R.family} {Y:(Bel R.family.book).Hierarchy}
    (bliss:Bliss F 𝓛 arch Y) (ledger:MatrixTicket (C:=R.family) S F.sector.derivatives (𝓛:Filter _))
    (c:Q.channels 4) : ∃(C:ℝ)(m:ℕ),0≤C ∧ ∀ᶠr in trail,∀v:S.Field 4,
      ‖grade F Q c v‖≤C*dock r^m*r^4*cost F 4 r v:=by
  obtain ⟨p,priced⟩:=WilsonThermometerWeakRunningCoordinates.assessed F ledger (grade F Q c).toLinearMap
    (le_refl 4) (fun e h v=>WilsonCenteredFourOutputRank.lower F Q c h v)
  obtain ⟨t,opened⟩:=every_pool F simple bliss 4
  obtain ⟨j₀,hj⟩:=eventually_atTop.1 priced
  let C:=R.family.path.levels.clock.bar+G.slopeConstant*((t:ℝ)+1)
  have cp:0≤C:=add_nonneg R.family.path.levels.clock.bar_pos.le
    (mul_nonneg (Gauge.slopeConstant_pos (G:=G) simple).le (by positivity))
  refine ⟨C^p,p+t*4+t,pow_nonneg cp _,?_⟩
  have slope:∀ᶠr in trail,r*(dock r)^t≤R.family.S.a j₀:=(lake_line t).eventually (ge_mem_nhds (R.family.S.a_pos j₀))
  have small:∀ᶠr in trail,r≤1:=(ge_mem_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [opened,slope,small,self_mem_nhdsWithin] with r hire paid small pos v
  obtain ⟨j,m,key⟩:=hire
  have sp:R.family.S.a j≤r*dock r^t:=(R.family.S.strictAnti.antitone key.fore).trans key.front.le
  have next:j₀≤j:=R.family.S.strictAnti.le_iff_ge.mp (sp.trans paid)
  have dk:0≤dock r:=zero_le_one.trans (dock_valid r ⟨pos,small⟩)
  have aj:R.family.S.a j≤1:=by simpa using R.family.S.strictAnti.antitone (Nat.zero_le j)
  have sj:0≤R.family.S.scale j:=by
    change 0≤Real.log (R.family.S.a j)⁻¹
    rw [Real.log_inv]
    linarith [Real.log_nonpos (R.family.S.a_pos j).le aj]
  have hat:0≤R.family.path.levels.clock.hatBeta j:=add_nonneg R.family.path.levels.clock.bar_pos.le
    (mul_nonneg (Gauge.slopeConstant_pos (G:=G) simple).le sj)
  have β:=pow_le_pow_left₀ hat (clock F (simple:=simple) key ⟨pos,small⟩) p
  have width:=pow_le_pow_left₀ (R.family.S.a_pos j).le sp 4
  have marked:=hj j next r _ m (key.budget 4 le_rfl) v
  calc
    _≤_:=marked
    _≤(C*dock r)^p*(r*dock r^t)^4*dock r^t*cost F 4 r v:=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul β width (pow_nonneg (R.family.S.a_pos j).le _) (pow_nonneg (mul_nonneg cp dk) _))
        (pow_nonneg dk _)) (Real.sqrt_nonneg _)
    _=_:=by rw [mul_pow,mul_pow,←pow_mul,pow_add,pow_add];ring

local notation "d₄" => (fun _:Fin 2=>4)
variable (J:ℝ→PhysMS.tower S) (Z:WilsonPrescription G) (T:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    (ν:ℝ) (v:Fin 2→RG17.Free R.family 4) (ψ:Test 2) (q:ℕ)
local notation "pred" => (prediction R.family d₄ 4 Z T ν v ψ q)

theorem polynomial : Continuous pred:=by
  unfold prediction assemble WilsonMSDictionaryFarRead.cutoff
  fun_prop

private theorem bounded {E:Type} [SeminormedAddCommGroup E] (x y:E) (h:dist x y < 1):
    ‖x‖≤‖y‖+1:=by
  have e:=dist_triangle x y 0
  simp only [dist_zero_right] at e
  linarith

private theorem registered (simple:G.Simple) (V:Store G) (lead:Leading F J) (c:Q.channels 4)
    (g:ℝ→ℝ) (hg:Coupling G g) {C:ℝ} {k:ℕ} (cp:0≤C)
    (booked:∀ᶠ r in trail,∀v:S.Field 4,‖grade F Q c v‖≤C*dock r^k*r^4*cost F 4 r v):
    ∃W:ℝ,0≤W ∧ ∀ᶠ r in trail,‖grade F Q c (J r 4 (pred (g r)))‖≤W*dock r^k*r^4:=by
  have limit:Tendsto (fun r=>pred (g r)) trail (𝓝 (pred 0)):=
    (polynomial Z T ν v ψ q).continuousAt.tendsto.comp (hg.conforms simple)
  let A:=‖pred 0‖+1
  have Ap:0≤A:=by dsimp only [A];positivity
  obtain ⟨W,wp,paid⟩:=WilsonNormalizedReflectedForm.uniform F J V lead 4 Ap
  have small:∀ᶠr in trail,r≤1:=(ge_mem_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds
  refine ⟨C*W,mul_nonneg cp wp,?_⟩
  filter_upwards [booked,paid,Metric.tendsto_nhds.1 limit 1 zero_lt_one,small,self_mem_nhdsWithin] with r bill wage close small pos
  have value:‖pred (g r)‖≤A:=bounded _ _ close
  have cost:Ascent.cost F 4 r (J r 4 (pred (g r)))≤W:=wage false _ value
  have dk:=zero_le_one.trans (dock_valid r ⟨pos,small⟩)
  exact (bill _).trans ((mul_le_mul_of_nonneg_left cost (by positivity)).trans_eq (by ring))

theorem budget (simple:G.Simple) {𝓛:Ultrafilter (ℕ×ℕ)} {arch:Arch R.family} {Y:(Bel R.family.book).Hierarchy}
    (bliss:Bliss F 𝓛 arch Y) (ledger:MatrixTicket (C:=R.family) S F.sector.derivatives (𝓛:Filter _))
    (V:Store G) (lead:Leading F J) (c:Q.channels 4) (g:ℝ→ℝ) (hg:Coupling G g) :
    ∃ k:ℕ,∀(v:Fin 2→RG17.Free R.family 4)(ψ:Test 2)(q:ℕ),∃C:ℝ,0≤C ∧ ∀ᶠ r in trail,
      ‖grade F Q c (J r 4 (prediction R.family d₄ 4 Z T ν v ψ q (g r)))‖≤C*dock r^k*r^4:=by
  obtain ⟨C,k,cp,booked⟩:=ticket F Q (simple:=simple) bliss ledger c
  exact ⟨k,fun v ψ q=>registered F Q J Z T ν v ψ q simple V lead c g hg cp booked⟩

theorem original (simple:G.Simple) {𝓛:Ultrafilter (ℕ×ℕ)} {arch:Arch R.family} {Y:(Bel R.family.book).Hierarchy}
    (bliss:Bliss F 𝓛 arch Y) (ledger:MatrixTicket (C:=R.family) S F.sector.derivatives (𝓛:Filter _))
    (V:Store G) (lead:Leading F J) (c:Q.channels 4) (g:ℝ→ℝ) (hg:Coupling G g) :
    ∃(C:ℝ)(m:ℕ),0≤C ∧ ∀ᶠ r in trail,
      ‖grade F Q c (J r 4 (pred (g r)))‖≤C*dock r^m*r^4:=by
  obtain ⟨k,all⟩:=budget F Q J Z T ν simple bliss ledger V lead c g hg
  obtain ⟨P,pp,paid⟩:=all v ψ q
  exact ⟨P,k,pp,paid⟩

end YM.Integration.WilsonCenteredFourOutputForecast
