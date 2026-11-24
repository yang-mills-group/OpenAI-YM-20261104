import YM.FVA2.Lambda.Scrap
/-!
# Compute the slope using the concrete continuum and comparison here

`β` for **increasing inverse length**. Using actually supplied pole convention.
The recipe (`lamps`): compute the three marginal derivatives called `pole`
(in `Capture`; scale derivatives of the matching data, not dimensional
parameter poles). They are detected by the WW, CU and S,C,C tests there.
The calculation of the values on those tests uses the quite substantial direct
integrals (`Lambda/{Rate,Scrap}` etc.), and for the last, `RoseS.point`.

Then the leading beta coefficient is the one from `ms_to_position_slope`,
applies in **both** the position and the MS variables (proof goes through
`TaylorOKF`; specifically `lamps` uses its `Fixed` bulk input). That theorem
also gives the shift behavior already at finite log argument, as in
`Lambda/Run`. ν argument below is log of the MS ν, as in `Teller/Mass`.
No claim about nonperturbative UV estimates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Lambda.VertexSlope
open Function Filter Set Finset MeasureTheory Real Metric Lattice
open MS MS.Plane MS.Momentum MS.Arts MS.Koszul MS.Landau MS.Landau.Detect
open MS.Wind MS.Wind.Modeled MS.Heat MS.Heat.Signal MS.High MS.Tone MS.Tone.Frame MS.Color MS.Native
open MS.Arc MS.Rock MS.Rock.Path MS.Motif MS.Hem MS.Hem.Mell MS.Outlook MS.Halo MS.Alps MS.City MS.Plane.Flux
open MS.Book MS.Book.Convolve MS.Dock MS.Train MS.Pearl MS.Emit MS.Book.Program MS.High.Knobs
open Gaussian (b₀)
open Canvas (quad high pole)
open Complex (I)
open scoped Topology ContDiff BigOperators Classical InnerProductSpace
variable {G:Gauge}{X:T ( Flats G )}{Y:T ( Coat G )} (hm : leader G X (gloss (pulseX G)) Y) (h:G.Simple)
variable {p:Team}(ht:Fixed ( col ( skyline G p ) ) ( high X ) true 4 1)
/-- $b$ manuscript positive asymptotic freedom with generator convention increasing inverse-length. $G.slopeConstant=2*b G$ normalized for $β_h$. -/
abbrev b (G:Gauge):ℝ:=11*G.casimir/(48*Real.pi^2)
lemma eq_b : G.slopeConstant=2*b G := by unfold b Gauge.slopeConstant; ring
include hm h ht
lemma lamps (x:ℝ): pole (p 3).coupling x= b G ∧ pole (p 2).waveA x = -(13/6)*G.casimir*b₀ ∧ pole (p 2).waveC x= - b G:= by
    obtain ⟨i,j,k,hk⟩:= Hue.Agent.Signal.marked h
    obtain hW:= ( Canvas.salaries hm x 0 h ht i ).symm.trans (Lathe.project_w i h hm x); obtain hQ := ( Canvas.chargeC hm x 0 h ht i ).symm.trans ( Lathe.project_q i h hm x ); obtain hS:= ( Canvas.ghost_tok hm x 0 h ht i j k ).symm.trans ( RoseS.point i j k hm );
    rw [ BranchR.walkW ] at hW; rw [ BranchR.walkC ] at hQ; obtain hm':= (mul_eq_zero.mp hS).resolve_right (show (↑(Mark.LieColor i j k):ℂ)≠0 from by exact_mod_cast hk );
    obtain hw' := congr_arg Complex.re hW; obtain hV := congr_arg Complex.im hQ; obtain hs:= congr_arg Complex.re hm'; simp only [Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.sub_re,Complex.sub_im,Complex.ofReal_im,Complex.ofReal_re,Complex.I_re,Complex.I_im,Complex.neg_re,Complex.neg_im] at hw' hV hs; norm_num at hs hw' hV; -- norm_num oversimplifies.Comm
    have he : b G=11/3*G.casimir*b₀:= by rw [Gaussian.b0]; unfold b; ring
    -- linear eliminate with he
    rw [ he ]; refine ⟨ ?_, ?_,?_ ⟩ <;> linarith
end YM.FVA2.Lambda.VertexSlope
namespace YM.FVA2.Lambda.Crest
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical
open Dframe Reg.Point Reg.Token Reg.Unique Reg.Choice _root_.YM.FVA2.Scale
open YM.FVA2.Scale.Facets Scale.Level Scale.Equator Scale.Measure Scale.Jury
open Scale.Meter Scale.GroupS Scale.Beta
variable {G:Gauge}(ν:ℝ)(Y:XSpace.Initialize G){V:XSpace.Normalize.Store G}(K:XSpace.Rose.Pick V){O: Booked (Press.portDeck G)}(T:MS_Data G O)
variable (S:Prescription (Press.portDeck G)) (t:ℝ)(h:G.Simple)(hs:TaylorOKF T (Press.wickInput Y) S)(hr:Favors.Horder S)(hu:Ace.UnitP S)
local notation "γ" => Scale.GroupS.ψ K T ν
local notation "π" => Scale.GroupS.Ψ K T ν
local notation "B" => Scale.Beta.beta
local notation "b0" => VertexSlope.b
include h hs hr hu
theorem ms_to_position_slope (x:ℝ):
        let c :ℂ := -(↑(b0 G):ℂ);
        (∀ i<3, coeff i ( B γ )=0 ∧ coeff i ( B π )=0) ∧
        ( coeff 3 ( B γ )=c ∧ coeff 3 ( B π )=c ∧ ∀ i,Even i→ coeff i (B π)=0 ) ∧
        GroupS.Ψ K T ν t=GroupS.Ψ K T x t ∧
        Program.shift S.team (x-t)=(Program.shift S.team x).subst ( GroupS.Ψ K T ν t ):= by
    intro c; obtain hL:= VertexSlope.lamps T.bulkOK h hs.bulk x; let S':= S; obtain ⟨he,hq⟩:= AxisB.first ν Y K T S h hs hr hu; have hm := LowBound.pace3 ν Y K T S h hs hr hu x; rw [show Polynomial.eval _ _= b0 G from (show Canvas.pole _ _= _ from hL.1)] at hm; -- eq.relation
    refine ⟨ fun i hi=>⟨he i hi,?_⟩, ⟨ hq ▸ hm.symm, hm.symm, LowBound.beta_parity ν Y K T S h hs hr hu ⟩ , ( LowBound.location_free ν Y K T S t h hs hr hu x ).symm, Lambda.Time.scale ν Y K T S t h hs hr hu x ⟩ -- orientation Ψ
    interval_cases i <;> first| exact LowBound.beta_parity ν Y K T S h hs hr hu _ ( by decide )| exact ( warp π (wave ν T) _ (Scale.GroupS.scaleM ν Y K T S h hs hr hu) ( Precise.fitM ν Y K T S h hs hr hu ) ).2 -- namespace wave
variable (F: MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (H:_root_.YM.FVA2.Scale.System.Contract Y K F S)
omit hs hr hu
include H
local notation "ξ"=> Scale.GroupS.Ψ K F ν
local notation "η"=> Scale.GroupS.ψ K F ν
theorem compares (x:ℝ): let c :ℂ := -(↑(b0 G):ℂ); (∀ i<3, coeff i ( B η )=0 ∧ coeff i ( B ξ )=0) ∧ ( coeff 3 ( B η )=c ∧ coeff 3 ( B ξ )=c ∧ ∀ i,Even i→ coeff i (B ξ)=0 ) ∧ GroupS.Ψ K F ν t=GroupS.Ψ K F x t ∧ Program.shift S.team (x-t)=(Program.shift S.team x).subst ( GroupS.Ψ K F ν t ):= by obtain ⟨hs,hr,hu⟩:= H.toMission.toSchemeV.born; exact ms_to_position_slope ν Y K F S t h hs hr hu x
end YM.FVA2.Lambda.Crest
