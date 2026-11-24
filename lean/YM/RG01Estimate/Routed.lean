import YM.RG01Estimate.Activation

/-! Deploy with the same C parameters. At step with forecast expense in place;
onstage new pre-L and delay gates (explicitly from Activation). Supply on
actual reps or their repriced versions with same authorization. No strengthened
gate presumed on all Floral families. Future marker budgets may require more. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Routed
open Function Filter Set Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Window Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Shoot Precision SectorMeasure Oriented Reserves
open PhysicalNext PhysicalNext.Repeat Height Beam Brim Match Song
open Next.Scheduling AnalyticBridge VerifiedReset Collection Quotes UVNext Extra.Iteration Meadow
open PriceCompiler Org Input Supply Pressure.Testing Time
open Roost Opera
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Expense Reprice
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} (g:G.Simple) {M : Metals G} {D : Rolls M.p} {A : Alloy M D} (R : Factor A)
    {ε : ℝ}
local notation "T" => A.B.a

def Allowed := Activation.OnTrack R.recordP R.shape R.t R.span R.prices A.delay

-- expense for THIS step, pre L charged earlier mRequest. Doesn't assume contractive
-- on calendars that didn't set L adequately.
def retention (m : ℕ) :=
    let i:= A.B.a.clock.J m
    let j:= A.B.a.clock.J (m+1)
    let x:= A.B.a.clock.hatBeta m
    Height.away (M.p.profile i)*(R.v j i / ((D.L j).val:ℝ))+ Activation.glyph G (D.L j) x

def spill (m r:ℕ) := (A.B.a.clock.hatBeta (m+1)) ^ (-Fate.aim r-(1/64:ℝ))

variable {m N n : ℕ} {U : RG.Rep G (A.B.a.S.side (m+1) n)}
local notation "Jp" => A.B.a.clock.J (m+1)
local notation "Ip" => A.B.a.clock.J m
local notation "x" => A.B.a.clock.hatBeta m
local notation "L" => D.L (A.B.a.clock.J (m+1))
local notation "k" => A.B.a.params m
local notation "K" => M.p.profile (A.B.a.clock.J m)
local notation "B" => A.B.a.budget m
local notation "Ξ" => Chi.canonical
local notation "Φ" => A.B.kin.alpha N m
variable (h : Allowed R) (hm : m<N) (H : Guide A.B R.shape N m n U) (hf : Opera.Price A.B R.shape N m n U H)
    (hx : U.beta ∈ RG.Shoot.band A.B.a (m+1)) (hp' : U.p=A.B.a.budget (m+1)) (D' : Alliance H H 1 0)
    (u' : D'.units=Equiv.refl _) (E : Set ℕ) (r:ℕ) (hr:2≤r) (hk : r ≤ A.B.a.clock.J (m+1))
    {τ : ℝ} (hδ : Inherit.Debits U E τ) (hτ : τ≤ Fate.debt r G (D.L (A.B.a.clock.J (m+1))) (A.B.a.clock.hatBeta m))

include h hm hf hx hp' u' hr hk hδ hτ
lemma step : Collection.Local (marquee H B) B (Pruned.high H Ξ D' E r Φ) (retention R m*τ+spill (A:=A) m r)
        (CensusStep.hardCost R m) ∧ (∃ w:ℝ, Collection.Local (marquee H B) B (Pruned.low H Ξ D' E r Φ) w (CensusStep.hardCost R m) ∧
      Collection.Local (marquee H B) B (plusone H D' Ξ Φ) w (CensusStep.hardCost R m)) := by
  let K':=K; let e:= R.expense Jp Ip; let S:=ships A.B N m n
  let v:= R.v Jp Ip; let u:= Solo.raise R.t Jp Ip
  have hA : StepStages Jp Ip:= step_paid T m
  have hT:= A.B.valid.pays m
  obtain ⟨hh,hQ,hΡ,hE,hw⟩:=h Jp x hT Ip hA (first_le A.B.valid m) r hr hk
  have hj := params_eq A.B.valid m
  have hak : A.B.a.params m = K':= hj -- notation
  have ht : preExponent B = K'.supportExponent+3:= congrArg (fun v: RG.Stage=>v.supportExponent+3) hj
  have ho : (B).order=K'.order:=congr_arg RG.Stage.order hj
  have hu : (B).power=K'.power:=congr_arg RG.Stage.power hj
  obtain ⟨hV,hY,hK⟩:= R.pledging.agenda _ _ hA
  have hΒ : preExponent B ≤ e.earn:= ht.trans_le hV
  obtain ⟨d,hpos,hS,hZ⟩:= hQ
  obtain ⟨f,g,e,a,b,c,d',s,q,i,j,N',hg,hΞ⟩:= (hh.2 _ _ _ _ (protocol A.B hm R.pledging.conducts.full) U _ H).1
  let P:= R.pledging.conducts
  have he₀:= JointLoad.Heir.Suite.directed n hm A.B (fun m' h'=> P.full _ _ _ (by simp at h'; omega)) P.hearing.covers P.hearing.early
  have hψ := he₀.make; obtain ⟨hp₀,hc⟩:= he₀.pre; have hχ := (he₀.clocks U.beta hx).2
  rw [← hp'] at hψ hp₀ hc hχ
  have he := PriceCompiler.block_eq A.B.valid m
  have hs : Single.Pays H B E Ξ u ((v/(L).val+d)*τ) := hZ _ _ _ S H.laws.data.funds U _ _ _ H B rfl hu
    hψ hK v (he ▸ hp₀) (hu ▸ hc) (he ▸ hχ) K'.order le_rfl _ _ _ _ _ _ _ _ _ _ N' τ (hτ.trans hE.2) E hδ
  have hL : (T|>.params m).supportExponent+3 ≤ R.t Jp Ip:= (ht.trans_le hY)
  have hU : S.down.Bounds S.low (k).width (k).paths (T|>.clock.loopCap m) := A.B.support.cap N m hm.le
  have hx : |U.beta|≤ 2*betaF G x L:= by
    rw [abs_of_nonneg H.laws.intake.positive.le, ← PriceCompiler.beta_eq A.B.valid]; exact hx.2
  have he' : (B).threshold ≤ 2*Pressure.fiery G x L:= by
    have hv:= H.laws.data.room.temperatures; rw [H.laws.data.funds.length_eq] at hv; exact hv
  have hG : (T|>.clock.loopCap m) ≤ ConnectedActivityE6.loopBill G L x:= (Pane.coverBill ..).2.trans (Pane.brace x hw)
  obtain ⟨hδ',hp⟩:= hΡ B he' hu ho (congr_arg RG.Stage.supportExponent hj : (B).supportExponent=K'.supportExponent) rfl U.beta Φ (T|>.clock.loopCap m)
    hx (Boulevard.coupling A _ _ hm) (Pane.coverBill ..).1 hG
  have hwidth: preExponent B/ (B).B ≤ (k).width/4:= by rw [hj]; exact hp
  have htV:Real.exp (-((k).width/4)*(B).B)*Song.octaveNeed G B (k).clip (k).width (k).paths (T|>.clock.loopCap m) U.beta Φ ≤ Fate.target r G L x:=by rw [hj]; exact hδ'
  obtain ⟨he,Hm⟩:= Pruned.account H B Ξ D' E r Φ rfl rfl u' hh (protocol A.B hm R.pledging.conducts.full) ho.le hu.le hf hU (CensusStep.decent R hm) hwidth hΒ htV
    (hL.trans (show R.t Jp Ip ≤ _+2 from le_add_of_nonneg_right (by norm_num))) (Inherit.loosens E τ _ hδ hτ) hs
  refine ⟨VacuumListing.relax B he ?_ (le_refl _),Hm⟩
  let t:= Fate.target r G L x
  have he := hE.1
  have hd:turnFee B=Height.away K':=by unfold turnFee Height.away; rw [ho,hu]
  have hg' : 0 ≤ τ := by unfold Inherit.Debits at hδ; obtain ⟨v,h,p⟩:= hδ; exact Cost.nonneg (p (0:Site _))
  rw [spill, PriceCompiler.beta_eq A.B.valid,hd]
  calc
    _ = (Height.away K'*(v/(L).val)+Height.away K'*d)*τ + Height.away K'*(t+t+t):= by dsimp only [t,v]; ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right (show Height.away K'*(v/(L).val)+Height.away K'*d ≤ retention R m from add_le_add_right hS _) hg') he

end YM.RG01Estimate.Routed
