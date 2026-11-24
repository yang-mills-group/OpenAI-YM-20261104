import YM.Integration.WilsonPositionProgramBlockedTrialVoice
import YM.MergeProof.Marco

/-! True finite aligned-column return between two interior dates, with the
complete old Wilson law held fixed throughout the interval. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Integration.WilsonPositionProgramBlockedTrialCone
open Function Filter Lattice RG Wilson Extra.Histories Source Labels
open Extra.Histories.Relay Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato RG05Readout RG05Readout.Address
open WilsonOriginalNullCorridor MergeProof
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) (d:ℕ)
local notation "C₀" => R.family
local notation "F₀" => (C₀).labels.level d
local notation "B₀" => (C₀).localSection d
local notation "H₀" => (C₀).path
local notation "P₀" => (C₀).params

def cost (b:ℕ):ℕ → ℝ
  | 0=>1
  | n+1=>((H₀).levels.params (b+n+1)).columns * cost b n

theorem cost_nonneg (b n:ℕ):0≤cost R b n:=by
  induction n with
  | zero=>exact zero_le_one
  | succ n ih=>exact mul_nonneg (zero_le_one.trans ((H₀).levels.params _).columns_ge) ih

theorem carry (simple:G.Simple) {N p b:ℕ} (bought:R.t d≤b) (n:ℕ) (live:b+n≤N)
    (V:Voice F₀ H₀ p (b+n)) (hv:Heard B₀ H₀ N p P₀ (b+n) V) (chor:Chorus H₀ N p (b+n) V):
    ∃ Z:Voice F₀ H₀ p b, Heard B₀ H₀ N p P₀ b Z ∧ Chorus H₀ N p b Z ∧
      (∀v,flow C₀ d N p b n ((V.plays v).density 0 B₀ ((H₀).rep N p (b+n)))=
        (Z.plays v).density 0 B₀ ((H₀).rep N p b)) ∧
      ∀ v,(F₀).coeffSize (V.index v)≤cost R b n*(F₀).coeffSize (Z.index v):=by
  induction n with
  | zero=>exact ⟨V,hv,chor,fun _=>rfl,fun _=>by simp only [cost,one_mul,le_refl]⟩
  | succ n ih=>
    have age:b+n<N:=by omega
    obtain ⟨door,_,fund⟩:=Bandage.chorus simple R.b R.T R.tuning.receipts N p (b+n) age
    obtain ⟨⟨tags,finite,keeper,owns,T,a,c,stamp,buy⟩,honest,toll,hard⟩:=
      fund d ((R.accepts d).trans (R.alloy.B.a.fits.mono (by omega)))
    obtain ⟨U,hu,reports,uc,_⟩:=repriseQ B₀ H₀ N p P₀ R.w (b+n) V R.makes.wilson age hv
      R.b.clock.room R.b.clock.bank T door honest tags toll stamp finite hard buy keeper owns chor
      (R.makes.sections d) (fun X=>(Tour.bright H₀ R.makes.wilson N p _ age X).ne')
    obtain ⟨Z,hz,zc,lower,back⟩:=ih age.le U hu uc
    refine ⟨Z,hz,zc,?_,?_⟩
    · intro v;rw [flow]
      change flow C₀ d N p b n (blast H₀ N p (b+n) d _) = _
      exact (congrArg (flow C₀ d N p b n) (reports.values v).symm).trans (lower v)
    · intro v
      have h:=Work.G08.cone_step R.w H₀ R.b.clock.room R.b.clock.bank (b+n) F₀
        ((U.plays v).x) ((V.plays v).x) (U.charge v) (V.charge v) (reports.tally v)
        (hv.currents v ▸ hv.cone v)
      have step:(F₀).coeffSize (V.index v)≤((H₀).levels.params (b+n+1)).columns*(F₀).coeffSize (U.index v):=by
        simpa only [hv.currents,hu.currents] using h.2.1
      exact (step.trans (mul_le_mul_of_nonneg_left (back v)
        (zero_le_one.trans ((H₀).levels.params _).columns_ge))).trans_eq (mul_assoc ..).symm

theorem original (simple:G.Simple) {N p b n:ℕ} (bought:R.t d≤b) (live:b+n≤N):
    let I:=WilsonPositionProgramBlockedTrialVoice.denomination F₀ H₀ N (b+n)
    ∃ Z:Voice F₀ H₀ p b, Heard B₀ H₀ N p P₀ b Z ∧ Chorus H₀ N p b Z ∧
      ∀v, let x:=I.symm v
        (Z.plays x).density 0 B₀ ((H₀).rep N p b)=WilsonPositionProgramOriginalBlockedTrial.carried R d live 0 v ∧
        (F₀).coeffSize v≤cost R b n*(F₀).coeffSize (Z.index x):=by
  let V:=WilsonPositionProgramBlockedTrialVoice.trial F₀ H₀ N p (b+n)
  have full:Chorus H₀ N p (b+n) V:=by
    constructor;intro x s;funext X U
    simp [V,WilsonPositionProgramBlockedTrialVoice.trial,primary,floatUp,stepUp,profile,cram,Motion.scalar]
  obtain ⟨Z,heard,cho,fields,pay⟩:=carry R d simple bought n live V
    (WilsonPositionProgramBlockedTrialVoice.enrolled R.makes.wilson (R.makes.sections d) live) full
  intro I;refine ⟨Z,heard,cho,?_⟩;intro v
  have field:=fields (I.symm v)
  have same:V.plays (I.symm v)=primary 0 v:=WilsonPositionProgramBlockedTrialVoice.submitted N p (b+n) v
  rw [same] at field
  refine ⟨field.symm,?_⟩
  have q:=pay (I.symm v)
  change (F₀).coeffSize (I (I.symm v))≤_ at q
  simpa only [LinearEquiv.apply_symm_apply] using q
end YM.Integration.WilsonPositionProgramBlockedTrialCone
end
