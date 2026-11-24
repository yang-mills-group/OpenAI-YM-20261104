import YM.Integration.WilsonMacroscopicUniformRemainder
import YM.Integration.WilsonMacroscopicVacuumFactor

/-! The empty exterior on the original funded reader. The three strictly
positive strata below four are empty on the genuine physical quotient. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
noncomputable section
namespace YM.Integration.WilsonNestedReportedCharacterCurrentBayQ198Physical
open Function Filter Finset Set MeasureTheory Extraction Table Spec
open Next.Rank Next.UVStress OPE OPE.Orbits OPE.Nesting RG12 RG17 SharpGram Climb PhysMS
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open scoped Topology Classical BigOperators
universe u
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
    (F:Spec.Final R.family f S)(Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
variable {I:Type}[Fintype I]{d:I→ℕ}

abbrev ghosts (S:Table R.family.book):Empty→S.Tag:=fun z=>nomatch z

def coefficient (x:I→E4)(v:Labels S d)(o:E4):ℂ:=
  upon S 0 o OPE.Short.gapPos (voices (ghosts S)) (Q.fresh 0 x o v)

theorem line (simple:G.Simple)(x:I→E4)(v:Labels S d)(o:E4):
    coefficient F Q x v o • S.unit 0=Q.fresh 0 x o v:=by
  obtain ⟨z,hz⟩:=RG12.Kintsugi.Spot.unit_desc (C:=R.family) (S:=S) simple (by decide : (0:ℕ)<4) (Q.fresh 0 x o v)
  unfold coefficient
  rw [hz,map_smul,show upon S 0 o OPE.Short.gapPos (voices (ghosts S)) (S.unit 0)=1 from
    OPE.Short.vacuum F none o 0 (ghosts S)]
  simp

theorem vacant (simple:G.Simple){j:ℕ}(jp:0<j)(low:j<4):IsEmpty (Q.channels j):=by
  constructor
  intro i
  apply (Q.basis j).ne_zero i
  apply Subtype.ext
  let x:S.Field j:=Q.basis j i
  have hx:x∈Q.stratum j:=(Q.basis j i).property
  obtain ⟨c,hc⟩:=RG12.Kintsugi.Spot.unit_desc (C:=R.family) (S:=S) simple low x
  change x=0
  rw [hc] at hx ⊢
  have hi:=F.sector.derivatives.fixs Q.lifts Q.continuum.laws (Nat.zero_le j)
  rw [← Q.test_fixes j (c • S.unit j) hx,←hi,map_smul,Q.cut_rise j 0 j (Nat.zero_le j),Q.kills_lower j 0 jp,smul_zero]

theorem horizon (simple:G.Simple)(x:I→E4)(v:Labels S d)(o:E4)(viewer:Viewers F):
    formula F Q x o v OPE.Short.gapPos (voices (ghosts S)) 0 viewer=
      formula F Q x o v OPE.Short.gapPos (voices (ghosts S)) 3 viewer:=by
  let T:=spectator F viewer
  let g(j:ℕ):=∑i:Q.channels j,Q.coef j i x v o*
    whole (S:=S) T (sole o) (sole (Q.actor j i):Labels S (fun _:Unit=>j)) OPE.Short.gapPos (voices (ghosts S))
  have spine (j:ℕ)(hj:j≤3):trunc T F Q j x o v OPE.Short.gapPos (voices (ghosts S))=g 0:=by
    apply Eq.trans (@Finset.sum_eq_single _ _ _ Finset.univ (fun i:Fin (j+1)=>g i) (⟨0,Nat.succ_pos _⟩) _ (by simp)) rfl
    intro k _ different
    have nonzero:k.val≠0:=fun no=>different (Fin.ext no)
    haveI:=vacant F Q simple (Nat.pos_of_ne_zero nonzero) (Nat.lt_succ_of_le ((Nat.le_of_lt_succ k.isLt).trans hj))
    exact Finset.sum_eq_zero fun i _=>(IsEmpty.false (α:=Q.channels k.val) i).elim
  exact congrArg (_-·) ((spine 0 (by decide)).trans (spine 3 le_rfl).symm)

theorem identity (simple:G.Simple)(x:I→E4)(v:Labels S d)(o:E4)(viewer:Viewers F)(distinct:Injective x):
    Orbits.moment (spectator F viewer) x v-coefficient F Q x v o=
      formula F Q x o v OPE.Short.gapPos (voices (ghosts S)) 3 viewer:=by
  rw [←horizon F Q simple,WilsonMacroscopicVacuumFactor.grade_zero,←line F Q simple x v o,map_smul,
    OPE.Short.vacuum F viewer o _ (ghosts S)]
  have wholeEq:=OPE.Short.tagged F (fun i:I=>(⟨d i,v i⟩:S.Tag)) x viewer distinct
  rw [show whole (spectator F viewer) x v OPE.Short.gapPos (voices (ghosts S))=Orbits.moment (spectator F viewer) x v from wholeEq]
  simp

theorem original {T:Campaign R}(simple:G.Simple)(W:Campaign.Pillars R T){b:ℝ}
    (source:FundedOriginalProperties.{u} simple b W)(pace:WilsonWindowReportingPace.Slow R.kit){B:ℕ}(bp:0<B)
    (fac:OPE.Facilities R.family f S)(J:ℝ→tower S)(lead:Leading F J){A:(Bel R.family.book).Hierarchy}
    (paid:∀d:ℕ,∀ᶠr in Trace.Pilot.trail,Frame.obedient F A (J r) d){n:ℕ}(d:Caps n){K:Set (Points n)}
    (compact:IsCompact K)(safe:K⊆conf n){θ:ℝ→ℝ}(heat:Trace.Pilot.Coupling G θ)(q:ℕ)
    {σ ε:ℝ}(sp:0<σ)(ep:0 < ε):
    ∀ᶠr in RG17.home,∀x∈K,∀viewer:Viewers F,∀v:(i:Fin n)→Free R.family (d i),
      let labels:=fun i=>J r (d i) (v i)
      ‖Orbits.moment (spectator F viewer) (RG17.posed r x) labels-
        coefficient F Q (RG17.posed r x) labels 0‖≤ ε*(θ r)^q*r^(4-σ)*(∏i,‖v i‖):=by
  have earned:=WilsonMacroscopicUniformRemainder.original simple W source pace bp F fac Q J lead paid d
    (voices (ghosts S)) compact safe (by norm_num : (0:ℝ)<1) heat 3 q sp ep
  filter_upwards [earned,RG17.positiveLength] with r charged rp x hx viewer v
  dsimp only
  have distinct:Injective (RG17.posed r x):=by
    intro a b eq
    apply (safe hx : Injective x.ofLp)
    have cancel:=congrArg (fun z:E4=>r⁻¹ • z) (show r • x a=r • x b from eq)
    simpa only [smul_smul,inv_mul_cancel₀ rp.ne',one_smul] using cancel
  rw [identity F Q simple (RG17.posed r x) (fun i=>J r (d i) (v i)) 0 viewer distinct]
  have result:=charged x hx OPE.Short.gapPos (by constructor <;> intro z <;> cases z) viewer v
  norm_num at result
  exact result

end YM.Integration.WilsonNestedReportedCharacterCurrentBayQ198Physical
end
