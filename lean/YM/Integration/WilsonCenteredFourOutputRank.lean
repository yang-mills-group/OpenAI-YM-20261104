import YM.Integration.WilsonCenteredFourOutputSensor
import YM.UVNext.FREE_STRESS_CERTIFICATE.Size

/-! The grade-four selector is non-vacuous on the actual physical table.
The cumulative Maxwell space has 22 entries. Removing the measured unit
leaves exactly 21 independent reader coordinates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredFourOutputRank
open Function Set Spec Extraction Table OPE OPE.Orbits RG17 PhysMS WilsonCenteredFourOutputSensor
open scoped Classical BigOperators Topology
variable {G:Gauge} {C:Family G} {f:Extraction.Order} {S:Table C.book}
    (F:Final C f S) (Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J:ℝ→PhysMS.tower S) (simple:G.Simple)

include J simple in
private theorem small {d:ℕ} (pos:0<d) (low:d<4) (v:S.Field d) (inQ:v∈Q.stratum d):
    v=0:=by
  have rank:Module.finrank ℂ (S.Field d)=1:=
    (J 1 d).symm.finrank_eq.trans (UVNext.FreeStress.dim_before C.book.grid simple low)
  obtain ⟨c,rfl⟩:∃c:ℂ,c • S.unit d=v:=
    (finrank_eq_one_iff_of_nonzero' (S.unit d) (S.alive d F.room.kernel.laws)).1 rank v
  have unit:=F.sector.derivatives.fixs Q.lifts Q.continuum.laws (Nat.zero_le d)
  rw [←Q.test_fixes d (c • S.unit _) inQ,←unit,map_smul,Q.cut_rise d 0 d (Nat.zero_le d),
    Q.kills_lower d 0 pos,smul_zero]

include J simple in
theorem card : Fintype.card (Q.channels 4)=21:=by
  let w:=Q.cutTest 0 4
  have all:Surjective w:=by
    intro z
    use F.sector.derivatives.rise (d:=0) (show 0≤4 by decide) z
    have st:z∈Q.stratum 0:=Q.piece_mem.mpr (fun i=>i.elim0)
    exact (Q.cut_rise 0 0 4 (by decide) z).trans (Q.test_fixes 0 z st)
  have ker:Q.stratum 4=w.ker:=by
    ext z
    constructor
    · intro good
      exact (Q.piece_mem.mp good) (0:Fin 4)
    · intro hz
      apply Q.piece_mem.mpr
      intro i
      by_cases h:i.val=0
      · rw [h]
        exact hz
      · exact small F Q J simple (Nat.pos_of_ne_zero h) i.isLt _ (Q.knife_mem i.val (Q.liftOne i.val 4 z))
  have dim0:Module.finrank ℂ (S.Field 0)=1:=
    (J 1 0).symm.finrank_eq.trans (UVNext.FreeStress.dim_before C.book.grid simple (by decide))
  have dim4:Module.finrank ℂ (S.Field 4)=22:=
    (J 1 4).symm.finrank_eq.trans (UVNext.FreeStress.four_size C.book.grid simple)
  have count:=w.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr all,finrank_top,dim0,dim4] at count
  rw [←Module.finrank_eq_card_basis (Q.basis 4),ker]
  omega

def channel : Q.channels 4:=
  Classical.choice (Fintype.card_pos_iff.mp (by rw [card F Q J simple];decide))

theorem unit_response (c:Q.channels 4) : grade F Q c (Q.actor 4 c)=1:=by
  let b:=Q.basis 4 c
  have fix:Q.cutTest 4 4 b.val=b.val:=Q.test_fixes 4 b.val b.property
  have same:(⟨Q.cutTest 4 4 b.val,Q.knife_mem 4 _⟩:Q.stratum 4)=b:=Subtype.ext fix
  change (Q.basis 4).repr (⟨Q.cutTest 4 4 b.val,Q.knife_mem 4 _⟩:Q.stratum 4) c=1
  rw [same]
  simp [b]

theorem lower (c:Q.channels 4) {d:ℕ} (h:d<4) (v:S.Field d):
    grade F Q c (F.sector.derivatives.rise h.le v)=0:=by
  have cancel:Q.cutTest 4 4 (F.sector.derivatives.rise h.le v)=0:=
    (Q.cut_rise 4 d 4 h.le v).trans (Q.kills_lower 4 d h v)
  have same:(⟨Q.cutTest 4 4 (F.sector.derivatives.rise h.le v),Q.knife_mem 4 _⟩:Q.stratum 4)=0:=Subtype.ext cancel
  change (Q.basis 4).repr (⟨Q.cutTest 4 4 (F.sector.derivatives.rise h.le v),Q.knife_mem 4 _⟩:Q.stratum 4) c=0
  rw [same,map_zero]
  rfl

end YM.Integration.WilsonCenteredFourOutputRank
