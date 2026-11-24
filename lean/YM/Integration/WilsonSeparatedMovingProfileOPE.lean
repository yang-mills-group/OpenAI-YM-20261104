import YM.Integration.WilsonTwoLengthDetector
import YM.Integration.WilsonSeparatedMovingRichGeometry
import YM.Integration.WilsonMacroscopicVacuumFactor

/-! On the whole separated support of a prescribed two-point profile, the
continuum near sites and the single normalized far site may both vary before
the rate. The result uses the signed original OPE remainder itself. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedMovingProfileOPE
open Filter Set Spec OPE OPE.Orbits PhysMS Trace.Pilot Pert RG17 Extraction Table Climb
open WilsonMovingFarShell WilsonSeparatedMovingRichGeometry
open scoped BigOperators Classical Topology
variable {G:Gauge} {C:Family G} {f:Extraction.Order} {V:Table C.book}
variable {I:Type} [Fintype I] {d:I→ℕ} {e:Fin 1→ℕ}

private lemma clearance {ℓ:Filter ℝ} (time:Tendsto id ℓ atTop) (a:ℝ) (φ:Test 2)
    (u:ℝ→Points 2) (inside:∀ᶠ L in ℓ,u L∈tsupport φ) :
    let y:=fun L:ℝ=>far (length a L) (u L)
    Intervals ℓ id a (fun _=>sole (0:E4)) y ∧ Kept ℓ id a y := by
  intro y
  obtain ⟨M,δ,_,dp,room⟩:=RG17.roomCosts (K:=tsupport φ) φ.hasCompactSupport φ.tsupport_subset
  constructor
  · intro c hc
    have rate : ∀ᶠ L in ℓ,Real.exp (-c*L)<δ*length a L :=
      ((RateIs.const time dp).mul (RateIs.exp (-a) time)).overtakes (RateLE.exp (-c) time) time (by linarith)
    filter_upwards [inside,rate] with L admissible price i j
    have diff : δ≤‖(u L) j.succ-(u L) 0‖ := by
      simpa only [RG17.posed,mul_one,one_smul] using (room 1 one_pos (u L) admissible).spaced j.succ 0 (Fin.succ_ne_zero j)
    change Real.exp (-c*L)<‖(0:E4)-(length a L) • ((u L) j.succ-(u L) 0)‖
    rw [zero_sub,norm_neg,norm_smul,Real.norm_eq_abs,abs_of_pos (show 0<length a L from Real.exp_pos _)]
    simpa only [mul_comm δ (length a L)] using price.trans_le
      ((mul_comm δ (length a L)) ▸ mul_le_mul_of_nonneg_left diff (Real.exp_nonneg _))
  · intro c hc
    exact Eventually.of_forall fun _ j k ne=>False.elim (ne (Subsingleton.elim j k))

private lemma window (F:Final C f V) (Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J:ℝ→tower V) (lead:Leading F J) (fac:Facilities C f V) (φ:Test 2)
    (v:(i:I)→Free C (d i)) (w:(j:Fin 1)→Free C (e j)) {a M η ζ:ℝ}
    (ap:0<a) (top:a<1) (mp:0≤M) (ep:0<η) (h:ℕ) (zeta:ζ<1) :
    ∀ᶠ L:ℝ in atTop,∀ site:(I→E4)×(Points 2×Viewers F),
      WithinRoom (length 1 L) M η site.1 0 ∧ site.2.1∈tsupport φ →
      ‖formula F Q site.1 0 (Frame.born J (length 1 L) v) (far (length a L) site.2.1)
        (Frame.born J (length a L) w) h site.2.2‖ ≤(length 1 L/length a L)^((h:ℝ)+ζ) := by
  apply refine_geometry
  intro S ℓ nonempty earlier cases
  haveI:=nonempty
  have time:Tendsto id ℓ atTop := tendsto_id.mono_left earlier
  have physical:Tendsto (fun L:ℝ=>length 1 L) ℓ trail :=
    tendsto_nhdsWithin_iff.mpr ⟨Real.tendsto_exp_atBot.comp
      (Tendsto.const_mul_atTop_of_neg (by norm_num : -(1:ℝ)<0) time),Eventually.of_forall (fun _=>Real.exp_pos _)⟩
  have near:=room_regime physical mp ep (cases.mono fun _ h=>h.1)
  simp only [run,WilsonMovingFarShell.length,Real.log_exp,neg_one_mul,neg_neg] at near
  have geometry:=clearance time a φ (fun L=>(S L).2.1) (cases.mono fun _ h=>h.2)
  have bill:=WilsonMovingFarShell.separated F Q J lead fac.toServices time ap top near.1 near.2 geometry.1
    geometry.2 (fun L=>(S L).2.2) h v w zeta
  exact ⟨ℓ,nonempty,le_rfl,bill⟩

private lemma clock (a:ℝ) {r:ℝ} (rp:0<r) : length a (run r)=r^a := by
  rw [WilsonMovingFarShell.length,run,Real.rpow_def_of_pos rp];congr 1;ring

/-- Uniform in every continuum near layout in a room and every far site in the
entire profile support, before any choice of its microscopic cutoffs. -/
theorem original (F:Final C f V) (Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J:ℝ→tower V) (lead:Leading F J) (fac:Facilities C f V) (φ:Test 2)
    (v:(i:I)→Free C (d i)) (w:(j:Fin 1)→Free C (e j)) {a M η ζ:ℝ}
    (ap:0<a) (top:a<1) (mp:0≤M) (ep:0<η) (h:ℕ) (zeta:ζ<1) :
    ∀ᶠ r in trail,∀ x:I→E4,WithinRoom r M η x 0→∀ u∈tsupport φ,∀ q:Viewers F,
      ‖formula F Q x 0 (Frame.born J r v) (far (r^a) u) (Frame.born J (r^a) w) h q‖≤(r/r^a)^((h:ℝ)+ζ) := by
  have sold:=window F Q J lead fac φ v w ap top mp ep h zeta
  have time:Tendsto run trail atTop := run_towards (tendsto_id : Tendsto id trail trail)
  filter_upwards [time.eventually sold,length_rate.pos] with r paid rp x hx u hu q
  change 0<r at rp
  have nr:length 1 (run r)=r := (clock 1 rp).trans (Real.rpow_one _)
  have copy:WithinRoom (length 1 (run r)) M η x 0 := by rw [nr];exact hx
  simpa only [nr,clock a rp] using paid (x,u,q) ⟨copy,hu⟩

end YM.Integration.WilsonSeparatedMovingProfileOPE
