import YM.Integration.WilsonSeparatedMovingProfileOPE

/-! The actual unoccupied outer arm on the same pair of real clocks. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedMovingNullOPE
open Filter Set Spec OPE OPE.Orbits PhysMS Trace.Pilot Pert RG17 Extraction Table Climb
open WilsonMovingFarShell OPE.Nesting
open scoped BigOperators Classical Topology
variable {G:Gauge} {C:Family G} {f:Extraction.Order} {V:Table C.book}
variable {I:Type} [Fintype I] {d:I→ℕ}

abbrev blank (V:Table C.book) (i:Empty) : V.Tag := Short.extra (z:=i)

private lemma window (F:Final C f V) (Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J:ℝ→tower V) (lead:Leading F J) (fac:Facilities C f V)
    (v:(i:I)→Free C (d i)) {a M η ζ:ℝ} (ap:0<a) (top:a<1) (mp:0≤M) (ep:0<η) (zeta:ζ<1) :
    ∀ᶠ L:ℝ in atTop,∀ x:I→E4,WithinRoom (length 1 L) M η x 0→
      ‖formula F Q x 0 (Frame.born J (length 1 L) v) Short.gapPos (voices (blank V)) 0 none‖≤
        (length 1 L/length a L)^ζ := by
  apply refine_geometry
  intro X ℓ nonempty earlier cases
  haveI:=nonempty
  have time:Tendsto id ℓ atTop := tendsto_id.mono_left earlier
  have physical:Tendsto (fun L:ℝ=>length 1 L) ℓ trail :=
    tendsto_nhdsWithin_iff.mpr ⟨Real.tendsto_exp_atBot.comp
      (Tendsto.const_mul_atTop_of_neg (by norm_num : -(1:ℝ)<0) time),Eventually.of_forall (fun _=>Real.exp_pos _)⟩
  have near:=room_regime physical mp ep cases
  simp only [run,WilsonMovingFarShell.length,Real.log_exp,neg_one_mul,neg_neg] at near
  let e:Empty→ℕ:=OPE.Nesting.degrees (blank V)
  let w:(i:Empty)→Free C (e i) := fun i=>i.elim
  have clear:Intervals ℓ id a (fun _=>sole (0:E4)) (fun _=>Short.gapPos) := by
    intro c hc;exact Eventually.of_forall fun _ _ i=>i.elim
  have separate:Kept ℓ id a (fun _=>Short.gapPos) := by
    intro c hc;exact Eventually.of_forall fun _ i=>i.elim
  have report:=WilsonMovingFarShell.separated F Q J lead fac.toServices time ap top near.1 near.2 clear separate
    (fun _=>none) 0 v w zeta
  refine ⟨ℓ,nonempty,le_rfl,report.mono fun L h=>?_⟩
  have tags:Frame.born J (length a L) w=voices (blank V) := by funext i;cases i
  simp only [id_eq,tags,Nat.cast_zero,zero_add] at h
  exact h

theorem original (F:Final C f V) (Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J:ℝ→tower V) (lead:Leading F J) (fac:Facilities C f V)
    (v:(i:I)→Free C (d i)) {a M η ζ:ℝ} (ap:0<a) (top:a<1) (mp:0≤M) (ep:0<η) (zeta:ζ<1) :
    ∀ᶠ r in trail,∀ x:I→E4,WithinRoom r M η x 0→
      ‖formula F Q x 0 (Frame.born J r v) Short.gapPos (voices (blank V)) 0 none‖≤(r/r^a)^ζ := by
  have sold:=window F Q J lead fac v ap top mp ep zeta
  have time:Tendsto run trail atTop := run_towards (tendsto_id : Tendsto id trail trail)
  filter_upwards [time.eventually sold,length_rate.pos] with r paid rp x hx
  change 0<r at rp
  have clock (d:ℝ):length d (run r)=r^d := by rw [WilsonMovingFarShell.length,run,Real.rpow_def_of_pos rp];congr 1;ring
  have nr:length 1 (run r)=r := (clock 1).trans (Real.rpow_one _)
  have copy:WithinRoom (length 1 (run r)) M η x 0 := by rw [nr];exact hx
  simpa only [nr,clock a] using paid x copy

end YM.Integration.WilsonSeparatedMovingNullOPE
