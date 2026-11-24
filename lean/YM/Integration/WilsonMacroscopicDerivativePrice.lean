import YM.Integration.WilsonMacroscopicRelativeGradient
import YM.Integration.WilsonMacroscopicDescendant
import YM.Integration.WilsonMacroscopicExteriorEnvelope

/-! An inner displacement with the external positions fixed: pay the
actual physical differentiated label on the measured higher-grade frame
and its complete signed correlation on the same macroscopic exterior. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMacroscopicDerivativePrice
open Function Filter Finset Set MeasureTheory Extraction Table Spec
open Next.Rank OPE OPE.Orbits OPE.Nesting RG12 RG17 SharpGram Climb PhysMS
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open scoped Topology Classical BigOperators
universe u u₁
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {V : Table R.family.book} {n : ℕ} {d : Caps n} {E : Type} [Fintype E] {e : E→ℕ}

private def higher (d : Caps n) (i : Fin n) := update d i (d i+1)
private def replacement {T : ℕ→Type u₁} (v : (j:Fin n)→T (d j)) (i : Fin n) (w : T (d i+1)) (j : Fin n) : T (higher d i j) := by
  by_cases h:j=i
  · subst j;simpa only [higher,update_self] using w
  · simpa only [higher,update_of_ne h] using v j

private theorem tags_replaced {T : ℕ→Type u₁} (v : (j:Fin n)→T (d j)) (i : Fin n) (w : T (d i+1)) :
    (fun j=> (⟨higher d i j,replacement v i w j⟩ : Sigma T))=
      update (fun j=> (⟨d j,v j⟩ : Sigma T)) i ⟨d i+1,w⟩ := by
  funext j;by_cases h:j=i
  · subst j;simp [higher,replacement]
  · simp [higher,replacement,h]

private theorem price {T : ℕ→Type u₁} [∀j,NormedAddCommGroup (T j)]
    (v : (j:Fin n)→T (d j)) (i : Fin n) {w : T (d i+1)} {c : ℝ} (hw : ‖w‖≤c*‖v i‖) :
    (∏ j,‖replacement v i w j‖) ≤ c * ∏ j,‖v j‖ := by
  have eq : (fun j=>‖replacement v i w j‖)=update (fun j=>‖v j‖) i ‖w‖ := by
    funext j
    have tagged := congrFun (tags_replaced v i w) j
    by_cases h:j=i
    · subst j;rw [update_self] at tagged ⊢
      exact congrArg (fun s : Sigma T=>‖s.2‖) tagged
    · rw [update_of_ne h] at tagged ⊢
      exact congrArg (fun s : Sigma T=>‖s.2‖) tagged
  have was := Finset.prod_update_of_mem (Finset.mem_univ i) (fun j=>‖v j‖) (‖v i‖)
  rw [Function.update_eq_self] at was
  change (∏ j,(fun k=>‖replacement v i w k‖) j)≤_
  rw [eq,Finset.prod_update_of_mem (Finset.mem_univ i),was,←mul_assoc]
  exact mul_le_mul_of_nonneg_right hw (prod_nonneg fun j _=>norm_nonneg _)

private theorem funded (F : Spec.Final R.family f V) (J : ℝ→PhysMS.tower V) (r : ℝ)
    (v : (j:Fin n)→Free R.family (d j)) (i : Fin n) (a : Axis) (x : Fin n→E4) (y : E→E4) (w : Labels V e) (t : Viewers F) :
    let ins (j : Fin n) := J r (d j) (v j)
    let D := F.sector.derivatives.deriv (d i) a (ins i)
    let z := (J r (d i+1)).symm ((r:ℂ) • D)
    r • whole (spectator F t) x (voices (update (fun j=> (⟨d j,ins j⟩ : V.Tag)) i ⟨d i+1,D⟩)) y w =
      whole (spectator F t) x (fun j=>J r (higher d i j) (replacement v i z j)) y w := by
  intro ins D z
  rw [←tags_replaced ins i D]
  let p := higher d i
  let old := replacement ins i D
  let new (j : Fin n) := J r (p j) (replacement v i z j)
  let ℳ := sectionLabels (d:=Sum.elim p e) w (Orbits.moment (spectator F t) (beside x y))
  have hm (b : Labels V p) : whole (spectator F t) x b y w=ℳ b := (sectionLabels_apply w _ b).symm
  change r • whole (spectator F t) x old y w=whole (spectator F t) x new y w
  rw [hm,hm,RCLike.real_smul_eq_coe_smul (K:=ℂ)]
  have same : update old i ((r:ℂ) • old i)=new := by
    funext j
    have original := congrFun (tags_replaced ins i D) j
    have normalized := congrArg (fun s : Sigma (Free R.family)=> (⟨s.1,J r s.1 s.2⟩ : V.Tag)) (congrFun (tags_replaced v i z) j)
    by_cases h:j=i
    · subst j
      rw [update_self] at original normalized ⊢
      have left := congrArg (fun s : V.Tag=> (⟨s.1,(r:ℂ) • s.2⟩ : V.Tag)) original
      change (⟨p i,(r:ℂ) • old i⟩ : V.Tag)=⟨d i+1,(r:ℂ) • D⟩ at left
      change (⟨p i,new i⟩ : V.Tag)=⟨d i+1,J r (d i+1) z⟩ at normalized
      have cancel : J r (d i+1) z=(r:ℂ) • D := (J r (d i+1)).apply_symm_apply _
      rw [cancel] at normalized
      exact eq_of_heq (Sigma.mk.inj (left.trans normalized.symm)).2
    · rw [update_of_ne h] at original normalized ⊢
      change (⟨p j,old j⟩ : V.Tag)=⟨d j,ins j⟩ at original
      change (⟨p j,new j⟩ : V.Tag)=⟨d j,ins j⟩ at normalized
      exact eq_of_heq (Sigma.mk.inj (original.trans normalized.symm)).2
  have amount := ℳ.map_update_smul old i (r:ℂ) (old i)
  rw [update_eq_self] at amount
  rw [←same];exact amount.symm

theorem axis {T : Campaign R} (hG : G.Simple) (W : Campaign.Pillars R T) {b : ℝ}
    (source : FundedOriginalProperties.{u} hG b W) (pace : WilsonWindowReportingPace.Slow R.kit) {B : ℕ} (hB : 0<B)
    (F : Spec.Final R.family f V) (fac : OPE.Facilities R.family f V)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower V) (leading : PhysMS.Leading F J) {A : (Bel R.family.book).Hierarchy}
    (paid : ∀ d : ℕ,∀ᶠ r in Trace.Pilot.trail,PhysMS.Frame.obedient F A (J r) d)
    (d : Caps n) (i : Fin n) (a : Axis) (w : Labels V e) {K : Set (Points n)} (hk : IsCompact K) (sep : K⊆conf n)
    {δ : ℝ} (hδ : 0<δ) {g : ℝ→ℝ} (hg : Trace.Pilot.Coupling G g) :
    ∃ M : ℝ,0≤M ∧ ∀ᶠ r in Trace.Pilot.trail,∀ x∈K,∀ y : E→E4,ClearOf 0 y δ →
      Injective (beside (RG17.posed r x) y) → ∀ t : Viewers F,∀ v : (j:Fin n)→Free R.family (d j),
      let ext := upon (spectator F t) 0 0 y w (V.unit 0)
      ‖Points.gradient i a (fun z : Points n=> whole (spectator F t) (RG17.posed r z) (fun j=>J r (d j) (v j)) y w) x‖ ≤
        M*(1+‖ext‖)*(∏ j,‖v j‖) := by
  have original := WilsonReportPrescribedFrame.present F J leading paid
  obtain ⟨c,hc,cost⟩:= WilsonMacroscopicDescendant.paid F J original (d i) a
  obtain ⟨M,hM,amp⟩:= WilsonMacroscopicExteriorEnvelope.amplitude hG W source pace hB F fac Q J leading paid (higher d i) w hk sep hδ hg
  refine ⟨M*c,mul_nonneg hM hc,?_⟩
  filter_upwards [cost,amp] with r invoice full x hx y clear safe t v
  let ins (j : Fin n) := J r (d j) (v j)
  let D := F.sector.derivatives.deriv (d i) a (ins i)
  let z := (J r (d i+1)).symm ((r:ℂ) • D)
  let ext := upon (spectator F t) 0 0 y w (V.unit 0)
  have identity := WilsonMacroscopicRelativeGradient.at_slot F t (fun j=> (⟨d j,ins j⟩ : V.Tag)) (fun j=> (⟨e j,w j⟩ : V.Tag)) r y safe i a
  have column := funded F J r v i a (RG17.posed r x) y w t
  change Points.gradient i a (fun s : Points n=>whole (spectator F t) (RG17.posed r s) ins y w) x =
    r • whole (spectator F t) (RG17.posed r x) (voices (update (fun j=> (⟨d j,ins j⟩ : V.Tag)) i ⟨d i+1,D⟩)) y w at identity
  change ‖Points.gradient i a (fun s : Points n=>whole (spectator F t) (RG17.posed r s) ins y w) x‖≤(M*c)*(1+‖ext‖)*(∏ j,‖v j‖)
  rw [identity,column]
  have bounded := full x hx y clear t (replacement v i z)
  exact bounded.trans ((mul_le_mul_of_nonneg_left (price v i (invoice (v i))) (mul_nonneg hM (by positivity))).trans_eq (by ring))

end YM.Integration.WilsonMacroscopicDerivativePrice
