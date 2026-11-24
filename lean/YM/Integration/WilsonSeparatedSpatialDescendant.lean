import YM.Integration.WilsonMacroscopicDerivativePrice

/-! Original Ward identities for the true, normalized near descendants,
in a form that can be iterated on the moving continuum region. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedSpatialDescendant
open Function Filter Finset Set MeasureTheory Extraction Table Spec
open Next.Rank OPE OPE.Orbits OPE.Nesting RG12 RG17 SharpGram Climb PhysMS
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open scoped Topology Classical BigOperators
universe u u₁
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {V : Table R.family.book} {n : ℕ} {d : Caps n} {E : Type} [Fintype E] {e : E→ℕ}

def higher (d : Caps n) (i : Fin n) := update d i (d i+1)
def replacement {T : ℕ→Type u₁} (v : (j:Fin n)→T (d j)) (i : Fin n) (w : T (d i+1)) (j : Fin n) : T (higher d i j) := by
  by_cases h:j=i
  · subst j;simpa only [higher,update_self] using w
  · simpa only [higher,update_of_ne h] using v j

private theorem tags_replaced {T : ℕ→Type u₁} (v : (j:Fin n)→T (d j)) (i : Fin n) (w : T (d i+1)) :
    (fun j=> (⟨higher d i j,replacement v i w j⟩ : Sigma T))=
      update (fun j=> (⟨d j,v j⟩ : Sigma T)) i ⟨d i+1,w⟩ := by
  funext j;by_cases h:j=i
  · subst j;simp [higher,replacement]
  · simp [higher,replacement,h]

theorem price {T : ℕ→Type u₁} [∀j,NormedAddCommGroup (T j)]
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

def lifted (F:Final R.family f V) (J:ℝ→tower V) (r:ℝ) (i:Fin n) (a:Axis) (v:(j:Fin n)→Free R.family (d j)) :
    (j:Fin n)→Free R.family (higher d i j) :=
  replacement v i ((J r (d i+1)).symm ((r:ℂ) • F.sector.derivatives.deriv (d i) a (J r (d i) (v i))))

def experiment (J:ℝ→tower V) (r:ℝ) (v:(i:Fin n)→Free R.family (d i)) (y:E→E4) (w:Labels V e)
    (X:Points n) : ℂ := whole V (RG17.posed r X) (fun i=>J r (d i) (v i)) y w

theorem at_slot (F:Final R.family f V) (J:ℝ→tower V) (r:ℝ) (i:Fin n) (a:Axis) (v:(j:Fin n)→Free R.family (d j))
    (y:E→E4) (w:Labels V e) (X:Points n) (safe:Injective (beside (RG17.posed r X) y)) :
    Points.gradient i a (experiment J r v y w) X = experiment J r (lifted F J r i a v) y w X := by
  let ins (j:Fin n):=J r (d j) (v j)
  have identity:=WilsonMacroscopicRelativeGradient.at_slot F none (fun j=> (⟨d j,ins j⟩ : V.Tag))
    (fun j=>(⟨e j,w j⟩:V.Tag)) r y safe i a
  have column:=funded F J r v i a (RG17.posed r X) y w none
  exact identity.trans column

theorem charge (F:Final R.family f V) (J:ℝ→tower V) (P:Pier.Lair.Present F J) (d:Caps n) (i:Fin n) (a:Axis) :
    ∃ C:ℝ,0≤C ∧ ∀ᶠ r in Trace.Pilot.trail,∀ v:(j:Fin n)→Free R.family (d j),
      (∏ j,‖lifted F J r i a v j‖)≤C*(∏ j,‖v j‖) := by
  obtain ⟨c,hc,paid⟩:=WilsonMacroscopicDescendant.paid F J P (d i) a
  exact ⟨c,hc,paid.mono fun _ receipt v=>price v i (receipt (v i))⟩

end YM.Integration.WilsonSeparatedSpatialDescendant
