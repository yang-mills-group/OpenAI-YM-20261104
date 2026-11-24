import YM.Integration.WilsonSeparatedSpatialDescendant
import YM.Integration.WilsonSeparatedContinuumAmplitude

/-! Every fixed finite list of normalized near-site derivatives of the true
moving joint signal is uniformly bounded on the actual separated continuum
region before the near vectors and the entire far profile. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedContinuumGradients
open Filter Function Set Spec OPE OPE.Orbits PhysMS Trace.Pilot Pert Pert.Position RG17 Extraction Table Climb
open MS MS.Land MS.Menus MS.Local.Physical OPE.Nesting OPE.Levy Next.UVStress
open Frontier6.Road PhysicalNext.Repeat.Legato WilsonLimitConstruction
open WilsonSeparatedMovingRichGeometry WilsonSeparatedMovingRichVacuum WilsonSeparatedSpatialDescendant
open scoped Classical BigOperators Topology
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {V:Table R.family.book} {n:ℕ}

abbrev Word (n:ℕ) := List (Fin n×Axis)

def grades : Word n→Caps n→Caps n
  | [],d=>d
  | (i,_)::rest,d=>grades rest (higher d i)

def labels (F:Final R.family f V) (J:ℝ→tower V) (r:ℝ) :
    (w:Word n)→(d:Caps n)→((i:Fin n)→Free R.family (d i))→((i:Fin n)→Free R.family (grades w d i))
  | [],_,v=>v
  | (i,a)::rest,d,v=>labels F J r rest (higher d i) (lifted F J r i a v)

/-- Apply the actual Euclidean near-site directions in the stated order. -/
def derivatives : Word n→(Points n→ℂ)→(Points n→ℂ)
  | [],f=>f
  | (i,a)::rest,f=>derivatives rest (Points.gradient i a f)

private lemma sameGerm (w:Word n) {X:Points n} {p q:Points n→ℂ} (h:p=ᶠ[𝓝 X]q) :
    derivatives w p=ᶠ[𝓝 X]derivatives w q := by
  induction w generalizing p q with
  | nil=>exact h
  | cons v w ih=>
    apply ih
    exact (h.fderiv (𝕜:=ℝ)).mono fun _ same=>congrArg (fun z:Points n→L[ℝ]ℂ=>z (Points.direction v.1 v.2)) same

private lemma nearby (r:ℝ) (y:Fin 1→E4) {X:Points n} (live:Injective (beside (posed r X) y)) :
    ∀ᶠ z in 𝓝 X,Injective (beside (posed r z) y) := by
  have sensor (i:Fin n⊕Fin 1):ContinuousAt (fun z:Points n=>beside (posed r z) y i) X := by
    cases i with
    | inl i=>change ContinuousAt (fun z:Points n=>r • z i) X;fun_prop
    | inr i=>exact continuousAt_const
  have pair (i j:Fin n⊕Fin 1):∀ᶠ z in 𝓝 X,i≠j→beside (posed r z) y i≠beside (posed r z) y j := by
    by_cases h:i=j
    · exact Eventually.of_forall fun _ ne=>False.elim (ne h)
    have sep:beside (posed r X) y i-beside (posed r X) y j≠0 := sub_ne_zero.mpr (fun eq=>h (live eq))
    exact (((sensor i).sub (sensor j)).tendsto.eventually_ne sep).mono fun _ ne _=>sub_ne_zero.mp ne
  filter_upwards [Filter.eventually_all.mpr (fun i=>Filter.eventually_all.mpr (pair i))] with z paid i j eq
  exact by_contra fun ne=>paid i j ne eq

/-- Identity of the physical derivative with the original measured, normalized
descendant roster. Only a neighborhood of the actual separated point is used. -/
theorem marked (F:Final R.family f V) (J:ℝ→tower V) (r:ℝ) (list:Word n) (d:Caps n)
    (v:(i:Fin n)→Free R.family (d i)) (y:Fin 1→E4) {e:Fin 1→ℕ} (w:Labels V e) (X:Points n)
    (live:Injective (beside (posed r X) y)) :
    derivatives list (experiment J r v y w) X=experiment J r (labels F J r list d v) y w X := by
  induction list generalizing d with
  | nil=>rfl
  | cons first rest ih=>
    rcases first with ⟨i,a⟩
    have step:Points.gradient i a (experiment J r v y w) =ᶠ[𝓝 X] experiment J r (lifted F J r i a v) y w :=
      (nearby r y live).mono fun z safe=>WilsonSeparatedSpatialDescendant.at_slot F J r i a v y w z safe
    exact (sameGerm rest step).eq_of_nhds.trans (ih (higher d i) (lifted F J r i a v))

theorem currency (F:Final R.family f V) (J:ℝ→tower V) (P:Pier.Lair.Present F J) (list:Word n) (d:Caps n) :
    ∃ C:ℝ,0≤C ∧ ∀ᶠ r in trail,∀ v:(i:Fin n)→Free R.family (d i),
    (∏ i,‖labels F J r list d v i‖)≤C*∏ i,‖v i‖ := by
  induction list generalizing d with
  | nil=>exact ⟨1,zero_le_one,Eventually.of_forall fun _ v=>by simp only [labels,one_mul];exact le_rfl⟩
  | cons first rest ih=>
    rcases first with ⟨i,a⟩
    obtain ⟨S,np,born⟩:=WilsonSeparatedSpatialDescendant.charge F J P d i a
    obtain ⟨C,cp,staged⟩:=ih (higher d i)
    refine ⟨C*S,mul_nonneg cp np,?_⟩
    filter_upwards [born,staged] with r first paid v
    exact ((paid (lifted F J r i a v)).trans (mul_le_mul_of_nonneg_left (first v) cp)).trans_eq (mul_assoc ..).symm

theorem original (hG:G.Simple) (F:Final R.family f V) (fac:Facilities R.family f V)
    (Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (J:ℝ→tower V) (lead:Leading F J)
    {A:(Bel R.family.book).Hierarchy} (obey:∀ h:ℕ,∀ᶠ r in trail,Frame.obedient F A (J r) h)
    (B:Deck G) (D:ℕ) (φ:Test 2) (d:Caps n) (list:Word n) (K:Set (Points n)) (hk:IsCompact K) (sep:K⊆conf n)
    {a:ℝ} (ap:0<a) (top:a<1) {g:ℝ→ℝ} (hg:Coupling G g) :
    ∃ C:ℝ,0≤C ∧ ∀ᶠ r in trail,∀ X∈K,∀ u∈tsupport φ,∀ b:Glyph B D,∀ v:(i:Fin n)→Free R.family (d i),
    ‖derivatives list (experiment J r v (far (r^a) u) (fields B D b J (r^a))) X‖≤C*∏ i,‖v i‖ := by
  have trueFrame:=WilsonReportPrescribedFrame.present F J lead obey
  obtain ⟨c,cp,issued⟩:=currency F J trueFrame list d
  obtain ⟨M,mp,signal⟩:=WilsonSeparatedContinuumAmplitude.original hG F fac Q J lead obey B D φ (grades list d) K hk sep ap top hg
  refine ⟨M*c,mul_nonneg mp cp,?_⟩
  filter_upwards [issued,signal,WilsonSeparatedContinuumAmplitude.geometry φ K hk sep top] with r gate measured room X hX u hu b v
  rw [marked F J r list d v _ _ X (room X hX u hu)]
  exact ((measured X hX u hu b _).trans (mul_le_mul_of_nonneg_left (gate v) mp)).trans_eq (mul_assoc ..).symm

end YM.Integration.WilsonSeparatedContinuumGradients
