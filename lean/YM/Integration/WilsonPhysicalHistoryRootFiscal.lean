import YM.Integration.WilsonPhysicalHistoryRootCrown
import YM.QuadraticLocal.Tint.Increases

/-! The three original fiscal tests use a common purchased gallery and its
actual majorant table. In the hard sector the assigned fine site pays for
the entire original crest. Only regular rows receive the two increases. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPhysicalHistoryRootFiscal
open Function Finset Lattice Wilson RG Pressure Ac Marker Push.Corrected Push.AbsoluteSums
open PhysicalNext PhysicalNext.Repeat Progress.DirectedRecipe RemainderComparison
open QuadraticLocal QuadraticLocal.Travel QuadraticLocal.Trigger ConnectedActivityE6 Lyric Muse Serif Spire
open Merge Lotus Typeface
open scoped Classical BigOperators
variable {I V : Type} [Countable I] [DecidableEq V] {G : Gauge} {n c L : Side}
  {x e κ w b b' z Y Γ K r : ℝ} {α : Type*} {A0 : Teller G}
  {Q : ConnectedActivityE6.Target G A0} {horizon : ConnectedActivityE6.Target.Order G w}
  {S : StepData c n} {tube : Pressure.Tube G S} {P : Rep G n} {P' : Rep G c}
  (H : Cash w x κ L Q horizon z tube P) {k : ℕ} (eyes : Eyes H P' e Γ Y K k)
  {R : Census V} {o : V → Site n} (A : Gallery α I o P R) (weights : V → ℝ)
  (U : Seal A weights b b') (positive : ∀ v, 0 < weights v) (slots : HasSlots P.p P.activities)
abbrev Addresses (P : Rep G n) (R : Census V) (o : V → Site n) :=
  Fog (fun i => (P.activities.forced i).support) R o

abbrev invoice := listCosts A weights positive slots U.supE U.crown (sighting A weights U) U.looks

abbrev regularFee (i : I) := Poly.toll weights (A.E.mode i) * U.supE i

abbrev crestOf (P : Rep G n) (R : Census V) (o : V → Site n) (i : Addresses P R o) :=
  (P.activities.forced i.val.1).support

abbrev forcedFee (i : Addresses P R o) :=
  Poly.toll weights i.val.2 * ‖(U.crown i.val.1).part i.val.2‖

variable (site : Addresses P R o → Site n) (inside : ∀ j, site j ∈ crestOf P R o j)
  (hard : Extra.Multi.Rooted (fun j => {site j}) (crestOf P R o) P.p.B P.p.supportExponent
    (forcedFee A weights U) r)

abbrev chargeSites (i : Trigger.Table A × Bool) :=
  Sum.elim (fun j : Fires A => A.E.ground j.val) (fun j : Addresses P R o => {site j}) i.1

abbrev increases (gain : I → ℝ) (i : Trigger.Table A × Bool) :=
  Sum.elim (fun j : Fires A => gain j.val) (fun _ : Addresses P R o => (1 : ℝ)) i.1
variable (t : α)

include inside hard in
private theorem scale (gain : I → ℝ) (pos : ∀ i, 0 ≤ gain i) {a : ℝ}
    (soft : Ac.Hit A.E.ground P.p.B (fun i => gain i * regularFee A weights U i) P.p.supportExponent a) :
    Lyric.Scale id (chargeSites A site) (brand (invoice A weights U positive slots) t) (increases A gain) (Fintype.card (Site S.ratio.count))
      P.p.supportExponent (2*(a+r)) S := by
  let M := brand (invoice A weights U positive slots) t
  let regular (i : Fires A) := A.E.ground i.val
  let f (i : Fires A) := gain i.val * regularFee A weights U i.val
  have rent : Ac.Hit regular P.p.B f P.p.supportExponent a := fun x =>
    budget_pull (b := (Subtype.val : Fires A → I)) Subtype.val_injective (soft x)
  have joined := WilsonPhysicalHistoryRootCrown.paired rent hard
  have crest (i : Trigger.Table A × Bool) : (M i).crest = Sum.elim regular (crestOf P R o) i.1 :=
    Trigger.wingE A slots i.1 i.2
  have wages (i : Trigger.Table A × Bool) :
      Palette.wages M (increases A gain) i = Sum.elim f (forcedFee A weights U) i.1 := by
    rcases i with ⟨j|j,h⟩
    · rfl
    · exact one_mul _
  refine ⟨?_, ?_, ?_, budget_nonneg (joined 0), Trigger.parentCost S⟩
  · rintro ⟨j|j,h⟩
    · exact pos _
    · exact zero_le_one
  · rintro ⟨j|j,h⟩ _
    · let y := (A.E.address j.val).site
      have anchor : y ∈ regular j := (A.E.address j.val).anchor
      exact ⟨y, anchor, (crest (.inl j,h)).symm ▸ anchor⟩
    · exact ⟨site j, mem_singleton_self _, (crest (.inr j,h)).symm ▸ inside j⟩
  · intro y
    convert joined y using 1
    funext i
    have ci := crest i
    have wi := wages i
    unfold M at ci wi
    dsimp only
    rw [ci, wi]

include site inside hard in
private theorem vote (gain : I → ℝ) (pos : ∀ i, 0 ≤ gain i) {a : ℝ}
    (soft : Ac.Hit A.E.ground P.p.B (fun i => gain i * regularFee A weights U i) P.p.supportExponent a)
    (fits : 2*(a+r) ≤ K) :
    Motto (brand (invoice A weights U positive slots) t) (increases A gain) 0 H P.p.supportExponent K Y (Eyes.sight eyes) := by
  let m := scale A weights U positive slots site inside hard t gain pos soft (S:=S)
  refine ⟨?_, eyes.grant, le_rfl, by simp, by simp⟩
  exact ⟨Site n, inferInstance, id, (chargeSites A site), m.currency, m.pin,
    (fun j => budget_loosen (m.crown j) fits), m.tolerance.trans fits,
    fun j => (Trigger.parentCost S j).trans eyes.count⟩

include positive in
omit [Countable I] in
private theorem boosted (rows : Set I) {d a : ℝ} (hd : 0 < d)
    (paid : Ac.Hit A.E.ground P.p.B (fun i => if i ∈ rows then regularFee A weights U i else 0) P.p.supportExponent a) :
    Ac.Hit A.E.ground P.p.B (fun i => (if i ∈ rows then d⁻¹ else 1) * regularFee A weights U i)
      P.p.supportExponent (b + d⁻¹*a) := by
  intro x
  have dpos := (inv_pos.mpr hd).le
  have money := budget_plus (U.payment.bright x) (budget_scale dpos (paid x))
  refine budget_mono money ?_ ?_
  · intro i
    have unit : 0 ≤ regularFee A weights U i :=
      mul_nonneg (Poly.worth positive (A.E.mode i)).le (U.perE i)
    split_ifs <;> positivity
  · intro i
    have raw := (U.payment.bright x).1 i
    by_cases hits : x ∈ A.E.ground i <;> by_cases take : i ∈ rows <;> simp [hits,take] at raw ⊢
    nlinarith

include site inside hard in
private theorem hike (rows : Set I) {d a : ℝ} (hd : 0 < d)
    (paid : Ac.Hit A.E.ground P.p.B (fun i => if i ∈ rows then regularFee A weights U i else 0) P.p.supportExponent a)
    (fits : 2*((b+d⁻¹*a)+r) ≤ K) :
    Motto (brand (invoice A weights U positive slots) t) (Creek.rage (Winter.hot A rows) d (fun _ => 1))
      0 H P.p.supportExponent K Y (Eyes.sight eyes) := by
  let gain (i : I) := if i ∈ rows then d⁻¹ else 1
  have h := vote H eyes A weights U positive slots site inside hard t gain
    (fun i => by dsimp [gain]; split <;> positivity) (boosted A weights U positive rows hd paid) fits
  convert h using 1
  funext i
  rcases i with ⟨j|j,v⟩ <;> simp [Creek.rage, Winter.hot, Mosaic.Verse.marked, gain, increases]

include site inside hard in
/-- The ordinary rent test and both tagged hikes read the same purchased
hard table, for each legitimate choice of the two submitted regular sectors. -/
theorem votes (oldRows longRows : Set I) {old long : ℝ} (ho : 0 < old) (hl : 0 < long)
    (oldPaid : Ac.Hit A.E.ground P.p.B (fun i => if i ∈ oldRows then regularFee A weights U i else 0) P.p.supportExponent old)
    (longPaid : Ac.Hit A.E.ground P.p.B (fun i => if i ∈ longRows then regularFee A weights U i else 0) P.p.supportExponent long)
    (ordinary : 2*(b+r) ≤ K) (increased : 2*(b+1+r) ≤ K) :
    Motto (brand (invoice A weights U positive slots) t) (fun _ => 1) 0 H P.p.supportExponent K Y (Eyes.sight eyes) ∧
    Motto (brand (invoice A weights U positive slots) t) (Creek.rage (Winter.hot A oldRows) old (fun _ => 1)) 0 H P.p.supportExponent K Y (Eyes.sight eyes) ∧
    Motto (brand (invoice A weights U positive slots) t) (Creek.rage (Winter.hot A longRows) long (fun _ => 1)) 0 H P.p.supportExponent K Y (Eyes.sight eyes) := by
  refine ⟨?_, hike H eyes A weights U positive slots site inside hard t oldRows ho oldPaid ?_,
    hike H eyes A weights U positive slots site inside hard t longRows hl longPaid ?_⟩
  · have v := vote H eyes A weights U positive slots site inside hard t (fun _ => 1)
      (fun _ => zero_le_one) (by simpa only [one_mul] using U.payment.bright) ordinary
    convert v using 1
    funext i
    rcases i with ⟨j|j,h⟩ <;> rfl
  · simpa [ho.ne'] using increased
  · simpa [hl.ne'] using increased

end YM.Integration.WilsonPhysicalHistoryRootFiscal
end

