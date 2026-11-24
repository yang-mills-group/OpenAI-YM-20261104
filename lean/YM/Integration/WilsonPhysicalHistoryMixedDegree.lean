import YM.Integration.WilsonPhysicalHistoryMixedCofactor
import YM.FormalBulk08.Kemp.Where

/-! Normalized connected marked diagrams preserve the field-degree allowance
on the entire genuinely recursive mixed finite Wick history. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonPhysicalHistoryMixedDegree
open FormalBulk08 Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets
open Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision Stationary Lotus Shore
open Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Dawn Wine Rial Roof Dove
open Planned.PrimaryIntegral295 Place Film Carrier WilsonRunFormalMarkedStep
open Source RG16.Literal RG16.Guarding WilsonCoeffUV PhysicalNext.Repeat.Legato
open WilsonPhysicalHistoryMixedChain
open scoped Topology ENNReal Matrix ContDiff Classical BigOperators
variable {G : Gauge} {K : KernelChoices} {j t : ℕ}

private theorem remap_zero {I J : Type*} {r : ℕ} (A : I → J → ℝ) (T : Tile I r) (zero : T=0) :
    Lava.pearl A T=0 := (congrArg (fun Y=>Lava.pearl A Y) zero).trans (Lava.pearl_zero A r)

private theorem connected {V I : Type} [Fintype V] [Fintype I] [DecidableEq V]
    (H : Hull V I) (p Z : Pap (V⊕I)) (solved : Solved H p) (action : Fiery (rancho (cobalt H p)))
    {l : ℕ} (input : Young (rancho (lever H Z)) l) : Young (rancho (flag H p Z)) l := by
  intro e r live
  by_contra high
  apply live
  rw [extraction_mark H p Z solved action input e r (l+3*e) le_rfl]
  apply Finset.sum_eq_zero
  intro m hm
  have vanishes : dipper (aqua H.saddle) (swim (aqua H.saddle) (rancho (cobalt H p)))
      (rancho (lever H Z)) m e r=0 := by
    by_contra h
    exact high ((youth_egg (aqua H.saddle) input action m e r h).1)
  rw [vanishes,jetty_zero]

/-- Before integration, both genuine finite changes of variables retain
every coupling/field bidegree of an arbitrary finite incoming Pap. -/
private theorem input (P : Flight j t) (L : Lodge P.patch) (b : P.patch.Branches K G)
    (n : Side) (Z : Pap (wire G (n*P.patch.L))) {l : ℕ} (shape : Young (rancho Z) l) :
    Young (rancho (lever (ferry P b L n) (Reef.seat (Reef.floor K P L n) Z))) l := by
  let S := primary P.patch K n
  let E := saddleP G S L
  let Z' := Reef.seat (Reef.floor K P L n) Z
  have seat (e r : ℕ) (h : rancho Z e r=0) : rancho Z' e r=0 := by
    have shifted := tor_yolk (G:=G) S L Z e r
    rw [h,jetty_zero] at shifted
    have zeroMove : rancho (joust E Z') e r=0 := by
      exact shifted.trans (remap_zero _ _ (remap_zero _ _ rfl))
    rw [infer_joust E Z' e r]
    change jetty E (rancho (joust E Z') e r)=0
    rw [zeroMove,jetty_zero]
  intro e r live
  apply shape e r
  intro h
  apply live
  rw [tilt_hull P L b n _,rename_income]
  exact (congrArg _ (seat e r h)).trans (pearl_zero _ _)

theorem block (P : Flight j t) (L : Lodge P.patch) (ρ : ChartRatio G) (b : P.patch.Branches K G)
    (W : Mesa.Pot G) (n : Side) (tag : (primary P.patch K n).Choices) (Z : Pap (wire G (n*P.patch.L)))
    (ratio : LocalRatio ρ) (order : 4 ≤ t) (ready : Story W (pink K.penalty P.wing))
    {l : ℕ} (shape : Young (rancho Z) l) :
    Young (rancho (Reef.tossed P ρ b L n tag (Mesa.stone W (n*P.patch.L)) Z)) l := by
  let H := ferry P b L n
  let p := flush (Reef.floor K P L n) tag ρ (Mesa.stone W _)
  obtain ⟨σ,C,hσ,hC,hf⟩ := aone P (K:=K) G order
  obtain ⟨v,B,hv,hB,stock,-⟩ := colors G K.penalty K.penalty_pos P.legal
  have lead := stoned_main hv.le hB.le (stock P.wing).1 ready.toVivid ready.ink (n*P.L)
  have solve := Reef.consolidate P ρ b L n ratio tag (Mesa.stone W _) lead order
  have old : Fiery (rancho (cobalt H p)) := bath_vac P L W ρ b n tag ready.toVivid ratio hσ hC hf
  exact connected H p (Reef.seat (Reef.floor K P L n) Z) solve old (input P L b n Z shape)

private theorem resized {c f : Side} (h : c=f) (Z : Pap (wire G c)) {l : ℕ} (hz : Young (rancho Z) l) :
    Young (rancho (h ▸ Z : Pap (wire G f))) l := by cases h; exact hz

variable (R : Run G) (L : ∀ i, Lodge ((R.family.path.levels.clock.op i 0).patch)) (a : hue G)

theorem one (simple : G.Simple) {N per i l : ℕ} (live : i<N) (tag : Tags R N per)
    (Z : Pap (wire G (R.family.S.side (i+1) per))) (shape : Young (rancho Z) l) :
    Young (rancho (once R L a N per tag i Z)) l := by
  let V := R.family.path.levels
  let P := destination V N i
  let n := R.family.S.side i per
  let bs := fun k=>(V.blocks k 0).branches
  let W := Dove.model V L bs R.metals.O a N (i+1)
  have hs : R.family.S.side (i+1) per=n*P.patch.L := Subtype.ext (V.clock.op i per).sizes
  let Z' : Pap (wire G (n*P.patch.L)) := hs ▸ Z
  change Young (rancho (Reef.tossed P R.metals.O (bs i) (L i) n (tag i) (Mesa.stone W (n*P.patch.L)) Z')) l
  exact block P (L i) R.metals.O (bs i) W n (tag i) Z' R.alloy.B.ratio (V.clock.adm i)
    (Dove.genu V L bs R.metals.O a R.alloy.B.ratio simple (i:=i+1) (N:=N) live).toStory (resized hs Z shape)

/-- Arbitrarily many genuine original physical dates, on one N and period,
with the same engineering allowance throughout. -/
theorem stable (simple : G.Simple) {N per k u l : ℕ} (ku : k ≤ u) (top : u ≤ N) (tag : Tags R N per)
    (Z : Pap (wire G (R.family.S.side u per))) (shape : Young (rancho Z) l) :
    Young (rancho (run R L a N per tag ku Z)) l := by
  induction u,ku using Nat.le_induction with
  | base => simpa only [at_top] using shape
  | succ u hu ih =>
      rw [from_above R L a N per tag hu]
      exact ih (u.le_succ.trans top) _ (one R L a simple top tag Z shape)

end YM.Integration.WilsonPhysicalHistoryMixedDegree

