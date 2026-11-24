import YM.FVA2.SpringUniq

/-! Implement a separately booked MS field system on a given physical warehouse and bulk
prescription. The marked Taylor program retains the physical fees and its quantum BV generator. -/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.MSPhysicalDeckChange

open Filter Function Set Finset MeasureTheory
open MS MS.Plane MS.Land MS.Landau MS.Landau.Detect MS.Koszul MS.Book MS.Book.Convolve
open MS.Book.Program MS.Local MS.Local.Physical MS.Local.BV MS.Local.BV.Woven MS.Menus MS.Theater
open MS.Pearl MS.Train MS.Outlook MS.Mach MS.Hem.Mell MS.SpinCode MS.Dock
open MS.Plane.Wire MS.Tone MS.Tone.Frame MS.High MS.Wind MS.Native MS.Native.Wilsonian
open MS.Rake MS.Rake.Geo MS.Vane MS.Echo MS.Lifting MS.High.Knobs MS.Motif MS.Motif.Literal
open FVA2 FVA2.ColorCode Maxwell
open scoped BigOperators Classical Topology ContDiff

variable {G : Gauge} (B A : Deck G)

def coordinates (h r : ℕ) : B.carries (h : ℤ) r ≃ₗ[ℝ] A.carries (h : ℤ) r :=
  (Studio B h r).trans (Studio A h r).symm

theorem primitive (h r : ℕ) (x : B.carries (h : ℤ) r) :
    ∃ K ∈ Lease G ((h : ℤ) - 1) r (-1),
      (x : Law G) = (coordinates B A h r x).val + natQ K := by
  let y := coordinates B A h r x
  let q : Film0 G h r := Resume B h r x - Resume A h r y
  have hi : Studio A h r y = Studio B h r x := (Studio A h r).apply_symm_apply _
  have hr : reduceEq q.val = 0 := by
    have he := congrArg (fun z : IvSpace G h r => z.val) hi
    change reduceEq (Resume A h r y).val = reduceEq (Resume B h r x).val at he
    change reduceEq ((Resume B h r x).val - (Resume A h r y).val) = 0
    rw [map_sub, he, sub_self]
  have hn := (certN q.property.2 q.property.1).mpr hr
  change orbit G ((Resume B h r x).val - (Resume A h r y).val) ∈ Null G h r at hn
  rw [map_sub, honor B x, honor A y] at hn
  obtain ⟨K, hK, hEq⟩ := hn.2
  change natQ K = x.val - y.val at hEq
  exact ⟨K, hK, by change x.val = y.val + natQ K; rw [hEq]; abel⟩

def weight (h r : ℕ) (i : B.BIndex h r) (j : A.BIndex h r) : ℝ :=
  (Module.finBasis ℝ (A.carries (h : ℤ) r)).repr
    (coordinates B A h r ((Module.finBasis ℝ (B.carries (h : ℤ) r)) i)) j

theorem raw (h r : ℕ) (i : B.BIndex h r) :
    ∃ K ∈ Lease G ((h : ℤ) - 1) r (-1),
      B.raw h r i = (∑ j, weight B A h r i j • A.raw h r j) + natQ K := by
  let U := Module.finBasis ℝ (B.carries (h : ℤ) r)
  let V := Module.finBasis ℝ (A.carries (h : ℤ) r)
  let y := coordinates B A h r (U i)
  obtain ⟨K, hK, he⟩ := primitive B A h r (U i)
  refine ⟨K, hK, he.trans ?_⟩
  have hs : ∑ j, weight B A h r i j • A.raw h r j = y.val := by
    rw [show ∑ j, weight B A h r i j • A.raw h r j =
      (A.carries (h : ℤ) r).subtype (∑ j, V.repr y j • V j) by simp only [map_sum, map_smul]; rfl,
      V.sum_repr]
    rfl
  rw [hs]

variable {B A} {O : Booked B} {Q : Booked A}

theorem bulk (D : MS_Data G O) (M : MS_Data G Q) :
    Archive 4 D.bulk = Archive 4 M.bulk :=
  FVA2.ArchTurn.archive_h (unique_B D.bulkOK M.bulkOK).2
    (fun i => (Dock.gang (D.bulkOK i)).dost) (fun i => (Dock.gang (M.bulkOK i)).dost)

abbrev Fees (B A : Deck G) := ∀ d : ℕ, Plaid B d → Acts A d

section implementation

variable (V : BookM A) (p : Team) (D : MS_Data G O)

def Implements (T : Fees B A) : Prop :=
  ∀ d i, Fixed (col (horizonM V p (T d i))) (Archive d (D.marks d i)) false d 0

theorem quantum (hG : G.Simple) (hb : Fixed (col (skyline G p)) (Archive 4 D.bulk) true 4 1) :
    ∃ T : Fees B A, Implements V p D T := by
  have h d (i : Plaid B d) : ∃ T : Acts A d,
      Fixed (col (horizonM V p T)) (Archive d (D.marks d i)) false d 0 :=
    High.mark (k := Wind.SeekM V p d) hb
      (Outlook.fieldD D.bulkOK (D.markOK d i) wisdom (O.law d i).moodQ)
      (by omega) (Wind.mark_seekM V hG) (0 : Acts A d)
  choose T ht using h
  exact ⟨T, ht⟩

theorem selected (M : MS_Data G Q) (P : Prescription A) (hG : G.Simple)
    (hP : TaylorOKM M V P) : ∃ T : Fees B A,
    Fixed (col (skyline G P.team)) (Archive 4 D.bulk) true 4 1 ∧ Implements V P.team D T := by
  have hb : Fixed (col (skyline G P.team)) (Archive 4 D.bulk) true 4 1 := by
    rw [bulk D M]; exact hP.bulk
  obtain ⟨T, hT⟩ := quantum V P.team D hG hb
  exact ⟨T, hb, hT⟩

theorem generator {d : ℕ} (a : Acts A d) :
    Echo.Menu p (Menus.scoreM V p a) (Menus.rentM V p a) := by
  refine ⟨⟨Menus.prim a, ⟨(fun i y => (a i).proof.actual y), (fun i => ⟨_, (a i).proof.ranks⟩),
    (fun i y => (a i).proof.calm y), (fun i => (a i).proof.polyn),
    (fun _ _ h => Bool.noConfusion h)⟩, ?_⟩⟩
  intro y
  change Menus.motto p a y = Menus.scoreM V p a y - Menus.rentM V p a y
  rw [Menus.scoreM]
  abel

end implementation

section kernels

open Plane Koszul Heat Tone Momentum Landau Detect Book High Frame Flux Osc Fiddle Snap City Wire Wind Signal Latch Job Belt
open Garment Outlook Geo Land Pearl Train Dock Emit Menus Book.Convolve LogTime LogTime.IntervalFamily Program

variable {I J : Type} (V : BookM A) (P : Prescription A)
variable (T : Fees B A) (v : J → Rake.Label B) (L : Geo I)

def site (u : Rake.Label B) : Rake.Site G I :=
  Rake.circle L.η (col (horizonM V P.team (T u.h u.item)))

private theorem lawful (hG : G.Simple) (u : Rake.Label B) :
    Ven (fun _ => planeF) (constantP G I (LowP G)) (constantP G I (PlanetL G))
      (initials L P) (site V P T L u) := by
  let a := T u.h u.item
  let H := horizonM V P.team a
  have hP := Marked.law (Wind.mark_seekM V (d := u.h) (p := P.team) hG) a
  have hg := hP.road
  change Domain.Flow _ _ _ _ _ (Wind.col H) at hg
  have hf (n : ℕ) : Wind.Fees false 0 (H n) := (Wind.aquaM V P.team a).owes n
  intro n
  refine ⟨nameWarm (H n) (hf n), fun i w t => ?_⟩
  have hh := pour (spaceL G) hg (L.η i) w n t
  rw [ergo (η := L.η)] at hh
  let f := H n (L.η i)
  have he : sailP (fun _ => μzone) (constantP G I (LowP G)) (site V P T L u n) i t =
      cycle (PlanetL G t) planeF (f (Real.exp t)) :=
    (startCycle f 0 (hf n |>.stay (L.η i)) _ _).symm
  rw [show sailP (fun _ => (spaceL G).measure) _ (circle _ (col H) n) i t = _ from he] at hh
  exact hh

private theorem tip (u : Rake.Label B) (k : ℕ) : Tip L true false u.h (site V P T L u k) := by
  have h : Wind.Fees false 0 _ := (Wind.aquaM V P.team (T u.h u.item)).owes k
  exact ⟨collectFee h, nameWarm _ h, Lease.sticks (sunX L _ h) (fun i => rank_e L i u.h)⟩

variable {L} {x : Position J I}

theorem tour (hG : G.Simple) (hx : Mesh L x) :
    Tour (constantP G I (LowP G)) (constantP G I (PlanetL G)) L x true
      (initials L P) (site V P T L ∘ v) (Rake.Label.h ∘ v) :=
  ⟨hx, Geo.masterL .., fun _ _ => tagL L P _, fun j k => tip V P T L (v j) k,
    fun j => lawful V P T L hG (v j)⟩

variable (D : MS_Data G O) {K : Belt I}

private theorem estimates (hb : Fixed (col (skyline G P.team)) (Archive 4 D.bulk) true 4 1)
    (hT : Implements V P.team D T) (hK : Gold L K) :
    Arch K (constantP G I (LowP G)) (constantP G I (PlanetL G)) (initials L P)
        (site V P T L ∘ v) (Rake.Label.h ∘ v) ∧
      Arch K (constantP G I (PlanetD G)) (constantP G I (PlanetD G)) (approach L D)
        (rowM L D ∘ v) (Rake.Label.h ∘ v) ∧
      ArcS K (constantP G I (LowP G)) (constantP G I (PlanetL G))
        (constantP G I (PlanetD G)) (constantP G I (PlanetD G)) (initials L P)
        (approach L D) (site V P T L ∘ v) (rowM L D ∘ v) (Rake.Label.h ∘ v) := by
  have h₀ (n : ℕ) (hn : 0 < n) :=
    partials hK (show 1 ≤ n from hn) (fun r hr => hb n hn r hr)
  have h₁ (j : J) (n : ℕ) := partials hK (show 0 ≤ n from Nat.zero_le n)
    (fun r hr => hT (v j).h (v j).item n (Nat.zero_le n) r hr)
  have he i : 1 ≤ K.price.length i := hK.day i ▸ Real.one_le_exp (hK.paid i)
  have hc := cost_D (G := G) hK.day
  exact ⟨⟨CoupleY he hK.day, Mate0 he hK.day, fun i hi => (h₀ i hi).1,
      fun j n => (h₁ j n).1⟩,
    ⟨fun i j => polar (hc i j), hc, fun i hi => (h₀ i hi).2.1, fun j n => (h₁ j n).2.1⟩,
    ⟨submarineT he hK.day (phaseY hK), submarineP he hK.day (phaseY hK),
      fun i hi => (h₀ i hi).2.2, fun j n => (h₁ j n).2.2⟩⟩

theorem covers [LinearOrder J] (hG : G.Simple) (hx : Mesh L x)
    (hb : Fixed (col (skyline G P.team)) (Archive 4 D.bulk) true 4 1)
    (hT : Implements V P.team D T) :
    ∃ U Y : Rake.Dance G I J,
      Fields x (fun _ => planeF) (constantP G I (LowP G)) (constantP G I (PlanetL G))
        (initials L P) (site V P T L ∘ v) U ∧ DOrd O L D v x Y ∧
      ∀ S : Finset J, S.Nonempty → ∀ n : ℕ, let k := charge (Rake.Label.h ∘ v) S
        Verdict L k 0 (U S n) ∧ Verdict L k 0 (Y S n) ∧ Verdict L k eps_gain (U S n - Y S n) := by
  have hU := tour V P T v hG hx
  have hY := builder D hx v
  obtain ⟨U, h₁⟩ := formal hU
  obtain ⟨Y, h₂⟩ := formal hY
  obtain ⟨Z, X, ZX⟩ := estimates V P T v D hb hT (gulfG (P := L))
  obtain ⟨Q, E, QE⟩ := estimates V P T v D hb hT (westV (P := L))
  exact ⟨U, Y, h₁, h₂, fun _ hS n => ⟨closure hU Z Q h₁ hS n, closure hY X E h₂ hS n,
    trade hU hY Z X Q E ZX QE h₁ h₂ hS n⟩⟩

end kernels

end YM.Integration.MSPhysicalDeckChange
