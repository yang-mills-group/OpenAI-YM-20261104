import YM.MS.ScaleForest.Ordered

/-!
# Ordered MS-bar prescription: sum over subgraphs collapsed to their poles

Implement the individual sign-weighted products BEFORE summing. A
`quotients` entry (count multiplicity) is the integral on a contracted graph,
retaining the regulator also in the complement of the contracted
subgraph(s), with the negative pole parts inserted there. Take **all**
choices, including the choice of no subtraction. Uses ordered-scale
subgraphs: at a node which is not a bare vertex either collapse it to its
assigned local vertex or continue independently in each child. The local
vertex itself is obtained on the series *with* proper subtractions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest

open Set Filter MeasureTheory Real
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color
open Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave
open scoped Topology ContDiff

variable {G : Gauge} {b : Bool} {u r : ℤ} {h : ℕ} {X Y J : Flats G}

namespace GraphSum

def combine (b : Bool) (h : ℕ) (K : LineRule G) (X Y : Flats G) : Flats G :=
  integratePages h (connect b K X Y)

def traceLoop (h : ℕ) (K : LineRule G) (X : Flats G) : Flats G :=
  integratePages h (closePages K.half X)

def extensions (b : Bool) (h : ℕ) (K : LineRule G) (L R : List (Flats G)) : List (Flats G) :=
  L.flatMap fun X => R.map fun Y => combine b h K X Y

def quotients : {b : Bool} → {h : ℕ} → GraphSum G b h → List (Flats G)
| _, _, vertex V => [collapsed fun _ => V.symbol]
| _, h, loop U X => collapsed (loop U X).instructions.pole :: (X.quotients.map (traceLoop h U))
| b, h, bridge U X Y => collapsed (bridge U X Y).instructions.pole :: extensions b h U X.quotients Y.quotients

def proper : {b : Bool} → {h : ℕ} → GraphSum G b h → List (Flats G)
| _, _, vertex V => [collapsed fun _ => V.symbol]
| _, h, loop U X => X.quotients.map (traceLoop h U)
| b, h, bridge U X Y => extensions b h U X.quotients Y.quotients

theorem connect_sewable {f g} (hX : Sewable true r 4 f X) (hY : Sewable b u h g Y) (K : LineRule G) :
    Sewable b (r+u-2) h 0 (connect b K X Y) := by
  simpa only [connect,smul_zero] using (Sewable.bridge hX.lower hY K.ok).realScale (factor b)

theorem combine_left {f g t} (hX : Sewable true r 4 f X) (hY : Sewable true r 4 g Y)
    (ht : Sewable b u h t J) (K : LineRule G) : Pact (combine b h K (X+Y) J)
      (combine b h K X J + combine b h K Y J) := by
  have H := integratePages_add (connect_sewable hX ht K) (connect_sewable hY ht K)
  simpa only [combine,connect,bridgePages_left K.ok, smul_add] using H

theorem combine_right {f g t} (hX : Sewable b r h f X) (hY : Sewable b r h g Y)
    (ht : Sewable true u 4 t J) (K : LineRule G) : Pact (combine b h K J (X+Y))
      (combine b h K J X + combine b h K J Y) := by
  have H := integratePages_add (connect_sewable ht hX K) (connect_sewable ht hY K)
  simpa only [combine,connect,bridgePages_right K.ok, smul_add] using H

theorem traceLoop_add (hX : ClockD b 0 r X) (hY : ClockD b 0 r Y) (h : ℕ) (K : LineRule G) :
    Pact (traceLoop h K (X+Y)) (traceLoop h K X + traceLoop h K Y) :=
  pact_comp (integratePages_congr _ (closePages_add K.ok (clockMoon hX) (clockMoon hY)))
    (integratePages_add (Sewable.loop hX h K.ok) (Sewable.loop hY h K.ok))

abbrev Valid (b : Bool) (r : ℤ) (h : ℕ) (L : List (Flats G)) := ∀ X ∈ L, ∃ f, Sewable b r h f X

theorem quotient_valid (F : GraphSum G b h) : Valid b F.slots h F.quotients := by
  induction F with
  | vertex V => intro X hx; simp only [quotients,List.mem_singleton] at hx; rw [hx]; exact ⟨_, Sewable.ofHomogeneous V.cap (fun _ => V.scaling)⟩
  | @loop b h U X ih =>
    let T := loop U X
    intro Y hy; rw [quotients,List.mem_cons] at hy
    rcases hy with rfl|hy
    · exact ⟨_,Sewable.ofHomogeneous T.accepted.poleShape T.accepted.after.back⟩
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hy
    obtain ⟨f,hf⟩ := ih i hi
    exact ⟨0,(integrate_sewable (Sewable.loop hf.clock h U.ok)).2⟩
  | @bridge b h U X Y ih it =>
    let T := bridge U X Y
    intro Z hz; rw [quotients,List.mem_cons] at hz
    rcases hz with rfl|hz
    · exact ⟨_,Sewable.ofHomogeneous T.accepted.poleShape T.accepted.after.back⟩
    obtain ⟨i, hi, hz⟩ := List.mem_flatMap.mp hz
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hz
    obtain ⟨f,hf⟩ := ih i hi
    obtain ⟨g,hg⟩ := it j hj
    exact ⟨0, (integrate_sewable (connect_sewable hf hg U)).2⟩

private theorem pact_join (F : GraphSum G b h) (hF : Pact F.instructions.prep F.proper.sum) :
    Pact F.instructions.renorm F.quotients.sum := by
  cases F with
  | vertex V => rw [renorm_vertex, quotients,List.sum_singleton]; exact same_pact _
  | loop U F =>
    rw [quotients, List.sum_cons, Result.renorm, add_comm]; exact common (same_pact _) hF
  | bridge U F H =>
    rw [quotients, List.sum_cons, Result.renorm, add_comm]; exact common (same_pact _) hF

private theorem tailValid {X : List (Flats G)} (Z : Flats G) (he : Valid b r h (Z :: X)) :
    Valid b r h X := fun i hi => he i (List.mem_cons_of_mem Z hi)

theorem Valid.sew {X : List (Flats G)} (hx : Valid b r h X) : ∃ f, Sewable b r h f X.sum := by
  induction X with
  | nil => rw [List.sum_nil]; exact ⟨0,(coal_zero b h 0 r).eye,(coal_zero b h 0 r).force⟩
  | cons i L ih =>
    obtain ⟨f,hf⟩ := hx i (by simp)
    obtain ⟨g,hg⟩ := ih (tailValid _ hx)
    rw [List.sum_cons]
    exact ⟨_,hf.plus hg⟩

theorem full_trace (U : List (Flats G)) (K : LineRule G) (hU : Valid b r h U) :
    Pact (traceLoop h K U.sum) (U.map (traceLoop h K)).sum := by
  induction U with
  | nil => simp [traceLoop,closePages,integratePages]; exact same_pact _
  | cons i L ih =>
    let hx := tailValid _ hU
    simp only [List.sum_cons,List.map_cons]; exact pact_comp
      (traceLoop_add (hU i (by simp)).choose_spec.clock (Valid.sew hx).choose_spec.clock _ K)
      (common (same_pact _) (ih hx))

theorem full_join_right (R : List (Flats G)) (K : LineRule G) (hR : Valid b u h R)
    {f} (hm : Sewable true r 4 f X) :
    Pact (combine b h K X R.sum) (R.map (fun Y => combine b h K X Y)).sum := by
  induction R with
  | nil => simp [combine,connect,bridgePages,integratePages]; exact same_pact _
  | cons i L ih =>
    let hx := tailValid _ hR
    simp only [List.sum_cons,List.map_cons]; exact pact_comp
      (combine_right (hR i (by simp)).choose_spec (Valid.sew hx).choose_spec hm _)
      (common (same_pact _) (ih hx))

theorem full_join (L R : List (Flats G)) (K : LineRule G) (hL : Valid true r 4 L) (hR : Valid b u h R) :
    Pact (combine b h K L.sum R.sum) (extensions b h K L R).sum := by
  induction L with
  | nil => simp [combine,connect,bridgePages,integratePages,extensions]; exact same_pact _
  | cons i L ih =>
    let hx := tailValid _ hL
    obtain ⟨f,hf⟩ := hL i (by simp)
    simp only [List.sum_cons,extensions,List.flatMap_cons,List.sum_append]; exact pact_comp
      (combine_left hf (Valid.sew hx).choose_spec (Valid.sew hR).choose_spec _)
      (common (full_join_right R K hR hf) (ih hx))

/-- Precise forest sum before extracting this pole. In particular this uses
pole part of proper subgraphs times the **regulated integral** on the
contracted complement, with no replacement by a four-dimensional limit. -/
theorem forest_prepared (F : GraphSum G b h) : Pact F.instructions.prep F.proper.sum := by
  induction F with
  | vertex V => rw [proper,List.sum_singleton]; exact same_pact _
  | loop U X ih =>
    exact pact_comp
        (integratePages_congr _ (closePages_congr U.ok (clockMoon X.accepted.usable.clock)
          (clockMoon (Valid.sew X.quotient_valid).choose_spec.clock) (pact_join X ih)))
        (full_trace X.quotients U X.quotient_valid)
  | bridge U X Y ih it =>
    exact pact_comp
        (integratePages_congr _ (pact_scaled
          (bridgePages_congr U.ok (pact_join X ih) (pact_join Y it)) _))
        (full_join X.quotients Y.quotients U X.quotient_valid Y.quotient_valid)

theorem forest_summed (F : GraphSum G b h) : Pact F.instructions.renorm F.quotients.sum :=
  pact_join F F.forest_prepared

/-- Applied at a retained infrared cutoff `exp s`. In particular this
accounts for `exp(-2*z*ell*y)` per ell-page when a counterterm is used.
The forest sum with all UV limits taken therefore has exactly the
pole-subtracted value in dimension parameter, not only at four dimensions. -/
theorem forest_germ (F : GraphSum G b h) :
    ∀ᶠ z in dotty, ∀ y s,
      (F.quotients.map (fun X => Parade X h y s z)).sum = Parade F.instructions.renorm h y s z := by
  filter_upwards [took F.forest_summed] with z hz y s
  rw [treaty z hz h y s]; clear hz
  generalize F.quotients = L
  induction L with
  | nil => simp [pageZ]
  | cons i L ih => simp only [List.map_cons,List.sum_cons, page_add, Pi.add_apply,ih]

end GraphSum
end YM.MS.ScaleForest
