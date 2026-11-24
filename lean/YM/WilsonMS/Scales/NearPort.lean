import YM.WilsonMS.Scales.DifferentialScale
/-!
# X-space perturbative predictions from the stipulated lattice regulator

Intrinsic construction of the Wilson outputs with comparison projection.
Policy is X behavior (`Initialize`:top stencils, Haar chart, gauge tree;
`Store`: external coupled diagnostics all horizons;
`Rose.Pick`: finite fixed triangle probe and coupling convention).
Finite-regulator data across `Front`.
Then choose a strict triangular adjustment on the field matrix. This is
characterized independently (pure scaling criterion on these predictions).
Thus the results can be stated without defining Wilson PT using an MS match.
The existence, smooth scale dependence and coherence through arbitrary
orders/horizons are consequences, not definitions.

Representative away from conf n arbitrary. We compare kernels only on conf n.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Network
open Function Set Filter MeasureTheory Real Finset Metric
open XSpace XSpace.Normalize XSpace.Expense XSpace.Cirrus XSpace.TestBudget XSpace.Structure1
open Maxwell Maxwell.Free Maxwell.Wick VisitH
open MS MS.Menus MS.Theater MS.Land MS.Book MS.Book.Program MS.Book.Convolve MS.Logarithm
open PowerSeries (coeff mk X C constantCoeff invOfUnit)
open Fiscal BMenu Rider Reservoir VisitH Sea Fray FrameConj FrameConj.Gates FrameX Ice TraceMC GFlow
  Datum
open scoped BigOperators Topology Classical ContDiff
variable {G : Gauge} {d k n m j : ℕ}
local notation "BΨ" => Ensure.deck G
local notation "𝕄" => XSpace.Mesh
section native
variable (W : Initialize G) {V : Store G} (Y : Rose.Pick V)

def Ends (H : Scheme G) (X : ∀ d, Reports G d) :=
  (∀ d, Marked (H d) (X d)) ∧
    ∀ d i n (t : Test n) p, Tendsto (fun k => Rose.proposed W Y k d i n t p) Front (𝓝 (X d i n t p))

def prospect : (Scheme G) × (∀ d, Reports G d) :=
  if h : ∃ p : (Scheme G) × (∀ d, Reports G d), Ends W Y p.1 p.2 then h.choose
  else (fun _ _ _ _ => 0, fun _ _ => 0)

abbrev forecast (W : Initialize G) (Y : Rose.Pick V) :=
  (prospect W Y).1

abbrev report (W : Initialize G) (Y : Rose.Pick V) :=
  (prospect W Y).2
variable {X P : Scheme G} {A B : ∀ d, Reports G d}

lemma unique (h : Ends W Y X A) (ht : Ends W Y P B) : A = B ∧ ∀ d, Equad (X d) (P d) := by
  have hP : A = B := by
    ext1 d
    ext1 j
    ext1 k
    ext1 p
    ext1 t
    exact tendsto_nhds_unique (h.2 d j k p t) (ht.2 d j k p t)
  refine ⟨hP, fun d n x hx => ?_⟩
  funext i
  ext1 p
  obtain ⟨hc, hM⟩ := h.1 d n i p
  obtain ⟨he, hK⟩ := ht.1 d n i p
  exact (Test.unique_kernel hc he).mp (fun q => (hM q |>.symm).trans (by rw [hP, hK q])) hx

def mandates : Traveling G :=
  if h : ∃ V' : Traveling G, ∀ t, Linked (forecast W Y) t (V'.Q t) (V'.r t) then h.choose
  else ⟨fun _ d => deck (0 : Pick G d), fun _ => PowerSeries.X⟩

def shiftAll (d : ℕ) : Guard G d :=
  if h : ∃ P, Anchored (mandates W Y) (P : Guard G d) then h.choose else 1

def check : Scheme G :=
  revising (forecast W Y) (shiftAll W Y)

def checked (d : ℕ) :=
  realm (shiftAll W Y d) (report W Y d)

def tilings (d : ℕ) (m : 𝕄) :=
  realm (shiftAll W Y d) (Rose.proposed W Y m d)

def tilings_pt (d : ℕ) (x : Cirrus.Sample n) :=
  pivot (shiftAll W Y d) (Rose.measureₓ W Y d x)

lemma starts {T : ℝ → Links G} {Q : ℝ → Cn} (h : ∀ d, Equad (X d) (P d))
    (hp : ∀ t, Linked P t (T t) (Q t)) : ∀ t, Linked X t (T t) (Q t) := fun t =>
  ⟨(hp t).ground, (hp t).normal, fun d =>
    ((sweep_t (h d) t).act (T t d)).trans ((hp t |>.origin d).trans ((h d).symm.sub (Q t)))⟩
section comp
variable (hG : G.Simple) {M : Booked (Ensure.deck G)} (F : MS_Data G M)
  {A : Prescription (Ensure.deck G)} (hA : Installed W F A) (hp : Commuting A)
include hA hp hG

lemma commit : Ends W Y (ΨScheme Y F) (softX Y F 0) :=
  ⟨fitted Y F, fun d i _ t p => ((removing Y W A F 0 hG hA hp i d).eval p t).limit⟩

lemma obtains : (report W Y) = softX Y F 0 ∧ ∀ d, Equad (forecast W Y d) (ΨScheme Y F d) := by
  obtain hT := commit W Y hG F hA hp
  apply unique W Y _ hT
  have he : ∃ p : (Scheme G) × _, Ends W Y p.1 p.2 := ⟨(ΨScheme Y F, softX Y F 0), hT⟩
  rw [report, forecast, prospect, dif_pos he]
  exact he.choose_spec

lemma testifies : Ends W Y (forecast W Y) (report W Y) := by
  unfold forecast report prospect
  split_ifs with h
  exact h.choose_spec
  exact False.elim (h (⟨(ΨScheme Y F, softX Y F 0), commit W Y hG F hA hp⟩))

lemma MAN : mandates W Y = tripX Y F := by
  obtain hx := obtains W Y hG F hA hp
  have he : ∀ t, Linked (forecast W Y) t ((mandates W Y).Q t) ((mandates W Y).r t) := fun t => by
    have hX : ∃ V' : Traveling G, ∀ p, Linked (forecast W Y) p (V'.Q p) (V'.r p) :=
      ⟨tripX Y F, starts hx.2 (growth Y hG hA hp)⟩
    rw [mandates, dif_pos hX]
    exact hX.choose_spec t
  have ht (p : ℝ) := single Y hG hA hp (starts (fun d => (hx.2 d).symm) he p)
  have he (A B : Traveling G) (h : A.Q = B.Q) (ht : A.r = B.r) : A = B := by
    cases A
    cases B
    congr
  exact he _ _ (funext fun i => (ht i).1) (funext fun i => (ht i).2)

lemma adjusts : shiftAll W Y = uprightN Y F := by
  ext1 d
  unfold shiftAll
  rw [MAN W Y hG F hA hp]
  split_ifs with h
  exact Anchored.unique (growth Y hG hA hp) h.choose_spec (grade_N Y hG hA hp d)
  exact False.elim (h ⟨_, grade_N Y hG hA hp d⟩)

lemma sameCheck (d : ℕ) : Equad (check W Y d) (finale Y F d) := by
  unfold check finale revising
  rw [adjusts W Y hG F hA hp]
  exact (obtains W Y hG F hA hp |>.2 d).act _

lemma nReady (d : ℕ) : CloseP (shiftAll W Y d) := by
  rw [adjusts W Y hG F hA hp]
  exact freeN Y hG hA hp d

lemma end_reads (d : ℕ) : Marked (check W Y d) (checked W Y d) := fun i =>
  pivotFund ((testifies W Y hG F hA hp).1 d i) _

lemma diagram (d : ℕ) :
    checked W Y d = realm (Zx Y F d) (substitute (ψW Y F) (fun i => Continuum F 0 i d)) := by
  refine
    Marked.unique (end_reads W Y hG F hA hp d) (S := _) (T :=
      GFlow.Act (GFlow.Sub (ψW Y F) (GMS F 0 d)) (Zx Y F d))
      (fun i => pivotFund (FundSwim (coupon_stage F 0 d i) _) _) ?_
  rw [← Ck Y hG hA hp]
  exact sameCheck W Y hG F hA hp d

lemma ranges (d j : ℕ) : NShape (fun i => tilings W Y d i j) (checked W Y d j) := by
  obtain ⟨p, hp'⟩ := (nReady W Y hG F hA hp d).1.actions
  unfold tilings checked
  rw [hp', (obtains W Y hG F hA hp).1]
  exact Ringlet _ _ (fun i _ => removing Y W A F 0 hG hA hp i d) (fun _ _ => Fast.const _)

lemma wound (d j : ℕ) (v : Fin n → Sec G d) (K : Set (Points n)) (ht : IsCompact K)
    (hK : K ⊆ conf n) : Vitals (fun i => tilings_pt W Y d i j v) (fun x => check W Y d n x j v) K := by
  let X := tilings_pt W Y d (n := n)
  obtain h :=
    Gates.liftT (j := j) (X := Rose.measureₓ W Y d) (P := ΨScheme Y F d n)
      (fun i _ => fun z => on_position Y W A F 0 hG hA hp K ht hK i d _) (fun _ => uprightN Y F d) _
      (fun i _ _ => Fast.const _) v
  obtain hE := sameCheck W Y hG F hA hp d
  unfold tilings_pt
  rw [adjusts W Y hG F hA hp]
  obtain ⟨hh, a, ha, C, hC, hT⟩ := h
  refine ⟨?_, a, ha, C, hC, hT.mono fun i hi k c hc hx => ?_⟩
  · unfold Climb.Traced
    convert hh using 1
    funext x p g
    dsimp only
    rw [hE n (hK x.property)]
    rfl
  rw [hE n (hK hx)]
  exact hi k c hc hx

lemma horizon_flow (d : ℕ) :
    Connect (shiftAll W Y) ∧
      ∀ᶠ m in Front, ∀ i : ℕ, recruit (step d) (tilings W Y (d + 1) m i) = tilings W Y d m i := by
  obtain hh := adjusts W Y hG F hA hp
  have hv : Connect (shiftAll W Y) := hh.symm ▸ cN Y hG hA hp
  refine ⟨hv, ?_⟩
  filter_upwards [Rose.horizon W Y d (d + 1) (by omega)] with i hi v
  unfold tilings
  rw [tail_free _ _ (hv d)]
  exact congr_arg (fun P : Reports G d => realm _ P v) (funext hi)

lemma step_check (d i : ℕ) : recruit (step d) (checked W Y (d + 1) i) = checked W Y d i := by
  ext1 n
  ext1 p
  ext1 q
  obtain hv := ((ranges W Y hG F hA hp (d + 1) i).eval (step d ∘ q) p).limit
  rw [recruits]
  exact
    tendsto_nhds_unique
      (Tendsto.congr' (f₂ := fun m => tilings W Y d m i n p q)
        ((horizon_flow W Y hG F hA hp d).2.mono fun i hi =>
          congr_arg (fun P : Prediction G d => P n p q) (hi _))
        hv)
      (((ranges W Y hG F hA hp d i).eval q p).limit)
end comp
end native
end YM.WilsonMS.Network
