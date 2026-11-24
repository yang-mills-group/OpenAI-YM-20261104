import YM.Comparison.RG02.Bare.View
import YM.Comparison.RG02.Sources.Aligned
import YM.Extra.MULTISOURCE_TRAJECTORIES.BirthBounds
import YM.Planned.PRIMARY_INTEGRAL_295.Columns
/-!
# One-step test with real stencils and valuation

 Implements mark construction on bare (last step only). Vertices in fog are *rescaled* -- read
 with bare g (coupling from the actual β read on this cutoff); no absorbing the true threshold
 schedule into formal time. Given data group weights and amplitudes, makes the stencil form of
 `Bulk.Colors` with marker parts. Equal physical labels allowed. Rank compensation uses radius-
 coherent *constants* and g^(K-j) to collect columns.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Bare.Signals
open Function Filter Finset MeasureTheory ProbabilityTheory RG Precision Lattice Wilson Exterior Tree
open PertExtension.Series PertExtension.Series.Tested
open Marker Multi Order YM.Next.SectorChange Integral Actual Laplace Fleet Source
open YM.Extra.Trajectories (connected pass_connected Probes places_combined degree)
open YM.Comparison.RG02.Assembly (GradeAt)
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] (R : Census V)

section singleton
variable {n : Side} (X : V→ℝ→ Config G n→ℂ) (L : V → ℕ)
omit [Fintype V] in
private lemma sing_eq {t : R.Mode} (h : ∃ i : V, R.fire i=t) (i : V) (hi : R.fire i=t) : h.choose=i:= (R.fire_inj ..).1 (h.choose_spec.trans hi.symm)

def flare : Bulk.Colors R G n where
   vac:=0
   mark s:= if h : ∃ i,R.fire i=s.val then X h.choose else 0
   power s:= if h : ∃ i,R.fire i=s.val then L h.choose else 0
lemma flare_well (h : ∀ i, GradeAt (L i) (Bulk.projected (X i))) (H : ∀ i t,Envelope (X i t)) (HG : ∀ i t,GaugeInvariant (X i t)) : Bulk.Well (flare R X L) := by
   refine ⟨GradeAt.grade_zero _,?_, fun _ _ _=> rfl, ?_, fun _=>Envelope.const _, ?_⟩
   · intro i; dsimp only [flare]; split; exact h _; exact GradeAt.grade_zero _
   · intro i t; dsimp only [flare]; split; exact HG _ _; exact fun _ _=> rfl
   intro i t; dsimp only [flare]; split; exact H _ _; exact Envelope.constC _
lemma flare_good (h : ∀ i, Allows (X i)) : Starts (flare R X L):=by intro i; dsimp only [flare]; split; exact h _; exact Allows.const _
lemma singleton (U : Config G n) (t : ℝ): markedLog t U (flare R X L)= Multi.lambda R (fun i=> (t^(L i))⁻¹ • X i t U) := by
    ext i; by_cases h:i=R.quiet; · subst i; rw [markedLog,part_lit_quiet,lambda_quiet]
    let a: Hot R:=⟨i,(Cumulants.hot_iff_ne _).2 h⟩; unfold markedLog; rw [show ∀ v:Hot R→ℂ,(lit R v).part i=v a from fun v=> part_lit v a]
    dsimp only [flare]; split
    next h=> exact (h.choose_spec ▸ lambda_part (fun i=> (t^(L i))⁻¹ • X i t U) h.choose).symm
    next h=>
      change _ • (0:ℂ) = _; unfold Multi.lambda; rw [smul_zero,Poly.part_sum]; symm; apply sum_eq_zero; intro j _; rw [Poly.part_send,if_neg (fun e=> h ⟨j,e.symm⟩)]
end singleton
variable {C : Family G} {N p d : ℕ} {H : History G}
  (A : Probes C V N p) (o : V)
local notation "V'"=>Config G (C.side N p)
local notation "X"=>fieldDir G (C.side N p) 1
local notation "L" x:max=> C.labels.level (A.d x)
local notation "I" x:max=> Labels.Frame.Index (C.labels.level (A.d x))
local notation "S" o:max=> C.localSection (A.d o)
local notation "o₁" o:max=> A.place o

open YM.Planned.PrimaryIntegral295

variable {n : Side}
def title (i : (C.labels.level d).Index) := ((C.labels.level d).grades i).2

def locus (D : Labels.Frame G d) (T : SectionData D) (Y : Site n) (x : fieldDir G n 1) (u : Place.Spot T.stencil) := x (wrap n (Place.placeEdge u).1+Y,coord (Place.placeEdge u).2)
private lemma located (D : Labels.Frame G d) (T : SectionData D) (Y : Site n) (x : fieldDir G n 1) (i : D.Index) : T.places (Pi.single i 1) Y (represent x)=Place.column T i (locus D T Y x):= by
   apply T.cylinder_local (Pi.single i 1); intro e h hx
   let a : Place.Spot T.stencil:= ⟨(⟨e.1,h⟩,e.2),hx⟩
   change expandAt Y (represent x) _=_
   rw [← show Place.placeEdge a=e from rfl,expandAt,Place.pore_site, Work.F03.represent_link]; rfl
lemma primary (i : (C.labels.level d).Index) (H : Bid.pop (C.localSection d)) (x : Site n) : GradeAt (title (C:=C) i) ( (C.localSection d).places (Pi.single i 1) x ∘ represent (G:=G) (n:=n)) := by
   let Q:= C.localSection d; let v:= C.labels.level d; let f:= locus v Q x
   have he : GradeAt (title (C:=C) i) (Place.column Q i):= ⟨(Place.column_smooth Q i).contDiffAt,Place.radials_vanish Q H i⟩
   have h : ContDiff ℝ ω f:= contDiff_pi.mpr fun _ => contDiff_apply ℝ _ _
   rw [show ( (C.localSection d).places _ _ ∘ _) = Place.column Q i ∘ f from funext fun a=> located v Q x a i]
   exact GradeAt.coarse he h.contDiffAt rfl

-- `fee` arbitrary weights per basis selected; no re-tuning. rank upper bounds from birth
variable (fee : ∀ o:V, (C.labels.level (A.d o)).Coeff)

abbrev degreeM (i) := Extra.Trajectories.degree C (A.d i)
def stoked (t : ℝ) (s : V') (i : (L o).Index) := t^(degreeM A o-title (C:=C) i) • ((fee o i) * (S o).places (Pi.single i 1) (o₁ o) s)

def fire (o : V) (t :ℝ) (s : V') := ∑ i:I o, stoked A o fee t s i
omit [DecidableEq V] [Fintype V] in
lemma fire_cont : Continuous (Function.uncurry (fire A fee o)) := by
   unfold fire stoked; apply continuous_finsetSum -- uncertain
   intro i _; exact Continuous.smul (continuous_fst.pow (degreeM A o-title (C:=C) i)) (continuous_const.mul (((S o).continuous_places ..).comp continuous_snd))
variable (hA : ∀ i,Bid.pop (C.localSection (A.d i)))
omit [DecidableEq V] [Fintype V] in
private lemma stoked_up (i : (L o).Index) (hp : Bid.pop (C.localSection (A.d o))) : GradeAt (degreeM A o) (Bulk.projected (fun t s=> stoked A o fee t s i)) := by
   let k:=degreeM A o; let l:=title (C:=C) i
   let Y : ℝ × X → X:= Prod.snd
   let B := ( (S o).places (Pi.single i 1) (o₁ o) ∘ represent (G:=G) (n:=C.side N p)) ∘ Y
   have hi: GradeAt l B:= GradeAt.coarse (primary i hp (o₁ o)) contDiffAt_snd rfl
   let P:ℂ→L[ℝ] ℂ:= fee o i • ContinuousLinearMap.id _ _
   have h:= GradeAt.linear_contact P hi
   have hl : l≤ k:=Finset.le_sup (f:=fun i:I o=> ((L o).grades i).2) (Finset.mem_univ _)
   exact show GradeAt k (Bulk.projected (fun t s=> stoked A o fee t s i)) from Nat.sub_add_cancel hl ▸ GradeAt.scale (GradeAt.shifts (Prod.fst: ℝ×X→ℝ) contDiffAt_fst rfl (k-l)) h
include hA
lemma fire_ready (hC : C.Makes) : Bulk.Well (flare R (fire A fee) (degreeM A)) := by
   refine flare_well _ _ _ ?_ (fun i t=> Envelope.compactC (((fire_cont A i fee)).comp (continuous_const.prodMk continuous_id))) ?_
   · intro i; exact GradeAt.list_sum (k:=degreeM A i) univ (fun j:I i=> Bulk.projected (fun t s=> stoked A i fee t s j)) (fun j _=> stoked_up A i fee j (hA i))
   -- gauge requires Makes (below)
   intro i t b x; unfold fire stoked; refine Finset.sum_congr rfl ?_; intro j _; rw [(S i).placed_invariant (hC.sections (A.d i)) (o₁ i) (Pi.single j 1) b]
end YM.Comparison.RG02.Bare.Signals
