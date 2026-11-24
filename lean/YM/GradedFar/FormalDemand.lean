import YM.WiderProfiles.Basket

/-!
# The homogeneous-input estimates used (before applying the scale columns)

(F.O), (F.1) in their Rain representation, on the original FVA2 book **after** its
adjustment; T=exp s. Also prove the resulting price on the full kernel (after (F.O) in the
paper). Keep the strong *no log cost* compact-x estimate for the OPE coefficients.
-/
namespace YM.FVA2.GradedFar
noncomputable section
open Set Filter Function Real PowerSeries
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Dframe
open scoped Topology BigOperators Classical

abbrev book {G : Gauge} (N : WilsonPrescription G) := Scale.Measure.outlook N.scheme N.criterion
abbrev ordinary {G : Gauge} (N : WilsonPrescription G) := install (book N)

section geometry
variable {n m : ℕ} {K : Set (Points n)} {S : Set (Points m)}

/-- Hereafter all the far arguments stay in the domains of the functions used. -/
theorem eventually_conf (hK : IsCompact K) (hx : K ⊆ conf n)
    (hS : IsCompact S) (hy : S ⊆ O.Enh.Outside m) :
    ∀ᶠ (s : ℝ) in atTop, (∀ x ∈ K, ∀ y ∈ S, forest x (squeeze (-s) y) ∈ conf (n+m)) ∧
      (∀ y ∈ S, outgoing (squeeze (-s) y) ∈ conf (1+m)) := by
  filter_upwards [O.Read.for_far hK hx hS hy] with s hs
  exact ⟨hs, fun y h => lives (-s) (hy h)⟩
end geometry

variable {G : Gauge} {n m : ℕ} {N : WilsonPrescription G} {simple : G.Simple}
  {T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
  {A : Prescription (Press.portDeck G)} (H : Main.Match N simple T A true)
  {K : Set (Points n)} {S : Set (Points m)}
include H

/-- By (F.O) of the supplied Match on the same book. `j` **inclusive**.
I.e. all `k<j+1` are uniform (in x,y) `Rain` with rate h+1+W. -/
lemma FO (u : Scan G n) (v : Scan G m) (hK : IsCompact K) (hx : K ⊆ conf n)
    (hS : IsCompact S) (hy : S ⊆ O.Enh.Outside m) (j h : ℕ) :
    ChargeP (j+1) ((h:ℝ)+1+(totalG v:ℝ))
      (fun (i : ↥K × ↥S) s => Basket (ordinary N) u v
        (FarCoefficients (book N) u i.1.val) h i.1.val (squeeze (-s) i.2.val)) :=
  (WiderProfiles.separate_predictor_inputs N simple T A H u v K S hK hx hS hy j h).1

/-- Compact-x tariff. -/
lemma compact_fare (u : Scan G n) (q : Q G) (hK : IsCompact K) (hx : K ⊆ conf n) (j : ℕ) :
    ∃ C : ℝ, ∀ x ∈ K, ‖coeff j (FarCoefficients (book N) u x q)‖ ≤ C :=
  hK.exists_bound_of_continuousOn
    ((((H.separatedOPE (Teller.logNu 1)).wilson.far u).2.1 q j).mono hx)

lemma constant_fare {I : Type} (u : Scan G n) (q : Q G) (hK : IsCompact K) (hx : K ⊆ conf n)
    (x : I → K) (j : ℕ) :
    ChargeP j 0 (fun (i : I) (_ : ℝ) => FarCoefficients (book N) u (x i).val q) := by
  intro k _
  obtain ⟨C,h⟩ := compact_fare H u q hK hx k
  exact Rain.cash ⟨C, fun i => h _ (x i).property⟩

/-- By (F.1) of same inputs. Price retained also for each output's own weight. -/
lemma F1 (q : Q G) (v : Scan G m) (hS : IsCompact S) (hy : S ⊆ O.Enh.Outside m) (j : ℕ) :
    ChargeP (j+1) ((heft q:ℝ)+(totalG v:ℝ))
      (fun (i : ↥S) s => lonelyG (ordinary N) (squeeze (-s) i.val) q v) := by
  let X : Set (Points 1) := {0}
  exact (WiderProfiles.separate_predictor_inputs N simple T A H (Single q) v X S
    isCompact_singleton (singleton_subset_iff.mpr (fun _ _ _ => Subsingleton.elim ..)) hS hy j 0).2.2 q

/-- Pay for a full homogeneous row (without OPE subtraction, retaining the
exterior grading), derived as after (F.O) in FormalDemand. -/
theorem full_fare (u : Scan G n) (v : Scan G m) (hK : IsCompact K) (hx : K ⊆ conf n)
    (hS : IsCompact S) (hy : S ⊆ O.Enh.Outside m) (j h : ℕ) :
    ChargeP (j+1) (totalG v:ℝ)
      (fun (i : ↥K × ↥S) s => party (ordinary N) i.1.val (squeeze (-s) i.2.val) u v) := by
  let B (i : ↥K × ↥S) (s : ℝ) := Basket (ordinary N) u v (FarCoefficients (book N) u i.1.val) h
    i.1.val (squeeze (-s) i.2.val)
  let L (i : ↥K × ↥S) (s : ℝ) := Lamp (ordinary N) h (squeeze (-s) i.2.val) v
    (FarCoefficients (book N) u i.1.val)
  have hB : ChargeP (j+1) (totalG v) B := (FO H u v hK hx hS hy j h).grow (by
    have : 0≤(h:ℝ) := by positivity
    linarith)
  have hq (q : Q G) : ChargeP (j+1) (totalG v)
        (fun (i : ↥K × ↥S) s => FarCoefficients (book N) u i.1.val q *
          lonelyG (ordinary N) (squeeze (-s) i.2.val) q v) := by
    refine (constant_fare H u q hK hx Prod.fst _).times ?_
    exact ((F1 H q v hS hy j).pull Prod.snd).grow (by
      have : 0 ≤ (heft q:ℝ) := by positivity
      linarith)
  have hL : ChargeP (j+1) (totalG v) L := ChargeP.sum _ fun i _ => ChargeP.sum _ fun a _ => hq _
  simpa only [B,Basket,L,sub_add_cancel] using ChargeP.plus hB hL
end
end YM.FVA2.GradedFar
