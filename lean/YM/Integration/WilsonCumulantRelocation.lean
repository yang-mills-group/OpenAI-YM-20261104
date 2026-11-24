import YM.Integration.WilsonCumulantCommonOffset

/-! The full original connected relocation. Each replacement uses exactly
one signed insertion together with all the other arguments of its physical
moment; the disconnected factors stay on their original Wilson law. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCumulantRelocation
open Function Finset MeasureTheory Lattice Wilson RG Source Marker Multi Extraction
open Extra.Trajectories WilsonReportMomentDifference WilsonReportCashierConnected
open Primitives.GCC.Anchor Comparison.RG02.Cumulants WilsonCumulantCommonOffset
open scoped Classical BigOperators

def variation {ι A : Type*} [CommRing A] (f g change : ι → A) : List ι → A
  | [] => 0
  | i :: xs => change i * (xs.map f).prod + g i*variation f g change xs

theorem difference {ι A : Type*} [CommRing A] (f g : ι → A) (xs : List ι) :
    variation f g (fun i => f i-g i) xs = (xs.map f).prod-(xs.map g).prod := by
  induction xs with
  | nil => simp [variation]
  | cons i xs ih => simp only [variation,ih,List.map_cons,List.prod_cons]; ring

variable {G : Gauge} {C : Family G} {N p k : ℕ}

def movedMoment {V : Type} [DecidableEq V] (F E : V → Config G (C.side N p) → ℂ)
    (s : Finset V) : ℂ := moment (C.beta N p) (fun U =>
      variation (fun i => F i U) (fun i => E i U) (fun i => F i U-E i U) s.toList)

theorem one_block {V : Type} [DecidableEq V] (F E : V → Config G (C.side N p) → ℂ)
    (cf : ∀ i,Continuous (F i)) (ce : ∀ i,Continuous (E i)) (s : Finset V) :
    movedMoment F E s = moment (C.beta N p) (fun U => ∏ i ∈ s,F i U) -
      moment (C.beta N p) (fun U => ∏ i ∈ s,E i U) := by
  have hF : Continuous (fun U => ∏ i ∈ s,F i U) := continuous_finsetProd _ fun i _ => cf i
  have hE : Continuous (fun U => ∏ i ∈ s,E i U) := continuous_finsetProd _ fun i _ => ce i
  unfold movedMoment; simp only [difference,Finset.prod_map_toList]
  exact integral_sub (hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hE.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

def signed {V : Type} [Fintype V] [DecidableEq V] (Γ : Census V)
    (F E : V → Config G (C.side N p) → ℂ) (s : Γ.Mode) : ℂ :=
  ∑ t ∈ shards Γ s, mobiusTop t.val.card *
    variation (fun z : Multi.Hot Γ => (microscopic Γ C F).part z.val)
      (fun z : Multi.Hot Γ => (microscopic Γ C E).part z.val)
      (fun z : Multi.Hot Γ => movedMoment F E z.val.val) t.val.toList

theorem full {V : Type} [Fintype V] [DecidableEq V] (Γ : Census V)
    (F E : V → Config G (C.side N p) → ℂ) (cf : ∀ i,Continuous (F i)) (ce : ∀ i,Continuous (E i))
    (s : Γ.Mode) :
    (connected (microscopic Γ C F)).part s - (connected (microscopic Γ C E)).part s = signed Γ F E s := by
  let A := microscopic Γ C F; let B := microscopic Γ C E
  have start (Z : V → Config G (C.side N p) → ℂ) : (microscopic Γ C Z).part Γ.quiet = 1 := by
    change moment _ (fun U => ∏ i ∈ (∅ : Finset V), Z i U) = 1; simp [moment]
  change (connected A).part s - (connected B).part s = _
  rw [log_partition A (start _),log_partition B (start _),←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro t _
  have eq : (fun z : Multi.Hot Γ => movedMoment F E z.val.val) = (fun z : Multi.Hot Γ => A.part z.val - B.part z.val) :=
    funext fun z => one_block F E cf ce z.val.val
  rw [← mul_sub,eq,difference,Finset.prod_map_toList,Finset.prod_map_toList]

theorem original {n : ℕ} (Γ : Census (Fin n)) (hk : k ≤ N) (d : Fin n → ℕ) (v : (i:Fin n) → C.label (d i))
    (y : Fin n → Site (C.side N p)) (q : Site (C.side N p)) (s : Γ.Mode) :
    displaced Γ hk d v y s = signed Γ (fun i => C.O N p (v i) (y i-q))
      (fun i => C.O N p (v i) (anchored hk y i)) s := by
  rw [relative (C:=C) (N:=N) (p:=p) Γ hk d v y q]
  exact full Γ _ _ (fun i => C.continuousO ..) (fun i => C.continuousO ..) s

end YM.Integration.WilsonCumulantRelocation
