import YM.GradedFar.Books.Greige

/-!
# Prices on the *mixed* announcements
Compare the leading values only for this, but expose the exact physical arguments
in the later application. As in QScale, this and Beginning replace assuming the
input statement on actual operator K_m.
-/
namespace YM.FVA2.GradedFar.Books
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus XSpace.Rose
open O O.Score O.Enh O.Canon Scale Dframe Jury Facets Growth Pose Moving Matrix
open MS.Book.Program
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n d e : ℕ} {I J : Type} {p : ℕ} (T : Filter I) (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G
local notation "ν"=> Teller.logNu 1
open Reg.Point (stepV)
local notation "Tn"=> Toon G d
local notation "xρ"=>rootPoints
variable {simple : G.Simple} {A : Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
variable {F : Pose.Plans G d} {Z : Rolled G d}
local notation "T0"=> filed

/-- Hypothesis used here: each finite two-leg job gets the earlier
**mixed**-homes C5 on `[1,2]`, with t' equivalent to g at all its settings.
In `mix` on real BOTH compact hands (first at home-`rT`, second
home-`r`, geometry `rootPoints` in r UNITS). Sufficient to be able
to query these finite stocks. Use with u, v fixed. Spin & real
convention still on those labels. Expressing first field back at its
home uses `Level.Dial d (+log T)` -- that was kept in `mix`. Geometry
T here in physical units, i.e. stretch, r=s-order log notation in other
modules. In this hypothesis s variable=`snd i` is log T. Earlier stocks,
stencil inversions & UV comparisons not claimed; this is C5 at submission.
-/
def Offered (F : Pose.Plans G d) (Z : Rolled G d) (u v : Tn) :=
    ∃ (j k:ℕ) (X Y : DataPoint → Normalize.Change G d)
        (t' : DataPoint → ℝ), 2≤k ∧ k≤j ∧
      Tendsto (fun i:DataPoint=>guide G d (X i)) T0 (𝓝 0) ∧
      Tendsto (fun i:DataPoint=>guide G d (Y i)) T0 (𝓝 0) ∧
      Tendsto (fun i:DataPoint=> t' i / g i.1) T0 (𝓝 1) ∧
      Buys T0 (fun i:DataPoint=> mix F Z i.1 i.2.val v u - crop j (t' i)
          (Pose.line N xρ (arms (stand (X i) (theory u)) (stand (Y i) (Read.prism (theory v))))))
            (fun i=>g i.1) k

private lemma stand_near {A : I → Normalize.Change G d} (hx : Tendsto (fun i=> guide G d (A i)) T (𝓝 0)) (u : Sec G d) :
    Tendsto (fun i=> chair G d (stand (A i) u)) T (𝓝 (chair G d u)) := by
    let L : MoveSpace G d →ₗ[ℝ] RowSpace G d :=
      { toFun x:= chair G d (((guide G d).symm x).val u), map_add' x y:= by rw [map_add]; exact map_add (chair G d) _ _, map_smul' := by intro x y; rw [map_smul]; exact map_smul ((chair G d).restrictScalars ℝ) _ _ }
    have h:Tendsto (fun i=> L (guide G d (A i))) T (𝓝 0) := by
      have hu:= L.continuous_of_finiteDimensional.continuousAt.tendsto.comp hx; rw [map_zero] at hu; exact hu
    have hh x : chair G d (stand (A x) u)= chair G d u + L (guide G d (A x)) := by
      rw [stood,map_add]; simp [L]
    simp_rw [hh]; simpa only [add_zero] using! (tendsto_const_nhds (x:= chair G d u)).add h

include H
variable (sv : ∀ a b : Toon G d, Offered N F Z a b)
include sv
lemma mixed_purchase : Mixed F Z := by
    intro v u; obtain ⟨j,k,X,Y,t',hk,hj,h0,h1,ht,hv⟩:= sv u v
    let x i:= stand (X i) (theory u); let y i:= stand (Y i) (Read.prism (theory v)); let F' i:= Pose.line N xρ (arms (x i) (y i))
    let P:= fxt (Pose.Bbook N d) xρ
    have he a : Tendsto (fun i=> coeff a (F' i)) T0 (𝓝 (artist (P a) (theory u) (Read.prism (theory v)))) := by
        unfold F' Pose.line; simp_rw [coeff_mk]; exact artist_tends T0 _ _ _ _ _ (stand_near T0 h0 (theory u)) (stand_near T0 h1 (Read.prism (theory v)))
    have hr : Tendsto (Prod.fst : DataPoint → ℝ) T0 τ := tendsto_comap
    have hu : Tendsto (fun i:DataPoint=> (t' i:ℂ)) T0 (𝓝 0) := by
        have h:= ht.mul ((shrink simple).comp hr); rw [mul_zero] at h
        have ht : Tendsto t' T0 (𝓝 0) := h.congr' ((hr.eventually (positive_g simple)).mono fun i hi=> by dsimp; rw [div_mul_cancel₀ (t' i) hi.ne'] )
        have H := Complex.continuous_ofReal.continuousAt.tendsto.comp ht; rw [Complex.ofReal_zero] at H; exact H
    have hh:Tendsto (fun i=> crop j (t' i) (F' i)) T0 (𝓝 (Read.GramP G d v u)) := by
        have hm:= tendsto_finsetSum (Finset.range (j+1)) (fun i _=> (hu.pow i).mul (he i))
        simp only [crop_eq]
        -- rewrite sum on coeff
        have hx:(∑ a∈Finset.range (j+1), (0:ℂ)^a * artist (P a) (theory u) (Read.prism (theory v)))=Read.GramP G d v u:= by
           rw [Finset.sum_eq_single 0,pow_zero,one_mul]; · exact gram N M H u v
           · intro z hz he; simp [he]
           simp
        rw [hx] at hm; exact hm
    have hl:= ((collapses T0 N M (Prod.fst : DataPoint→ℝ) hr H hv (by omega)).add hh)
    rw [zero_add] at hl; apply hl.congr; intro i; exact sub_add_cancel _ (crop j (t' i) (F' i))

theorem aligned (θ : ℝ → ℝ) (h : Beginning N θ d F) (ht : ∀ᶠ r in τ,∀ z∈Growth.Small, permissible (forwards Z r z)) : Righted Z := by
    refine ⟨ht,?_⟩
    have hv : Mixed F Z := mixed_purchase N M H sv; have hw := paced N M H θ h hv; have he:= (hw.sub_const (1:Maps G d)); rw [sub_self] at he
    simp_rw [orient,chairs_mul] at he
    simpa only [engine,Zenith, neg_neg] using he
end
end YM.FVA2.GradedFar.Books

