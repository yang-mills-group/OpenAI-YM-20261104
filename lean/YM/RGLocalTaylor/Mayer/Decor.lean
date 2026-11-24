import YM.RGLocalTaylor.Engine.Paid
import YM.RGLocalTaylor.Mayer.Lift

/-!
# Keep *all* reuses of a log coefficient BEFORE forming the integrated moment

Keep terms through a total positive interaction order across all the analytic
vertices. Can fix some of the vertices in a tuple (to accommodate joint-source
costing or other conventions); all actual uses of survivor-numerics must be at
the same moment on these selected original logarithmic heads. `code=last` is
not treated as a perturbative contribution. Error itself even at this level is
a **function** ready to be estimated on the original support, with all links.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F F' : Forest S.ratio} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {X : Coat T F} {η r q a Y W d C' A b s μ C v B : ℝ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R}

open Blaze.March PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt
namespace Mayer

/-- Use each of the different **analytic** entries in an integrated tuple.
`select` says which of the log letters contribute to Taylor order; don't select
the marked additional f insertion. -/
def original (H : Cash W s μ L Q o C T R) (p select : Molecule S) (f : Head S → Insert T) : Insert T :=
  Insert.joined p (fun x => if x ∈ select then leg H (own p) x else f x)

abbrev Decors (select : Molecule S) (M : ℕ) := (i : ↥select) → Fin (M+1)

variable {M : ℕ} {p z : Molecule S} (H : Cash W s μ L Q o C T R)
    (f' : Head S → Insert T)

def decorOrder (u : Decors z M) : ℕ:= ∑ i:↥z, ((u i).val+1)

lemma decorOrder_lt {g : Decors z M} (h : decorOrder g ≤ M) (i:↥z) : (g i).val < M :=
  (Finset.single_le_sum (f:=fun k:↥z=> (g k).val+1) (fun _ _=> Nat.zero_le _) (mem_univ i)).trans h

/-- All inputs retain the original footprint; will underlie the pointwise
formulas as well as weighted norms. -/
def payload (H : Cash W s μ L Q o C T R) (p : Molecule S) (f' : Head S → Insert T)
    (g : Decors z M) (x : Head S) : Insert T := if h : x∈z then
  kernelQuote H (own p) (g ⟨x,h⟩) x else f' x

def tagged (H : Cash W s μ L Q o C T R) (p : Molecule S) (f' : Head S → Insert T) (g : Decors z M) : Insert T :=
  Insert.joined p (payload H p f' g)

lemma dad (H : Cash W s μ L Q o C T R) (p : Molecule S) : original H p p f' = native H p := by
  change Insert.mk _ = Insert.mk _; congr! 1; funext F X z
  exact prod_congr rfl fun i hi=> by simp only [if_pos hi]

variable (hz : z⊆p)
include hz
lemma values_at (M : ℕ) (w : Air f G) (X : Coat T F) :
    (∑ u : Decors z M, (tagged H p f' u).value X w) = (original H p z f').value X w := by
  let a i := (f' i).value X w; let b i:= (leg H (own p) i).value X w
  let Z := ∏ i∈p \ z,a i
  let g (u : Decors z M) i:= (payload H p f' u i).value X w
  have he' (u:Decors z M) : (tagged H p f' u).value X w = Z*∏ i:↥z, indexValue (u i) (b i.val):= by
    change ∏ i∈p,g (u:Decors z M) i = _
    rw [← prod_sdiff hz]; refine congr_arg₂ (·*·) (prod_congr rfl ?_) ?_
    · intro i hi; unfold g payload; rw [dif_neg (mem_sdiff.mp hi).2]
    rw [← prod_attach z]; exact prod_congr rfl fun i _=> by unfold g payload; rw [dif_pos i.property]; rfl
  let r (u:Head S):= if u∈z then leg H (own p) u else f' u
  simp_rw [he']; rw [← mul_sum]
  change _=∏i∈p,(r i).value X w
  rw [← prod_sdiff hz, ← Fintype.prod_sum (f:=fun i:↥z => fun j:Fin (M+1) => indexValue j (b i.val))]; simp_rw [index_identity]
  apply congr_arg₂ (·*·); · refine Finset.prod_congr rfl fun i hi=> ?_; unfold r; rw [if_neg ((mem_sdiff.mp hi).2)]
  rw [← prod_attach z]; exact prod_congr rfl fun i _=> by unfold r; rw [if_pos i.property]

lemma restore (M : ℕ) :
    Insert.together univ (tagged H p f' : Decors z M → Insert T)=original H p z f' := by
  change Insert.mk _ = Insert.mk _; congr! 1; funext F X w; exact values_at H f' hz M w X

omit hz
variable (hf : ∀ i∈ p \ z,Fits H (f' i) (H.supportP i) j)
include hf
lemma fits_tagged (u : Decors z M) : Fits H (tagged H p f' u) (H.unionP p) j := by
  apply Fits.joined
  intro i hi; apply Fits.bigger (u:=H.supportP i) _ (subset_biUnion_of_mem H.supportP hi)
  unfold payload; split; exact quote_fits ..; next h=> exact hf _ (mem_sdiff.mpr ⟨hi,h⟩)

-- On healthy configurations read genuine joint budgets. `M` appearing in the
-- low slots only as a horizon; this recipe at order d uses NO derivative of
-- the actual pushed answer. Last global remainder defined separately.
variable (p z) in
/-- Aggregate at precisely the indicated Taylor order in one molecule. -/
def coefficient (χ:Chi) (M d : ℕ) (V : Config G c) := ∑ g∈ univ.filter (fun g:Decors z M => decorOrder g=d),
    (tagged H p f' g).onLog H χ p V

variable (p z) in
def retained (χ:Chi) (M : ℕ) (V : Config G c) := ∑ g∈ univ.filter (fun g:Decors z M => decorOrder g≤M),
    (tagged H p f' g).onLog H χ p V
omit hf
lemma retained_eq (p z) (M : ℕ) (V : Config G c) : retained p z H f' χ M V=∑ d: Fin (M+1), coefficient p z H f' χ M d V:= by
  unfold retained coefficient; simp_rw [sum_filter]; rw [sum_comm]; refine sum_congr rfl ?_
  intro g _; by_cases hp : decorOrder g ≤ M
  swap; · rw [if_neg hp]; symm; refine sum_eq_zero (fun i _=>?_); apply if_neg; intro hx; exact hp (hx ▸ Nat.le_of_lt_succ i.isLt)
  let i : Fin (M+1):=⟨_,Nat.lt_succ_of_le hp⟩; rw [if_pos hp, sum_eq_single i]; · rw [if_pos rfl]
  · intro j _ h; exact if_neg (fun p=> h (Fin.ext p.symm))
  simp

include hf hz
variable {H f'}
lemma decor_near (M : ℕ) (N : Captain H j C' d v Y A b r B q n χ)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (he : (roster p).flags=∅) {x:E} {V : E → Config G c} (hV : Mode V x j v)
    (hy : Healthy (Pressure.temp s) (H.unionP p) (V x)) :
    (fun y=> (original H p z f').onLog H χ p (V y) - retained p z H f' χ M (V y)) =ᶠ[𝓝 x]
      fun y=>∑ u∈univ.filter (fun g:Decors z M=> ¬decorOrder g ≤ M), (tagged H p f' u).onLog H χ p (V y) := by
  have hv i := fits_tagged (M:=M) H f' hf i
  filter_upwards [(Fits.sum_onLog (Ξ:=N) (w:=univ) he (fun i _=> hv i) hV hy)] with y hh
  rw [restore H f' hz M] at hh
  rw [hh,sub_eq_iff_eq_add]; unfold retained; rw [add_comm (∑ u ∈ _, (_:ℝ)),Finset.sum_filter_add_sum_filter_not]
end Mayer
end YM.RGLocalTaylor
