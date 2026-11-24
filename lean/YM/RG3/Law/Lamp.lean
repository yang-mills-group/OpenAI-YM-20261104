import YM.RG3.Law.Sample
import YM.MergeProof.Pitch

/-!
# One marked coefficient on its whole multi-source representation

Use the existing coefficient/density system for single insertions. Apply also
AFTER any new representation (Stamp etc). No partner omissions or alternate
scalar. Uncompacted multi address alternatives reclosed via sum in `forced`.
Export `summable` and pricing separately to permit these sums before building
`Coefficient`, even on active K payload. Roots fixed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Law
open RG Lattice Wilson Marker Overlay Function Finset Source MergeProof.Accent MeasureTheory RG3.Forms Push.AbsoluteSums
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V} (s : V) {G : Gauge} {n : Side} {P : Rep G n} (d : Deck R P)

def solution (i : ℕ) (U : Config G n) := ∑' j : ℕ, if d.contents.marks i j=R.fire s then d.contents.entries i j U else 0
/-- Capture only the matching singleton. On other regular labels one may pad
the support instead to keep the correct origin support as in Coefficient.
All costs at zero preserved. -/
def verses (i : ℕ) : Config G n → ℂ := if d.contents.rays i=R.fire s then d.contents.H i else 0
def snapshots (i : ℕ) (U : Config G n) := masked P.p.threshold (d.contents.support i) (verses s d i) U

def legend := d.contents.units s+(d.captions.chord).part (R.fire s)
def localRead U := legend s d+∑' i,snapshots s d i U

def casting {D : ℕ} {F : Labels.Frame G D} (T : SectionData F) (c : Coefficient F n) :=
    (∀ U, localRead s d U=c.exponentialEntry (d.contents.origins s) T P U) ∧
    c.forced = solution s d

omit [Fintype V] in
lemma marked_ray (U i) : (d.contents.ray i U).part (R.fire s)=snapshots s d i U := by
  by_cases h : d.contents.rays i=R.fire s
  · unfold Bands.ray snapshots verses; rw [Poly.part_send,h,if_pos rfl,if_pos rfl]
  unfold Bands.ray snapshots verses
  rw [Poly.part_send,if_neg (Ne.symm h),if_neg h]
  by_cases hx : Healthy P.p.threshold (d.contents.support i) U
  · rw [masked_eq _ _ _ _ hx]; rfl
  rw [masked_ne _ _ _ _ hx]

lemma logs {w u c d' b a} (h : d.Active) (he : d.Budget w u c d' b a) (U) :
    (d.log U).part (R.fire s)=localRead s d U := by
  unfold Deck.log Bands.extra
  rw [Poly.part_plus, Poly.part_plus, Poly.part_sum, Poly.share (d.contents.bulkBound h.articles he.radial U).1]
  simp only [Poly.part_send,Census.fire_inj,sum_ite_eq,mem_univ,↓reduceIte, marked_ray s d]
  unfold localRead legend; abel

lemma inked {w u c d' b a δ k} (h : d.Active) (he : d.Budget w u c d' b a) (hp : P.activities.Valid P.p δ k)
    (i U) :
    (d.contents.each i U).part R.quiet=(P.activities.K i U:ℂ) ∧
      (d.contents.each i U).part (R.fire s)=solution s d i U := by
  have hx j (y : ℂ) : (Poly.send (d.contents.marks i j) y).part R.quiet=0 := by rw [Poly.part_send]; exact if_neg fun hv => (h.articles.occurs i j).ne_empty (congrArg Subtype.val hv.symm)
  simp_rw [Bands.each, Poly.part_plus, Poly.share ((d.contents.baseBound h.articles he.radial hp U).1 i),Bands.tagged,
    hx, Poly.part_send,tsum_zero]
  constructor
  · simp
  rw [if_neg (R.fire_hot s),zero_add]; unfold solution; refine tsum_congr fun j => ?_; simp only [eq_comm (a:=R.fire s)]

lemma plate {w u c d' b a D δ k} {F : Labels.Frame G D} (q : Coefficient F n) (hQ:q.forced=solution s d)
    (h : d.Active) (he : d.Budget w u c d' b a) (hp : P.activities.Valid P.p δ k) (U i) :
    (d.contents.packet i U).part R.quiet=(P.activities.gasOccurrence P.p i U:ℂ) ∧ (d.contents.packet i U).part (R.fire s)=q.marked P i U := by
  classical
  unfold Bands.packet Activities.gasOccurrence Coefficient.marked
  split_ifs with h'
  · have hv j := inked s d h he hp j U
    rw [shockProd₀,Complex.ofReal_prod, shockProd]; constructor
    · exact prod_congr rfl fun i _ => (hv _).1
    rw [hQ]
    refine sum_congr rfl (fun i hc => congrArg₂ HMul.hMul (hv i).2 (prod_congr ?_ (fun i _ => (hv _).1)))
    congr; exact Subsingleton.elim _ _
  simp

lemma candle {w u c d' b a D δ k} {F : Labels.Frame G D} (q : Coefficient F n) (T : SectionData F) (hQ : casting s d T q)
    (h : d.Active) (he : d.Budget w u c d' b a) (hp : P.activities.Valid P.p δ k) :
    q.density (d.contents.origins s) T P = fun U => (d.density U).part (R.fire s) := by
  funext U
  have hg := (d.contents.population h.articles he.radial hp U).1
  unfold Coefficient.density Deck.density Bands.cluster
  have hi := plate s d q hQ.2 h he hp U
  rw [Poly.part_smul,shock,Poly.share hg,Poly.share hg,Poly.pass_part _ (d.quiet h he _),whisper _ _ (d.quiet h he _) s,logs s d h he,one_mul]
  simp_rw [(hi _).1,(hi _).2,hQ.1 U]
  rw [← Complex.ofReal_tsum, Rep.eval,Complex.ofReal_mul, mul_add]
  unfold Activities.gas; ring
end YM.RG3.Law
