import YM.XSpace.WickOperator
import YM.XSpace.ContactPrice

/-!
# Key-indexed columns of the lattice operator covariances

Retain overcapacity coordinates (they vanish). Work with pure on-shell columns
lifted to keys then full-address beans. Keep `frameX` conversion separate. This
file reconciles **all** pairings with the Hessian inverse used inside Bare.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Cross
open Lattice Filter Function Set Top Labels Source Source.Drops Wilson
open Next.Rank.Normal Next.Rank Beamer Contraction Finsupp MvPolynomial
open scoped Topology BigOperators
variable {G : Gauge} {d e : ℕ} {H K : Hol G} (A : Survey G H d)

def address (i : Bean A): Next.Rank.Beamer.Address G:= ((A.looks i.1).offset,(A.looks i.1).plaq,i.2)

def readKey (i : Key G) := looks A (Survey.component i)
lemma price_print (i : Key G) (f : Next.Rank.Beamer.Horizon G) : readKey A i f=∑ p:Bean A,bills A (Survey.component i) p*f (address A p):=by rw [readKey,looks,LinearMap.sum_apply]; rfl
lemma startsKey (i : Key G) (h : generation i ≤ d): Starts i.1 (readKey A i):=usable A i h
lemma on_shell (i : Key G) (h : generation i ≤ d): actsOn i.1 (readKey A i)=Prayer.scans i:=by
  ext1 q; exact end_cost A i h (Maxwell.gaugeJet q)
lemma unused (i : Key G) (h : d < generation i) : readKey A i=0:= by
  unfold readKey; ext1 f; rw [uses,Survey.component_point,expand,dif_neg (by unfold generation at h; omega), map_zero]; rfl

variable (B : Survey G K e)
lemma contracted (i j : Key G) (f : Bridge G): mourn (readKey A i) (readKey B j) f= ∑ u : Bean A, ∑ v : Bean B, bills A (Survey.component i) u * bills B (Survey.component j) v * f (address A u) (address B v):= by
  rw [show mourn _ _ f=readKey A i _ from rfl, price_print]; refine Finset.sum_congr rfl fun u _=>?_; rw [price_print, Finset.mul_sum]; refine Finset.sum_congr rfl fun v _=> ?_; rw [mul_assoc]

lemma sleeps (i j : Key G): (A.selfCov 1).cov i j = ↑(mourn (readKey A i) (readKey A j) Cross.self):=by
  rw [contracted]; simp only [Survey.selfCov, one_mul]; rfl

variable {R : Period} (T : R.Tree)
def j_at (x : Cover) (p : Bean A): Bare.At R G:= (faceOf R (x+(A.looks p.1).offset) (A.looks p.1).plaq,p.2)
lemma sees (x : Cover) (p : Bean A): (j_at (R:=R) A x p).1=Work.F03.slotFace (A.looks p.1) (wrap R.side x):=by simp [j_at,faceOf,Work.F03.slotFace,add_comm]
def ask (x : Cover) (k : Key G): T.Key G →₀ ℂ:=∑ i:Bean A,(bills A (Survey.component k) i:ℂ) • Bare.faceAppeal T (j_at A x i)
lemma evaluated (x : Cover) (k : Key G) (v : T.Field G): Taylor.evalAt (T.basis G) v (glyph (ask A T x k))= PowerSeries.constantCoeff (PowerSeries.map (Taylor.evalAt (T.basis G) v).toRingHom (Bare.factor T A (wrap R.side x) k)):=by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply]; change _ = Taylor.evalAt _ v _; rw [Bare.factor_leading,ask,map_sum,map_sum]
  let z:GaugePanel G A.size:= fun j=> T.linearCurl v (Work.F03.slotFace (A.looks j) (wrap R.side x))
  rw [Work.G05.snapCoord_eq, ← show ∀ x, (↑(Survey.component (G:=G) (d:=d) k x):ℂ) = coord (expand d x) k from fun _=> rfl]
  conv_rhs=> change ((↑(Survey.component k (A.extract z)):ℂ)); rw [← bean_reconstruct A z,map_sum,map_sum];
  push_cast; refine Finset.sum_congr rfl fun p _=> ?_; rw [map_smul,map_smul,Bare.measures_face,map_smul,map_smul, sees,smul_eq_mul, smul_eq_mul, Complex.ofReal_mul,mul_comm]; rfl
lemma milk_raw (x : Cover) (p : Labels.Pol G): PowerSeries.constantCoeff (Bare.raw T A (wrap R.side x) p)=exchange (ask A T x) p:=by
  unfold Bare.raw; induction p using MvPolynomial.induction_on with
  | C a=> rw [aeval_C,exchange_c,PowerSeries.algebraMap_apply]; simp [MvPolynomial.algebraMap_eq]
  | add p q hp hq=>rw [map_add,map_add,hp,hq,map_add]
  | mul_X p i hp=>
    rw [map_mul,map_mul,hp,map_mul,aeval_X,exchange_x]; congr 1
    apply Taylor.from_real (T.basis G); intro v; rw [evaluated,← PowerSeries.coeff_zero_eq_constantCoeff_apply,← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]; rfl
lemma wicks (p : Label G d) (x : Cover):
    PowerSeries.constantCoeff (Bare.column T A (wrap R.side x) p)= Normal.exchange (ask A T x) (milk (-(A.selfCov 1)) p.val):=by rw [Bare.column_formula,milk_raw,Survey.insertW_val,A.inverseCov]

private lemma scaled_treat {V :Type*} (M : Cov V) (x y: V→₀ℂ) (c d:ℂ): treats M (c • x) (d • y)= c*d*treats M x y:= by 
  have h (z) (x y : V→₀ℂ) : treats M x (z • y) = z • treats M x y:= map_smul (Finsupp.linearCombination ℂ _) z y
  rw [h,treats_comm,h,treats_comm]; simp only [smul_eq_mul]; ring
lemma reads_position (i j : Key G) (x y : Cover): treats (Bare.Q T G) (ask A T x i) (ask B T y j)=
    ↑(mourn (readKey A i) (readKey B j) (lag R x y + extra R x y)):= by
  unfold ask; rw [treats_sum,contracted,Complex.ofReal_sum]; refine Finset.sum_congr rfl fun u _=> ?_; rw [treats_comm,treats_sum,Complex.ofReal_sum]; refine Finset.sum_congr rfl fun v _=> ?_; rw [treats_comm,scaled_treat,Bare.orbit_pairs]; simp only [Pi.add_apply]; push_cast; rfl
end YM.XSpace.Cross
