import YM.MSbar.TreeOPE.Join

/-!
# OPE output in physical leading MS labels

Position tested at radius-one shape, all grades. Homogeneous supports.
Construct independent of output truncation, and normal tensors are
color invariant (proof uses orthogonal color rotations, not only
connected adjoint subgroup). No need spectral basis choices via OPE
conditions, but prepare for those later. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.OPE
open Function Set Filter Asymptotics Analysis
open Maxwell Maxwell.Free Maxwell.Wick Finsupp Next.Rank.Normal
open scoped ContDiff Topology BigOperators Classical
variable {G : Gauge} {H m n : ℕ} {x : Points n}

def delivery (x : Points n) (r : ℂ) (h : ℕ) (i : Mark G n): Slot G→₀ℂ:= series h (x i.1) r i.2
def send (x : Points n) (m : ℕ) (r : ℂ): poly (Mark G n)→ₐ[ℂ] WickPol G:= Next.Rank.Normal.exchange (delivery x r m)
lemma sends_x (x : Points n) (m : ℕ) (r : ℂ) (i: Mark G n) : send x m r (MvPolynomial.X i)=glyph (series m (x i.1) r i.2):= exchange_x ..
lemma lowered (v : ℂ) (p : poly (Mark G n)) : scale scaleW v (send x m 1 p)=send x m v p:= by
  apply DFunLike.congr_fun (f:=(scale scaleW v).comp (send x m 1)) (g:=send x m v) (x:=p)
  ext1 i; rw [AlgHom.comp_apply,sends_x,sends_x,series,series,map_sum,map_sum,map_sum];
  exact Finset.sum_congr rfl fun i _=> (stanza_resc ..).symm
lemma holding (p : poly (Mark G n)) : through scaleW m (send x m 1 p) (send x (m+1) 1 p):= through_eval _ _ _ (fun i=> by rw [sends_x,sends_x]; exact progress_add m i.2) p

lemma send_slot (r : ℂ) (m : ℕ) (i : Fin n) : (send x m r).comp (post i : poly (Slot G) →ₐ[ℂ] poly (Mark G n))=Next.Rank.Normal.exchange (series (G:=G) m (x i) r):= by
  ext1 v; rw [AlgHom.comp_apply,post_X, sends_x, exchange_x]

def turnS (g : G.El) (n : ℕ): poly (Mark G n) →ₐ[ℂ] poly (Mark G n):= Next.Rank.Normal.exchange (perSlot (fun _=>rows g))
lemma pigment_slot (g : G.El) (i : Fin n) (p : WickPol G) : turnS g n (post i p) = post i (pigment g p):= by
  rw [rows_expr g]; exact posts (fun _=> rows g) i p
lemma composed (g : G.El) (p : poly (Mark G n)) : send x m 1 (turnS g n p)=pigment g (send x m 1 p):= by
  apply DFunLike.congr_fun (f:= (send x m 1).comp (turnS g n)) (g:= (pigment g).comp (send x m 1)) (x:=p)
  ext1 i; rw [show MvPolynomial.X i=_ from (post_X i.1 i.2).symm]
  have ht (p : WickPol G): send x m 1 (post i.1 p)=Next.Rank.Normal.exchange (series m (x i.1) 1) p:= DFunLike.congr_fun (send_slot (x:=x) (G:=G) 1 m i.1) p
  rw [AlgHom.comp_apply,AlgHom.comp_apply,pigment_slot,ht,ht]; exact DFunLike.congr_fun (rotate_transport 1 (x i.1) g (m:=m)).symm (MvPolynomial.X i.2)
lemma filtered (h : m≤H) (p : poly (Mark G n)) : tier scaleW m (send x H 1 p) =tier scaleW m (send x m 1 p):= by
  induction H,h using Nat.le_induction with
  | base=> rfl
  | succ k h ih=> rw [← holding (x:=x) p m h,ih]
lemma sector_pigment {p : WickPol G} (h : ∀ g,pigment g p=p): ∀ m, tier scaleW m p∈ shellSector G m:= by
  intro m; apply sector.2; constructor
  · rw [Free.lowerCap,MvPolynomial.mem_restrictSupport_iff]; intro i hi
    exact (show weight scaleW i=m from MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous m p (MvPolynomial.mem_support_iff.mp hi)).le
  intro u; rw [← commuting scaleW scaleW (pigment u) (fun i=>?_) p m, h];
  rw [pigment, MvPolynomial.aeval_X]; exact symbol_hom _ (fun i => i+2)

def tube (hx : x∈conf n) (p : Fin n→WickPol G) := milk (frameX hx) (pot Finset.univ p)
def glued (hx : x∈conf n) (p : Fin n → WickPol G) (m : ℕ) := tier scaleW m (send x m 1 (tube hx p))
lemma glued_grade (hx : x∈conf n) (p : Fin n → WickPol G) (m : ℕ): pureW scaleW m (glued hx p m) := MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous _ _
lemma tube_cov (g : G.El) {p : Fin n → WickPol G} (h : ∀ i,pigment g (p i)=p i) (hx : x∈conf n): turnS g n (tube hx p) = tube hx p:= by
  have he : pot Finset.univ p=turnS g n (pot Finset.univ p):= by unfold pot; rw [map_prod]; exact Finset.prod_congr rfl fun i _=> by rw [pigment_slot,h]
  unfold tube; nth_rw 2 [he];
  rw [turnS,prepared,pigment_frame g]
lemma glued_physical {p : Fin n → WickPol G} (h : ∀ (g : G.El) i,pigment g (p i)=p i) (hx : x∈conf n) (m : ℕ): glued hx p m ∈ shellSector G m := sector_pigment (fun g=> (composed (m:=m) (x:=x) g (tube hx p)).symm.trans (by rw [tube_cov g (h g) hx])) m
lemma gave (r : ℂ) (p : Fin n→ WickPol G) (h : x∈conf n) (L : WickPol G →ₗ[ℂ] ℂ) (m : ℕ):
    L (approximant scaleW (send x m 1 (tube h p)) r m) = ∑ i ∈ Finset.range (m+1), r^i * L (glued h p i):= by
  rw [approximant,map_sum]; simp only [map_smul,smul_eq_mul]; apply Finset.sum_congr rfl; intro i hi; rw [filtered (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]; rfl
end YM.MSbar.OPE
