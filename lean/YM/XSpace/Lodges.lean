import YM.XSpace.KeyReads
import YM.XSpace.Regulated

/-!
# Wick-renormalized leading position kernels on every finite cutoff

Pre-conditions. `Rate`-free (other file checks numerical stability). Compute
at specific x from `Initialize` choices. Use `YM.Next.Rank` Wick calculus,
alphabet ALL keys, discarding no image terms, reading numerator & vacuum.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Price
open Lattice Filter Function Set Top Labels Source Source.Drops
open Contraction Next.Rank Next.Rank.Normal Beamer Finsupp MvPolynomial
open scoped Topology BigOperators
variable {G : Gauge} {n : ℕ} (p : Mesh) (A : Initialize G)

local notation "T" => A.tree p.p
variable (d : Fin n → ℕ)

abbrev Tag (G : Gauge) (n : ℕ) := Fin n × Key G
def Z (p : Mesh):ℂ := (p.spacing:ℂ)⁻¹
def promote (i : Key G) : Key G→₀ℂ:= single i (Z p ^ generation i)
def stamps := scope (perSlot (fun _ : Fin n=> promote (G:=G) p))
lemma stamped (V : Cov (Tag G n)) (i j : Tag G n): (stamps p V).cov i j= ((Z p)^(generation i.2+generation j.2)) * V.cov i j:=by
   dsimp only [stamps,scope,perSlot]; rw [promote,promote,mapDomain_single,mapDomain_single,treats_single,pow_add,mul_comm (Z p ^ generation j.2)]

private lemma on_monomial (b : Key G→₀ℕ) (c : ℂ) : exchange (promote p) (monomial b c)=(Z p ^ (Finsupp.weight generation b)) • monomial b c:= by
  classical
  apply Extra.FD.per_factor b
  · change exchange _ (C c) = _; rw [exchange_c,map_zero,pow_zero,one_smul]; rfl
  intro a i hi; rw [monomial_add_single,pow_one,map_mul,hi,exchange_x,promote,glyph,linearCombination_single,map_add,weight_single,pow_add]; rw [smul_mul_smul]; simp
lemma promote_grade {m : ℕ} (L : Labels.Pol G) (h : IsWeightedHomogeneous generation L m):
    exchange (promote p) L= (Z p ^ m) • L :=by
  classical
  rw [L.as_sum,map_sum, Finset.smul_sum]; apply Finset.sum_congr rfl; intro k hk; rw [on_monomial,h (MvPolynomial.mem_support_iff.mp hk)]

def roots (x : Fin n→ Cover) : Fin n → Key G → (A.tree p.p).Key G→₀ℂ:=fun i k=> Cross.ask (A.surveys (d i)) T (x i) k

def home (i : Fin n):= (A.surveys (d i)).selfCov 1

def season (x : Fin n → Cover) : Cov (Tag G n):= stamps p (scope (fun z : Tag G n=> roots p A d x z.1 z.2) (Bare.Q T G) + -(Normal.self (home A d)))
private def pin {d : ℕ} (x : On.Grade G d) : Maxwell.shellSector G d := Submodule.inclusion (show On.Grade G d ≤ Maxwell.shellSector G d from inf_le_left) x
def preparedL {d : ℕ} (x : On.Grade G d) : Labels.Label G d:= On.sectionMap d (pin x)
lemma preparedV {d : ℕ} (x : On.Grade G d): (preparedL x).val=On.lifting x.val:=On.section_value _
lemma natural {d : ℕ} (x : On.Grade G d): IsWeightedHomogeneous generation (preparedL x).val d:= by
  have hp:IsWeightedHomogeneous Maxwell.Free.scaleW x.val d:= x.property.2
  rw [preparedV]; have he:= Maxwell.Free.commuting Maxwell.Free.scaleW generation On.lifting (On.grade (m:=fun i=> i+2)) x.val d; rw [hp.weightedHomogeneousComponent_same] at he; rw [← he]; exact weightedHomogeneousComponent_mem ..

def output (v : ∀ i, On.Grade G (d i)) := Normal.pot Finset.univ (fun i=> (preparedL (v i)).val)
lemma pot_calc (v : ∀ i, On.Grade G (d i)) : exchange (perSlot fun _ : Fin n => promote (G:=G) p) (output d v)=Normal.pot Finset.univ (fun i=> (Z p ^ d i) • (preparedL (v i)).val) := by
  unfold output pot; rw [map_prod]; exact Finset.prod_congr rfl fun i _=> (posts ..).trans (by rw [promote_grade _ _ (natural (v i))])
lemma settle (x : Fin n→Cover) (v : ∀ i, On.Grade G (d i)) : PowerSeries.constantCoeff (A.atTuple p d (wrap p.p.side ∘ x) v)=blend (season p A d x) 0 (output d v) := by
  let f i:= (Z p ^ d i) • (preparedL (v i)).val; let R i:= home A d i; let a:= roots p A d x
  have ht (i) : PowerSeries.constantCoeff (A.atSite p (d i) (wrap p.p.side (x i)) (v i))= exchange (a i) (milk (-(R i)) (f i)):=by
    unfold f
    rw [Initialize.atSite, LinearMap.smul_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_smul, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_smul,map_smul]
    unfold Z; rw [inv_pow]; exact congr_arg ((↑p.spacing^d i:ℂ)⁻¹ • ·) (Cross.wicks (A.surveys (d i)) T (preparedL (v i)) _)
  have he {V Z : Type} (m:V→Z→₀ℂ) : reads m 0=0:= funext fun i=> linearCombination_zero_apply ..
  rw [A.atTuple_eq,Bare.leading,map_prod]; simp_rw [Function.comp_apply, ht,lodge a R (Bare.Q T G) 0 f]; rw [he,show Normal.pot Finset.univ f=_ from (pot_calc p d v).symm,wets,he]; rfl

open Cross (readKey sleeps reads_position lag extra)
lemma pair_position (x : Fin n→Cover) (i j : Fin n) (a b : Key G):
    (season p A d x).cov (i,a) (j,b)=
      ↑(p.spacing⁻¹^(generation a + generation b)*(mourn (readKey (A.surveys (d i)) a) (readKey (A.surveys (d j)) b) (lag p.p (x i) (x j)+extra p.p (x i) (x j)) -
       if i=j then mourn (readKey (A.surveys (d i)) a) (readKey (A.surveys (d j)) b) Cross.self else 0)):= by
  rw [season, stamped]; simp only [scope,show ∀ v t:Cov (Tag G n),(v+t).cov=v.cov+t.cov from fun _ _=>rfl, show ∀ q:Cov (Tag G n), (-q).cov= -q.cov from fun _=> rfl, Pi.add_apply,Pi.neg_apply,roots]
  rw [Cross.reads_position]; simp only [Normal.self,home]; split_ifs with h
  · subst j; rw [sleeps]; simp [Z,sub_eq_add_neg]
  simp [Z]
end YM.XSpace.Price
