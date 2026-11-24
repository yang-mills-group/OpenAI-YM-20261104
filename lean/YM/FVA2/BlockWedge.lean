import YM.FVA2.RankLevel
import YM.FVA2.Dark
/-!
# Emit the full oriented Berezin determinant on the based generator

Action sign is **plus** c·bar. Entries in `Price` (may carry bosonic fields! This is not
 Wick expectation yet). To avoid analytic claims re Grassmann elements, use that these
 particular blocks have exterior alternating product directly in the MS `Raw` algebra. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Paper
open Filter
open MS MS.Koszul MS.Plane MS.Swirl MS.Orbit MS.Orbit.Cog MS.Orbit.LogReal MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Engine MS.Puff.SplitP MS.Puff.Actors MS.Puff.Mom MS.Cylinder MS.Cylinder.Taylor MS.Cylinder.Lab MS.Theater Finset PowerSeries PairCoords
open scoped Topology Classical ContDiff
variable {U J:Type}
local notation "p"=>φ (U:=U) (J:=J)
abbrev peer (j i:J) : Dark (φ (U:=U) (J:=J)):= ⟨ PairCoords.block U j i,( speaks_p («p»:=φ) (PairCoords.c i)).prod (speaks_p (bar j))⟩

section commute
abbrev rowPair (j i:J) : Price (φ (U:=U) (J:=J)):= C (peer j i)
local notation "B" => rowPair (U:=U)
local infixl:70 " ● " => product p
lemma crossHop(j i:Slot U J)(hx:p j=true)(hv:p i=true): atLetter j ● atLetter i= - (atLetter i ● atLetter j (R:=ℂ)):= by
   have ht:= (speaks_p (R:=ℂ) («p»:=p) j).times_comm (speaks_p («p»:=p) i); rwa [hx,hv,cross_true,neg_one_smul] at ht
-- exterior determinant alternating across both kinds

lemma slot_alt (i j k v:J): B i k * B j v = - ( B i v * B j k ):= by
   rw [rowPair,rowPair,rowPair,rowPair,← map_mul,← map_mul, ← map_neg]
   apply congr_arg C; apply Subtype.ext
   let x:=atLetter (PairCoords.c k) (R:=ℂ) (A:=Slot U J); let y:=atLetter (PairCoords.c v) (R:=ℂ) (A:=Slot U J); let a:=atLetter (bar i) (R:=ℂ) (A:=Slot U J); let b:=atLetter (bar j) (R:=ℂ) (A:=Slot U J)
   change (x ● a) ● (y ● b) = -( (y ● a) ● (x ● b))
   have hu : a ● x=-(x ● a):= crossHop _ _ rfl rfl
   have hU : a ● y=-(y ● a):= crossHop _ _ rfl rfl
   have hc : x ● y=-(y ● x):= crossHop _ _ rfl rfl
   rw [times_assoc, times_assoc y a, ← times_assoc a, ← times_assoc a, hu, hU];
   simp only [map_neg,LinearMap.neg_apply,neg_neg]; rw [times_assoc y a, times_assoc x a, ← times_assoc x y, ← times_assoc y x]
   rw [hc]; simp

private lemma eq_zero_of_eq_neg {v:Price p}(h:v=-v):v=0:= by have he:(2:ℂ) • v=0:= Eq.trans (two_smul ℂ v) (eq_neg_iff_add_eq_zero.mp h); exact (smul_eq_zero.mp he).resolve_left (by norm_num)
lemma bar_alt (i k v:J): B i k* B i v=0:= by
   have hv:=slot_alt (U:=U) i i k v; rw [mul_comm _ (B i k)] at hv; exact eq_zero_of_eq_neg hv
lemma diag_alt (i j k:J): B i k * B j k=0:= eq_zero_of_eq_neg (slot_alt i j k k)
end commute
variable [Fintype J]

def turnP (j:J) (U:Type) (a:J→Price (PairCoords.φ (U:=U) (J:=J))) : Price (PairCoords.φ (U:=U) (J:=J)):= ∑ i:J,rowPair (U:=U) j i * a i
local notation "q"=>Price p
local notation "B"=>rowPair (U:=U)
lemma turn_alt (j i:J) (a:J→ q): turnP j U a * turnP i U a = 0 := by
  let T (j i:J):=turnP j U a * turnP i U a; suffices ht:T j i = -T j i from eq_zero_of_eq_neg ht
  unfold T turnP; simp_rw [Finset.mul_sum,Finset.sum_mul,← Finset.sum_neg_distrib]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun x _=> Finset.sum_congr rfl fun y _=>?_ ; -- sums cross
  rw [mul_mul_mul_comm, mul_mul_mul_comm (B j y), mul_comm (a y), slot_alt j i x y, neg_mul]
lemma pair_turn (i:J) (a b:J→q) : turnP i U (a+b)=turnP i U a+ turnP i U b:= by unfold turnP; simp_rw [Pi.add_apply,mul_add, Finset.sum_add_distrib]
lemma pair_pay (i:J)(a:J→q)(x:q): turnP i U (x • a)= x* turnP i U a:= by unfold turnP; simp_rw [Pi.smul_apply,smul_eq_mul,mul_left_comm _ x, Finset.mul_sum]
lemma turn_zero (i:J): turnP i U 0=0:= by simp [turnP]
lemma turn_same (i:J)(a b:J→q): turnP i U a * turnP i U b=0:= by unfold turnP; simp_rw [Finset.mul_sum,Finset.sum_mul]; apply Finset.sum_eq_zero; intro a' _; apply Finset.sum_eq_zero; intro j _; rw [mul_mul_mul_comm,bar_alt,zero_mul]

def entree (i:J) : (J→q) →ₗ[q] q:={ toFun:=turnP i U, map_add':=pair_turn i, map_smul':=fun x a=>pair_pay i a x}

def emissions : AlternatingMap q (J→q) q J where
  toMultilinearMap:= (MultilinearMap.mkPiAlgebra q J q).compLinearMap (fun i=> entree i)
  map_eq_zero_of_eq' v i j hij h:=by
     change ∏ i,turnP i U (v i)=0
     rw [ ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), ← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨ Ne.symm h, Finset.mem_univ _⟩ : j ∈ univ.erase i),← mul_assoc,hij,turn_alt,zero_mul]

lemma on_center [DecidableEq J] (i:J) : turnP i U ((Pi.basisFun q J) i)= B i i:= by unfold turnP; rw [Finset.sum_eq_single i]; simp; intro j _ hj; simp [hj]; simp

def crown (U J:Type) [Fintype J]: Price (PairCoords.φ (U:=U) (J:=J)):= ∏ j:J,rowPair (U:=U) j j

lemma generated [DecidableEq J] (M:Matrix J J q) :
    ∏ j, turnP j U (M j)= crown U J*M.det:= by
   let A: (J→q) [⋀^J]→ₗ[q] q:= emissions
   have he := DFunLike.congr_fun (AlternatingMap.eq_smul_basis_det (Pi.basisFun q J) A) (fun i=>M i)
   rw [AlternatingMap.smul_apply,Pi.basisFun_det_apply] at he
   change (∏ j, turnP j U (M j))= (∏ j,turnP j U ((Pi.basisFun q J) j))* (Matrix.of (fun i j => M i j)).det at he
   simp_rw [on_center] at he; exact he
end YM.FVA2.Paper
