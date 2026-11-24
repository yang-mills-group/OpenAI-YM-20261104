import YM.AlbaMS.Barr.Digger

/-!
# Cohomology using Fritz's actual braces at free level, even Tag coefficients

Parameter r from pairing must be a unit for homotopies. Uses linear matrix
mult rule intertwining order. Arcs non-project complementary gauges may also
be computed via this at finite lattice level. Reusable in projected multi-mark
Lag identities.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Cutis.Fritz
open Set Function Filter LinearMap Matrix
open scoped BigOperators Classical Topology Matrix InnerProductSpace ENNReal
open Bric Coil Inlay Inlay.Net Odom Lattice Nexus Loft
variable {G : Gauge} {E B R V W : Type*}[CommRing R][Algebra ℚ R]
variable (P: Lot E B R)(F:Fritz E B R)(r s:R)
-- homotopy operator. Lot.q already.
def bare (F:Fritz E B R)(s:R)(i j:Place E B): R:= match i,j with
  | .inl (.inl i), .inl (.inr j)=> s * F.H i j
  | .inr (.inl i), .inl (.inl j)=> s * F.U j i
  | .inl (.inr i), .inr (.inr j)=> s * F.U i j
  | _,_=>0
variable [Fintype E][Fintype B]
def clay (P:Place E B→Place E B→R): Module.End R (Floor E B R):= tom Finset.univ fun i=>∑ j:Place E B,P i j • varC R ø j
lemma qclay : P.q r=clay (line P r):=by
  ext1 v; apply Eq.trans (from_vectors (F:=P.combo) true (Strip.work r)); unfold clay; congr 1; apply congr_arg (tom _); funext i; exact kick P r i
omit [Algebra ℚ R] in
lemma clay_rises (u:Place E B→Place E B→R): Rises (clay u):= Rises.from_axis _ fun _ _=> Heg.sum _ _ fun i _=>(Heg.var i).smul _
omit [Algebra ℚ R] in
lemma clay_var (u:Place E B→Place E B→R)(i:Place E B): clay u (varC R ø i)=∑ j:Place E B,u i j • varC R ø j:= tom_var _ _ (Finset.mem_univ _)
omit [Algebra ℚ R] in
private lemma value_t {u:Place E B→Place E B→R}(h:Graded ø true u)(i):Tone (xor true (ø i)) (∑ j:Place E B,u i j • varC R ø j):= Tone.sum _ _ (fun j _=> by by_cases ht:u i j=0; rw [ht,zero_smul];apply Tone.none; rw [← h i j ht,Bool.xor_comm (ø i) (ø j),Bool.xor_assoc, Bool.xor_self,Bool.xor_false]; exact (var_tone j).smul _)
omit [Algebra ℚ R] [Fintype E] [Fintype B] in
lemma brace_p : Graded ø true (bare F r):=by rintro ((i|i)|(i|i)) ((j|j)|(j|j)) h <;> first|rfl|exact False.elim (h rfl)
def bud := clay (bare F s)
omit [Algebra ℚ R] in
lemma bend : Polar true (F.bud s):= Polar.build _ fun i _=> value_t (F.brace_p s) i
lemma Qb : Polar true (P.q r):=by rw [qclay]; apply Polar.build; intro i _; apply value_t _ i; rintro ((i|i)|(i|i)) ((j|j)|(j|j)) h <;> first|rfl|exact False.elim (h rfl)
lemma Qh : Rises (P.q r):=by rw [qclay]; exact clay_rises _
variable [DecidableEq E][DecidableEq B]
-- locals
omit [Algebra ℚ R] in
private lemma lint (h: F.Normal P) (hv:r*s=1)(i j:Place E B): (∑ x:Place E B,line P r i x * bare F s x j)+(∑ x:Place E B, bare F s i x* line P r x j)= if i=j then 1 else 0:=by
  have he (a b:R): r*a*(s*b)= a*b:=by rw [mul_mul_mul_comm,hv,one_mul]
  have hh (a b:R): s*a*(r*b)= a*b:=by rw [mul_mul_mul_comm, mul_comm s r,hv,one_mul]
  -- identity for all four diagonals
  have ha : F.H * P.Z+ P.X*F.U.transpose =1:=by rw [h.sub_inv]; exact sub_add_cancel ..
  have hb : P.Z * F.H+ F.U * P.X.transpose=1:=by
    have h := congr_arg Matrix.transpose ha; rw [transpose_one,transpose_add,transpose_mul,transpose_mul,P.Z_sym,F.H_t,transpose_transpose] at h; exact h
  have hj : P.Xᵀ * F.U=1 := by nth_rw 1 [← transpose_transpose F.U]; rw [← transpose_mul,h.long,transpose_one]
  rcases i with (i|i)|(i|i)<;> rcases j with (j|j)|(j|j) <;>
    simp only [Fintype.sum_sum_type,line,bare,zero_mul,mul_zero,Finset.sum_const_zero,add_zero,zero_add,he,hh,Sum.inl.injEq, Sum.inr.injEq, ite_false, reduceCtorEq]
  -- A i,j : line(c)*U gives (X Uᵀ), bare(K)*... ; K,Q*A case. C. L.
  · change (P.X *F.Uᵀ+F.H*P.Z) i j=_; rw [add_comm,ha, Matrix.one_apply]
  · change (P.Z * F.H+ F.U * P.X.transpose) i j=_; rw [hb, Matrix.one_apply]
  · change (F.Uᵀ * P.X) i j=_; rw [h.long, Matrix.one_apply]
  change (P.Xᵀ* F.U) i j=_; rw [hj, Matrix.one_apply]
-- extend eval to any registration inside finite fields (Lot)
lemma sups (h:F.Normal P)(hv:r*s=1)(U: Floor E B R)(hk:FinRank U): F.bud s (P.q r U)+P.q r (F.bud s U)=germ Finset.univ U:=by
  let K:=tom (ρ:=@ø E B) Finset.univ (varC R ø); let T:= bud F s; let V:= T.comp (P.q r)+(P.q r).comp T; change V U= _; rw [show V U= K U from ?_,tom_apply]; rfl
  refine Coil.extend V K false (ordinary _ _ (Exo.build (s:=Finset.univ) (v:=fun i=> ∑ j:Place E B,bare F s i j • varC R ø j) ?_) (F.bend s) ?_ (Qb P r)) (Exo.build _ ?_) ?_ hk (fun _ _ _ _=> Finset.mem_univ _)
  · intro i _; exact value_t (F.brace_p s) i
  · intro F G; exact uses (Strip.work r) P.tone
  · intro i _; rw [Bool.false_xor]; exact var_tone (R:=R) i
  intro i hi; have hh: T (P.q r (varC R ø i))+P.q r (T (varC R ø i))=∑ j:Place E B,(if i=j then (1:R) else 0) • varC R ø j:=by
    unfold T bud; rw [qclay]; simp_rw [clay_var,map_sum,map_smul,clay_var, Finset.smul_sum, smul_smul, ← lint P F r s h hv]; simp_rw [add_smul,Finset.sum_smul,Finset.sum_add_distrib]; rw [Finset.sum_comm]; congr 1; rw [Finset.sum_comm]
  change T _+ P.q r (T _)=tom _ _ _; rw [hh,tom_var _ _ hi]; simp [ite_smul]
end YM.MSBar.Cutis.Fritz
