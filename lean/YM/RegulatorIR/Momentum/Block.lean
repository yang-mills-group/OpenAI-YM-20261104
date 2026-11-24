import YM.RegulatorIR.Momentum.Rebate
import YM.RegulatorIR.Geometry.Edges

/-! Multiplying Taylor responses with a joint exponent order. Width currency
uses L1 metric in native meshes, not running-phase normals. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Momentum
open Function Set Filter Finset Budget Budget.Packet Budget.Tuple Lattice Laurent Geometry
open scoped Topology ENNReal NNReal BigOperators Classical
variable {J X Y:Type}{c L F A:ℝ≥0∞}{u m i:ℕ}
section tolls
variable [Fintype J]
lemma extent_add (v s:Moves J): extent (v+s)≤extent v+extent s:=by unfold extent; exact_mod_cast size_add v s
lemma extent_neg (v: Moves J): extent (-v)=extent v:=by unfold extent; rw [size_neg]
lemma extent_rev (v s:Moves J): extent (v-s)=extent (s-v):= by rw [← extent_neg (s-v),neg_sub] -- ?
lemma extent_n (t:ℕ)(x:Moves J): extent (t • x)= (t:ℝ≥0∞) * extent x:=by
 unfold extent; exact_mod_cast (show size (t • x)= t*size x from by unfold size; rw [mul_sum]; apply sum_congr rfl; intro i _; change Int.natAbs (t • x i)= _;rw [nsmul_eq_mul,Int.natAbs_mul,Int.natAbs_natCast])
omit [Fintype J] in
lemma add_one_order (s:Finset J)(f:J→ℝ≥0∞): 1+∑ i∈s,f i ≤ ∏ i∈s,(1+f i):=by
 induction s using Finset.induction_on with
 | empty=>simp
 | insert i s hs ih=>
    let t:= ∑ i∈s,f i;rw [sum_insert hs,prod_insert hs];apply le_trans _ (mul_le_mul_right ih (1+f i)); change 1+(f i+t) ≤ _*(1+t); rw [add_mul,one_mul,mul_add,mul_one]; calc
       _ = _:= congr_arg (1+·) (add_comm (f i) t) |>.trans (add_assoc ..).symm  -- ?
       _ ≤ (1+t)+(f i+f i*t):=add_le_add_right (le_self_add) _ -- left orientation?
end tolls
-- output norm relative fixed fine root. generative
section movesR
abbrev Regalia (X:Type):=Axis×X
abbrev MovesR (r:ℕ):=Moves (Fin r × Axis)
def ask (p:Cover)(f:Regalia X): Long X:= ((p,f.fst),f.snd)
def area (v:Long X):= v.fst.fst
def tariff (v:Long X): Regalia X:= (v.fst.snd,v.snd)
def award (s:ℕ):= (s:ℝ≥0∞)⁻¹
def awayZ (p:Cover)(x:Long X)(s:ℕ):ℝ≥0∞ := award s * extent (p-s • area x)
def quotes (p:Cover)(x:Long X)(s u:ℕ):ℝ≥0∞:=(1+awayZ p x s)^u
lemma quote_one (p:Cover)(x:Long X)(s u):1 ≤ quotes p x s u:=one_le_pow₀ le_self_add
variable {r s:ℕ}
def confers (v:MovesR r)(i:Fin r):Cover:= fun t=> v (i,t)
def wall (p:Cover)(s u:ℕ)(t:Tuple (Long X) r):ℝ≥0∞ := (1+∑ i, awayZ p (t i) s)^u
lemma wall_one (p:Cover)(s u)(t:Tuple (Long X) r) : 1 ≤ wall p s u t:= one_le_pow₀ le_self_add
lemma dollars (v:MovesR r):∑ i,extent (confers v i)=extent v:=by unfold extent; norm_cast; simp_rw [size,Fintype.sum_prod_type];rfl
lemma wages (v:MovesR r)(p:Cover)(t:Tuple (Long X) r) : wall p s u t ≤ (1+award s * extent v)^u * ∏ i, quotes (p+confers v i) (t i) s u:=by
 unfold wall;simp_rw [quotes]; rw [Finset.prod_pow,← mul_pow]; apply pow_le_pow_left'; let f i:= awayZ (p+confers v i) (t i) s
 have ht i : awayZ p (t i) s ≤ award s*extent (confers v i)+ f i:=by
    unfold f awayZ; rw [← mul_add]; apply mul_le_mul_right
    let z:=confers v i; let y:= s • area (t i)
    rw [← show -z +(p+z-y)=p-y by abel]; exact (extent_add ..).trans_eq (by rw [extent_neg z])
 have hh:= sum_le_sum (fun i (_:i∈ @Finset.univ (Fin r) _)=>ht i); rw [sum_add_distrib,← mul_sum,dollars] at hh
 let x:=award s * extent v;let B:=∑ i,f i
 apply le_trans (show 1+ _ ≤ 1+(x+B) from add_le_add_right hh _)
 apply le_trans _ (mul_le_mul_right (add_one_order Finset.univ f) _)
 change 1+(x+B) ≤ (1+x)*(1+B)
 rw [← add_assoc,mul_add,mul_one,add_mul,one_mul]; gcongr; exact le_self_add
end movesR
section parts
lemma produced (p:ℕ)(W:Fin p→X→ℝ)(A:Fin p→X→ℝ≥0∞): quota (fun v:Tuple X p=>∏ i,W i (v i)) (fun v=>∏ i,A i (v i))=∏ i,quota (W i) (A i):=by
 induction p with
 | zero=> simp [quota, Tuple]
 | succ p ih=>
    let f (s:X × Tuple X p) := s.2; let V: X×Tuple X p≃Tuple X (p+1):= Tuple.glueEquiv ..
    let T(v : Tuple X p):=∏ i,W i.succ (v i)
    let t(v:Tuple X p):=∏ i,A i.succ (v i)
    have he s : (∏ i: Fin (p+1),W i (V s i))= W 0 s.1 * T s.2:=by unfold V T; rw [Fin.prod_univ_succ];rfl
    have hh s : (∏ i: Fin (p+1),A i (V s i))= A 0 s.1*t s.2:=by unfold V t;rw [Fin.prod_univ_succ];rfl
    rw [← quota_perm V]; change quota (fun s=>∏ i, W i (V s i)) (fun s=> ∏ i,A i (V s i))=_;simp_rw [he,hh]; rw [Fin.prod_univ_succ (f:=fun i=> quota ..),quota_prod (fun i j=> W 0 i * T j) (fun i j=>A 0 i * t j),← ih (fun i=>W i.succ) (fun i=>A i.succ)]
    unfold quota; simp_rw [enorm_mul, mul_mul_mul_comm (‖W 0 _‖ₑ) _ (A 0 _),ENNReal.tsum_mul_left,ENNReal.tsum_mul_right];rfl
end parts
end YM.RegulatorIR.Momentum
