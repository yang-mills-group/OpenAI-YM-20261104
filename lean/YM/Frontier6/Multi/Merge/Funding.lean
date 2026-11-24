import YM.Frontier6.Multi.Merge.Directions
/-! Debt of the packed products. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Road.Fork
open Function Filter Finset Set Spec Fareway Tale Lattice Next.Extract Cells MergeProof.Acme
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {I V:Type} [Fintype V][DecidableEq V]{G:Gauge}{C:Family G}{F:Extraction.Order}{S: Table C.book}{T:Fareway I}
variable {O:V→Type} [heO:∀ i,Fintype (O i)][htO:∀ i,DecidableEq (O i)]
variable (K:Final C F S) (hC: Road.Ribbon C F S)
set_option quotPrecheck false

variable {u:I→ Sigma O→ E4}{c:I→ V→ E4}(v:Sigma O→ S.Tag)(z: (Sigma O)×Axis)(t:I→ℝ) (d:ℕ){a b r hM:ℝ}
local notation "J"=> z.1.fst
local notation "η"=> fun i=>0 -- placeholder
variable (hu:∀ i,Aspect T (fun k=> cutTo i (u k))) (hc:Wide T c a) (ha:a<1)
variable (s:I→ StateIndex K)
include hu hc ha
lemma found : Wide T (fun i=> pickup (u i) (c i)) 1:= hc.concat (v:=fun i j=> cutTo j (u i)) hu ha
include hC
def sails (d:ℕ):ℝ:= expenses (fun _:V=> d)+(Fintype.card V:ℝ)*havens K d
omit hu hc ha hC in
lemma haven_nn (d:ℕ):0 ≤ havens K d:= sum_nonneg (fun _ _=> sum_nonneg (fun _ _=> sum_nonneg fun _ _=>expenses_nonneg _))
lemma rough_bill : T.Costs (fun i=> poll S (state K (s i)) (combining K (u i) (c i) v d)) (wages v + sails (V:=V) K d):=by
   let f(i)(k):= abroad K (u i) v d k; let y(i):= assembly S (c i) (fun j=> ⟨d,f i j⟩); let x(i):= assembly S (pickup (u i) (c i)) v
   have hX : T.Costs (fun i=> poll S (state K (s i)) (x i)) (wages v * 1):=crude K hC.grill (found hu hc ha) zero_le_one v s
   let r:=(sails (V:=V) K d); have he: 0 ≤ r:= add_nonneg (expenses_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (haven_nn K _)) -- include hG ha? section warnings
   let Z(i:V):= wages (cutTo i v)+havens K d; have hf(i:V): T.Costs (fun j:I=>f j i) (Z i):= unlit_anchor K d (hu i) (cutTo i v) hC.grill
   have hY:= votes K hC.grill (x:=c) (fun _:V=> d) (fun i j=> f j i) hf (hc.higher ha.le) zero_le_one s
   let A:=wages v+sails (V:=V) K d; have hZ: expenses (fun _:V=>d)*1+(∑ i:V,Z i)= A:=by unfold Z A sails; rw [mul_one,sum_add_distrib,spectrum, Finset.sum_const,nsmul_eq_mul,Finset.card_univ]; ring
   have hx':T.Costs (fun i=> poll S (state K (s i)) (x i)) A:= hX.too (by change wages v*1≤wages v+r; linarith only [he]); have hy' : T.Costs (fun i=> poll S (state K (s i)) (y i)) A:=by rw [←hZ]; exact hY
   exact (hx'.sub hy').cf (Eventually.of_forall fun i:I=> by dsimp only; unfold combining; rw [map_sub]; rfl)
variable {t} (hQ:T.Mint t (-b))(hv:1<b)
omit hc ha hC hQ hv
lemma percolating {x:I→ Sigma O→ E4}(hp:Neighbors T u x b)(hv:1<b):∀ i,Aspect T (fun k=>cutTo i (x k)):=fun i=>(hu i).peal (a:=b) (fun v=>hp (Sigma.mk i v)) hv
include hc ha hC hQ hv
lemma tending (k:ℕ)(L:I→ Icc (-r) r): T.Costs (fun i=> vibrating K (u i) v (c i) z k (t i) d (s i) (L i)) (wages v+sails (V:=V) K d-(b-1)*k):=by
   let y(i):= wag (u i) (t i) z (L i); let f:= route K v z k; have hz:T.Costs (fun i=> poll S (state K (s i)) (combining K (y i) (c i) f d)) (wages f+sails (V:=V) K d):= rough_bill K hC f d (percolating hu (wag_neighbors z hQ.pay (Costs.unlimited r (Eventually.of_forall fun i=>abs_le.mpr ((L i).property)))) hv) hc ha s
   have ht:= hz.scalarR₀ (hQ.power k|>.pay); rw [show wages f=wages v+k from revolve_cap .., show -b*(k:ℝ)+(wages v+k+sails (V:=V) K d)= wages v+sails (V:=V) K d-(b-1)*k from (by ring)] at ht; exact ht
lemma shoving : Guard T u t b (fun i u=>poll S (state K (s i)) (combining K u (c i) v d)) hM:=by
    intro y hy z; have hz:= percolating hu hy hv
    obtain ⟨k,hk⟩:= exists_nat_gt ((wages v+sails (V:=V) K d - hM)/(b-1))
    let P:=swing (Sigma O) k; let f i n:=vibrating K (y i) v (c i) z n (t i) d (s i)
    obtain ⟨r,hr,hE⟩:= Frontier6.Safe.limits K d
    have hU(L:I→ Icc (-P) P):∀ᶠ i in T.via,snug 0 r (cutTo z.1.fst (wag (y i) (t i) z (L i)))∧Injective (pickup (wag (y i) (t i) z (L i)) (c i))∧‖f i k (L i)‖ ≤ Real.exp (T.scale i*hM):=by
        have hw:=(percolating (u:=y) (x:=fun i=> wag (y i) (t i) z (L i)) hz (wag_neighbors z hQ.pay (Costs.unlimited P (Eventually.of_forall fun i=> abs_le.mpr (L i).property))) hv)
        have hT:= tending K hC v z d hz hc ha s hQ hv k L
        exact ((hw z.1.fst).cozy hr).and ((found hw hc ha).injective.and (hT hM (by linarith only [(div_lt_iff₀ (sub_pos.mpr hv)).mp hk])))
    refine ⟨k,f,?_⟩; filter_upwards [eventually_uniform (P:=fun i (p:Icc (-P) P)=> snug 0 r (cutTo z.1.fst (wag (y i) (t i) z p))∧Injective (pickup (wag (y i) (t i) z p) (c i))∧‖f i k p‖ ≤ Real.exp (T.scale i*hM)) hU] with i hi
    refine ⟨funext fun x=>?_,fun j _ x hx=> vibration K (y i) v (c i) z j (t i) x d (s i) (hi ⟨x,hx⟩|>.1) (hi ⟨x,hx⟩|>.2.1) hE, fun t ht=> (hi ⟨t,ht⟩).2.2⟩; simp only [f,vibrating,pow_zero,one_smul,route_zero]
end YM.Frontier6.Road.Fork
