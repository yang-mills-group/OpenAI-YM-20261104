import YM.WilsonCoeffUV.Product.Connected.RootCosts
/-!
# Spread geometrical envelopes across the join
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Soil
open Gauge Power PathCost Precision Embroider Fountain Cosmos Shard Realm
open PowerSeries
open scoped Topology BigOperators
variable {n:Side}{U V α β ι:Type*}{r h D j m e i i' j' l k u a:ℕ}{A B C s:ℝ}{G:Gauge}
variable {p q:ProfileW}{D' t η K M s S δ:ℝ}
/-- one-seam geometry. D is arbitrary lower report of lifted span, in
//coarse// units. K already includes rounding and translated centers. -/
structure SplitHill (p q:ProfileW)(η K d:ℝ) : Prop where
   lipP : AngleSea p
   lipQ : AngleSea q
   globe : 1≤K
   toll : 0<d
   nonneg : 0≤η
   year : η≤1
   edge i : η*Bank.terrain.gap 0 i ≤ K + p i
   rate i : η*Bank.terrain.gap 0 i ≤ K + q i
   gap a b: d≤ 1+(p a:ℝ)+ Bank.terrain.gap a b+q b
lemma payout (p t:ℕ)(q:ℕ)(d:ℝ)(h:0≤d)(v:d≤ 1+(p:ℝ)+t+q)(u:ℕ): d^u≤autumn 1 u p*autumn 1 u q*autumn 1 u t:=by
   unfold autumn; simp only [one_mul,←mul_pow]; gcongr; refine v.trans ?_; nlinarith only [show 0≤ (p:ℝ)*q by positivity,show 0≤(t:ℝ)*q by positivity,show 0≤(p:ℝ)*t by positivity,show 0≤(p:ℝ)*q*t by positivity]
lemma autumn_split (v:SplitHill p q η K D') (x:dock Cover α (i+j))(y:dock Cover α 2)(u:ℕ):
    let L:=hewer x y; let V:= stepping x y; hedge 0 η u x ≤ (4*K)^u*quoteT p u L*quoteT q u V:=by
   intro L V; let a:=Ridge p L; let b:=Ridge q V; have hk:0≤ K:=zero_le_one.trans v.globe; let C:=K+a+b; have hC:0≤ C:=by unfold C; positivity
   let T:=stud 0 x; have he l: η*(Bank.terrain.gap 0 (T l)) ≤ C:= by
       refine Fin.cases (by rw [show Bank.terrain.gap 0 (T 0)=0 from Bank.terrain.self 0,Nat.cast_zero,mul_zero]; exact hC) (fun l=>?_) l
       refine Fin.addCases (fun l=>?_) (fun l=>?_) l
       · let a':=(L l.succ).1; exact (v.edge a').trans ((add_le_add_right (by exact_mod_cast Ridge.host p L l.succ) K).trans (le_add_of_nonneg_right (by positivity : 0 ≤ (b:ℝ))))
       let b':=(V l.succ).1; exact (v.rate b').trans ((add_le_add_right (by exact_mod_cast Ridge.host q V l.succ) K).trans (add_le_add_left (le_add_of_nonneg_right (by positivity : 0 ≤(a:ℝ))) _))
   have hz v' t: η*(Bank.terrain.gap (T v') (T t)) ≤ 2*C:=by
       apply (mul_le_mul_of_nonneg_left (show (Bank.terrain.gap (T v') (T t):ℝ)≤ Bank.terrain.gap (T v') 0+ (Bank.terrain.gap 0 (T t):ℝ) by exact_mod_cast Bank.terrain.tri (T v') (0:Cover) (T t)) v.nonneg).trans; rw [Bank.terrain.swap (T v') 0,mul_add,two_mul]; exact add_le_add (he v') (he t)
   have ht: η *tread Bank.terrain 0 x ≤2*C:= by
       change η*↑(league Bank.terrain T)≤_
       unfold league; obtain ⟨a,_,H⟩:= Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty (fun i=> Finset.univ.sup fun j=> Bank.terrain.gap (T i) (T j)); obtain ⟨b,_,w⟩:=Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty (fun j=> Bank.terrain.gap (T a) (T j)); rw [H,w]; exact hz a b
   unfold hedge autumn; rw [quoteT,quoteT,autumn,autumn,one_mul,one_mul,←mul_pow,←mul_pow]; refine pow_le_pow_left₀ (by have he:=v.nonneg; positivity) ?_ u; refine (add_le_add_right ht 1).trans ?_; unfold C; change 1+2*(K+(a:ℝ)+b)≤4*K*(1+a)*(1+b)
   nlinarith only [v.globe, (mul_le_mul_of_nonneg_right v.globe (by positivity :0≤ (a:ℝ))), (mul_le_mul_of_nonneg_right v.globe (by positivity : 0≤ (b:ℝ))), show 0≤ K*(a:ℝ)*b by positivity]
private lemma pointPipe (G:ropes Cover α α)(g:dragCup Bank.terrain s B G)(p:0<s)(x y) (u:ℕ): autumn 1 u (Bank.terrain.gap x.1 y.1)*‖G x y‖≤ B*ceilPoly u s:=by
    let n:= Bank.terrain.gap x.1 y.1; unfold autumn; rw [one_mul]; apply (mul_le_mul_of_nonneg_left (g.2 x y) (by positivity)).trans; rw [mul_left_comm]; apply mul_le_mul_of_nonneg_left _ g.1
    simpa only [sub_zero,neg_zero,zero_mul,Real.exp_zero,mul_one] using poly_used u p n
lemma quote_plus (w:ProfileW)(i j:ℕ)(x:dock Cover α k): quoteT w (i+j) x=quoteT w i x*quoteT w j x:=by unfold quoteT autumn; rw [pow_add]
lemma spineR (v:SplitHill p q η K D') (x:dock Cover α (i+j))(y:dock Cover α 2)(G:ropes Cover α α)(g:dragCup Bank.terrain s S G)(t:0<s)(b u:ℕ): hedge 0 η u x*‖G (y 0) (y 1)‖≤ (D'^b)⁻¹ *(4*K)^u * quoteT p (u+b) (hewer (j:=j) x y)*quoteT q (u+b) (stepping (j:=j) x y)*(S*ceilPoly b s):=by
   let L:=hewer (j:=j) x y; let R:=stepping (j:=j) x y; let d:= D'^b; have hz:0<d:=pow_pos v.toll b
   suffices h : hedge 0 η u x*‖G (y 0) (y 1)‖*d≤ (4*K)^u*quoteT p (u+b) L*quoteT q (u+b) R*(S*ceilPoly b s) by
       refine ((le_div_iff₀ hz).mpr h).trans_eq ?_; change _=d⁻¹*_*_*_*_; unfold L R; rw [div_eq_mul_inv]; ring
   let Z:=Bank.terrain.gap (y 0).1 (y 1).1; have hx:D' ≤ 1+(Ridge p L:ℝ)+Z+Ridge q R:= (v.gap ..).trans (add_le_add (add_le_add_left (add_le_add_right (Nat.cast_le.mpr (Ridge.host p L 0)) _) (Z:ℝ)) (Nat.cast_le.mpr (Ridge.host q R 0)))
   have hp:d ≤ quoteT p b L * quoteT q b R * autumn 1 b Z:= payout _ _ _ _ v.toll.le hx b
   rw [mul_right_comm (hedge _ _ _ _)]
   refine (mul_le_mul_of_nonneg_right (mul_le_mul (autumn_split v x y u) hp hz.le ((hedge_nn v.nonneg x).trans (autumn_split v x y u))) (norm_nonneg _)).trans ?_
   calc
   _ = (4*K)^u*quoteT p (u+b) L*quoteT q (u+b) R*(autumn 1 b Z*‖G (y 0) (y 1)‖) := by rw [quote_plus,quote_plus]; unfold L R; ring
   _ ≤ _:= mul_le_mul_of_nonneg_left (pointPipe G g t _ _ b) (mul_nonneg (mul_nonneg (pow_nonneg (by have ho:=v.globe; linarith) _) (zero_le_one.trans (quoteT_pos L ..))) (zero_le_one.trans (quoteT_pos R ..)))
end YM.WilsonCoeffUV.Mer
