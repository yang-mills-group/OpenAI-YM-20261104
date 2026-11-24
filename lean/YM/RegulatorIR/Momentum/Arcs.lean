import YM.RegulatorIR.Momentum.Intro
import YM.RegulatorIR.Sources.Child

/-!
# Held-root receipts and evaluation ledger
One anchor born in coarse. Translation lattice across block; no residue
count hidden as independent per leg. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Momentum
open Function Set Filter Finset Budget Budget.Packet Budget.Tuple Lattice Laurent Geometry Sources Spatial
open scoped Topology ENNReal NNReal BigOperators Classical
variable {J X Y:Type}{K:Layer (Long X) (Long Y)} {u m r s:ℕ}{c:ℝ≥0∞}
lemma porter_width (x:Long Y)(p:Tuple (Long Y) r)(v:Cover)(hs:0<s): wall (area x) 1 u (Fin.cons x p) ≤ (1+r:ℝ≥0∞)^u * quotes v x s u * wall v s u p:=by
 let d :ℝ≥0∞:=r
 let f i:=awayZ v (p i) s; let h:=awayZ v x s
 have hv : (1:ℝ≥0∞) + (∑ i, awayZ (area x) (p i) 1) ≤ (1+d) * (1 + h) * (1+∑ i,f i):=by
    apply le_trans (b:=1+∑ i:Fin r,(h+f i)) -- yes
    · apply add_le_add_right; apply sum_le_sum; intro i _
      unfold h f awayZ; simp only [award,Nat.cast_one,inv_one,one_mul,one_smul]; rw [← mul_add]
      let a:=area x;let b:=area (p i);
      have hp:s • (a-b) = -(v-s • a)+(v-s • b):=by rw [smul_sub];abel
      calc
         extent (a-b)=(s:ℝ≥0∞)⁻¹*extent (s • (a-b)):= by rw [extent_n, ← mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast hs.ne') (by finiteness),one_mul]
         _ ≤ _:= mul_le_mul_right (hp ▸ (extent_add ..).trans_eq (by rw [extent_neg])) _
    rw [sum_add_distrib,Finset.sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]; let P:= ∑ i,f i
    change 1+(d*h+P) ≤ (1+d)*(1+h)*(1+P)
    calc
       _ ≤ 1+(d*h+P)+(d+h + (d*P+h*P+d*h*P)):=le_self_add
       _ = _ := by ring
 rw [price_held]; unfold wall quotes; rw [← mul_pow, ← mul_pow]; exact pow_le_pow_left' hv _
-- translation covariant with p/P circuit. width scale row

def movesXY (X:Type)(v:Cover) : Equiv.Perm (Long X):= ⟨fun p=> (Geometry.dis v p.fst,p.snd),fun p=>(Geometry.dis (-v) p.fst,p.snd),fun _=>by simp [Geometry.dis],fun _=>by simp [Geometry.dis]⟩
def SelfT (K:Layer (Long X) (Long Y))(s:ℕ):Prop:=∀ i y t,K (movesXY X (s • t) i) (movesXY Y t y)=K i y

def RootsBudget (K:Layer (Long X) (Long Y))(s u:ℕ)(F:ℝ≥0∞): Prop:=∀ y,quota (fun x=> K x y) (fun x=> quotes (area x) y s u)≤ F

def anchor_ix (X:Type)(t:Side) : Set (Long X):= Set.range (fun i:Site t×Regalia X=> ask (Lattice.lift i.1) i.2)
def citizens (X:Type)(t:Side): Cover × (Site t×Regalia X) ≃ Long X:=by
 let f (v : Cover×(Site t × Regalia X)):= ask (child t v.1 v.2.1) v.2.2
 refine Equiv.ofBijective f ⟨?_,?_⟩
 · rintro ⟨v,x,a⟩ ⟨u,y,b⟩ he; obtain ⟨rfl,rfl⟩:= countR (congr_arg area he); have ha:a=b:=congr_arg tariff he;rw [ha]
 rintro ⟨⟨x,v⟩,y⟩;obtain ⟨⟨s,z⟩,rfl⟩:= reachesR t x; exact ⟨(s,z,v,y),rfl⟩
variable [Fintype X]
lemma repays_roots {t: Side} (h:SelfT K t.val) (hh: PriceW K t.val u m c): RootsBudget K t.val u ((t.val:ℝ≥0∞)^4 * (Fintype.card (Regalia X):ℝ≥0∞)* (c*award t.val)):=by
 intro y
 rw [← quota_perm (citizens X t)]
 let f(z: Cover × (Site t×Regalia X)) :=‖K (citizens X t z) y‖ₑ * quotes (area (citizens X t z)) y t.val u
 change (∑' z,f z)≤_; rw [ENNReal.tsum_prod', ENNReal.tsum_comm, tsum_fintype]
 have Q : (t.val:ℝ≥0∞)^4 * (Fintype.card (Regalia X):ℝ≥0∞)=(Fintype.card (Site t×Regalia X):ℝ≥0∞):= by rw [Fintype.card_prod]; norm_cast; simp [Site,Axis,Per]
 rw [Q, ← nsmul_eq_mul, ← card_univ,← sum_const]
 refine sum_le_sum fun z _=>?_
 let p:=Lattice.lift z.1;let x:= ask p z.2
 let f':= fun v=> movesXY Y (-v) y
 have ht (v:Cover) : f (v,z)= ‖K x (f' v)‖ₑ* quotes p (f' v) t.val u:=by
    let A:=movesXY X (t.val • v) x
    change ‖K A y‖ₑ*quotes (area A) y t.val u=_
    have he:K A y=K x (f' v):=by
      nth_rw 1 [show y=movesXY Y v (f' v) from ((movesXY Y v).apply_symm_apply y).symm]; exact h ..
    rw [he]; unfold quotes awayZ; change _* (1+_*extent (t.val • v+p-t.val • area y))^u=_*(1+_*extent (p-t.val • (-v+area y)))^u
    rw [show p-t.val • (-v+area y)=t.val • v+p -t.val • area y from by rw [smul_add,smul_neg];abel]
 have hv:Injective f':=fun i j hi=> neg_injective (add_right_cancel (congr_arg area hi)) -- type
 simp_rw [ht]; apply le_trans (quota_restrict f' hv (K x) (fun v=> quotes p v t.val u)); have he:= hh.cost p z.2 [] (by simp) 0
 change quota (K (ask (p+0) z.2)) _ ≤ _ at he; simpa only [add_zero,List.length_nil,pow_one] using he
end YM.RegulatorIR.Momentum
