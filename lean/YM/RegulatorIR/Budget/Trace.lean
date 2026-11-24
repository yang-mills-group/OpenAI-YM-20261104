import YM.RegulatorIR.Budget.Order

/-! Unary contraction with the covariance. Self-pairings in the finite
logarithmic heat equation. Here there is not yet a rank/factorial
prefactor. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Budget
open Set Function Tuple Motion Spatial
open scoped NNReal ENNReal Topology BigOperators Classical
variable {X Y Z : Type} {r : ℕ} {P:ℝ}
namespace Tuple

def linked (x:Tuple X r)(i:X×X):Tuple X (r+2):=Fin.cons i.1 (Fin.cons i.2 x)
def linkEquiv (r:ℕ)(X:Type) : Tuple X r × (X × X) ≃ Tuple X (r+2) where
 toFun p:=linked p.1 p.2
 invFun p:=(Fin.tail (Fin.tail p),(p 0,Fin.tail p 0))
 left_inv p:=by rcases p with ⟨x,i,j⟩; simp [linked]
 right_inv p:=by dsimp only [linked]; simp
@[simp] lemma link_here (v: Tuple X r)(p:X×X)(j:Fin r):linked v p j.succ.succ = v j:=by simp [linked]
@[simp] lemma link_first (v:Tuple X r)(p:X×X):linked v p 0=p.1:=by simp [linked]
@[simp] lemma link_second (v:Tuple X r)(p:X×X):linked v p (0:Fin (r+1)).succ=p.2:=by simp [linked]
lemma map_link (A:X→Y)(v:Tuple X r)(p:X×X): A ∘ linked v p=linked (A∘v) (A p.1,A p.2):=by simp_rw [linked, comp_cons]
def linkHold (i:Fin r)(x:X):Hold i x × (X×X) ≃Hold i.succ.succ x:=by
 refine Equiv.ofBijective (fun p=>⟨linked p.1.val p.2,(link_here ..).trans p.1.property⟩) ⟨?_,?_⟩
 · rintro ⟨a,u⟩ ⟨b,v⟩ he
   have h := (linkEquiv r X).injective (show linkEquiv r X (a.val,u)=linkEquiv r X (b.val,v) from Subtype.mk.inj he)
   exact Prod.ext (Subtype.ext ((Prod.mk.inj h).1)) (Prod.mk.inj h).2
 rintro ⟨u,hu⟩
 obtain ⟨⟨z,y⟩,rfl⟩:= (linkEquiv r X).surjective u; change linked z y i.succ.succ = x at hu
 rw [link_here] at hu
 exact ⟨(⟨z,hu⟩,y),rfl⟩
lemma linked_diameter (A:Tariff X) (x:Tuple X r)(p:X×X): A.diameter x ≤ A.diameter (linked x p):= by
  refine A.diameter_le (A.diameter_unit _) fun i j=>?_
  simpa only [link_here] using A.diameter_ge (linked x p) i.succ.succ j.succ.succ
lemma linked_width {A:Tariff X}(B:Premium A)(x:Tuple X r)(p:X×X): B.width x ≤ B.width (linked x p):=by
  refine B.width_le ((linked_diameter ..).trans (B.width_diameter _)) fun i=>?_
  simpa only [link_here] using B.width_ge (linked x p) i.succ.succ
lemma price_link (T:Tuple X (r+2)→ℝ≥0∞): (∑'x,∑'p,T (linked x p))=∑'x,T x:=
   ENNReal.tsum_prod.symm.trans ((linkEquiv r X).tsum_eq T)
lemma price_hold (T:Tuple X (r+2)→ℝ≥0∞)(i:Fin r)(x:X):
   (∑'z:Hold i x,∑'p,T (linked z.val p))=∑'z:Hold i.succ.succ x,T z.val:= ENNReal.tsum_prod.symm.trans ((linkHold i x).tsum_eq (fun z=>T z.val))
end Tuple
namespace Deck
lemma link_polish (A:Deck P X Y)(u:Tuple X r)(v:X×X): A.polish (linked u v)= A.orient v.1*A.orient v.2*A.polish u:=by
 unfold polish linked; simp_rw [Fin.prod_univ_succ]; simp [mul_assoc]
end Deck
namespace Packet

def curve (T:Packet X (r+2))(K:Layer X X) (u:Tuple X r) (w:X × X) := K w.1 w.2 * T (linked u w)
def loop (T:Packet X (r+2))(K:Layer X X):Packet X r:= fun z=>∑' w,curve T K z w
lemma loop_mark (T:Packet X (r+2)){K:Layer X X}{A:Tariff X}{B:Premium A}{c:ℝ≥0∞}(hh:Layer.height K c):
       markQ B (loop T K) ≤ c* markQ B T:= by
  apply (inside_quota (curve T K) B.width).trans
  unfold markQ quota; rw [← price_link (r:=r) (T:=fun z=>‖T z‖ₑ * B.width z),← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum; intro x; rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum; intro p; dsimp only
  rw [curve,enorm_mul,← mul_assoc]; exact mul_le_mul' (mul_le_mul_left (hh ..) _) (linked_width ..)
lemma loop_cost {T:Packet X (r+2)}{K:Layer X X}{A:Tariff X}{c d:ℝ≥0∞}(ht:localQ A T d)(hh:Layer.height K c)(i:Fin r)(x:X) :
   (∑' z:Hold i x,quota (curve T K z.val) (fun _=> A.diameter z.val)) ≤ c*d := by
 refine le_trans ?_ (mul_le_mul_right (ht i.succ.succ x) c)
 unfold Stalk.scopeQ quota; rw [← price_hold (r:=r) (fun x=>‖T x‖ₑ * A.diameter x),← ENNReal.tsum_mul_left]
 apply ENNReal.tsum_le_tsum; intro x; rw [← ENNReal.tsum_mul_left];apply ENNReal.tsum_le_tsum;intro p; dsimp only
 rw [curve,enorm_mul,← mul_assoc]; exact mul_le_mul' (mul_le_mul_left (hh ..) _) (linked_diameter ..)
lemma loop_local {T:Packet X (r+2)}{K:Layer X X}{A:Tariff X}{c d:ℝ≥0∞}(ht:localQ A T d)(hh:Layer.height K c):localQ A (loop T K) (c*d) := fun i x=>
 (inside_quota (fun z:Hold i x=>curve T K z.val) _).trans (loop_cost ht hh i x)
lemma loop_ready {T:Packet X (r+2)}{A:Deck P X Y}(h:A.Ready T){K:Layer X X}(hk: Layer.Sym A A K):A.Ready (loop T K):=by
 apply (Deck.ready_iff A _).mpr
 intro d x
 unfold loop; rw [← tsum_mul_left,← (Equiv.prodCongr (A.wind d) (A.wind d)).tsum_eq]
 apply tsum_congr; intro ⟨i,j⟩
 change K (A.wind d i) (A.wind d j) * T (linked (A.wind d ∘ x) ((A.wind d) i,(A.wind d) j)) = d.sign^r*(K i j*T (linked x (i,j)))
 rw [hk]
 rw [← show (A.wind d) ∘ linked x (i,j)=linked ((A.wind d) ∘ x) ((A.wind d) i,(A.wind d) j) from map_link _ _ _,(Deck.ready_iff A T).mp h d, pow_add,show d.sign^2=1 from by rw [pow_two,Motion.sign_sq]]
 ring

end Packet
end YM.RegulatorIR.Budget
