import YM.OPE.Compatible.Dale.Mesa
/-!
# Gauge Forest on graph with directed signed bonds
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade
open Function Filter Set Lattice Laurent Tree Woody Weir
open scoped Topology BigOperators ComplexConjugate Classical
variable {D V:Type*}
-- no conv.
structure Score (D V:Type*) where
  inn:D→V
  out:D→V
namespace Score
variable (R:Score D V)
def start (p:D × Bool):V:=if p.2 then R.out p.1 else R.inn p.1
def lastV (p:D × Bool):V:=if p.2 then R.inn p.1 else R.out p.1
lemma swapV (p:D)(b:Bool): R.start (p,!b)=R.lastV (p,b):=by cases b<;>rfl
variable {K:Type*}[Group K]
def taste (u:D→K)(p:D×Bool):= if p.2 then (u p.1)⁻¹ else u p.1
def dress (s:V→K)(u:D→K)(e:D) := s (R.inn e)*u e*(s (R.out e))⁻¹
lemma tasteD (s:V→K)(u:D→K)(p:D×Bool): taste (R.dress s u) p=s (R.start p)*taste u p*(s (R.lastV p))⁻¹:=by
     unfold taste dress start lastV; cases e:p.2 <;> simp [mul_assoc]
lemma dance (u:D→K): R.dress 1 u=u:=by ext; simp [dress]
lemma dandy (u v:V→K)(s:D→K): R.dress u (R.dress v s)=R.dress (u*v) s:=by funext i; simp [dress,mul_assoc]
variable (B:Set V)
structure Stand where
   point : ↥(Bᶜ)→ D × Bool
   flick : V→ℕ
   root (v: ↥(Bᶜ)): R.start (point v)=v.val
   bump (v: ↥(Bᶜ)): flick (R.lastV (point v))<flick v.val
namespace Stand
variable {R B}
variable (T:R.Stand B)
def Branch (p:D):Prop:=p∈ Set.range (Prod.fst ∘ T.point)
def Leaf (p:D):Prop:=¬ T.Branch p
abbrev Free:= {i:D// T.Leaf i}
abbrev Stable:= {i:D// T.Branch i}
-- equiv complement
lemma oneRoad : Injective (Prod.fst ∘ T.point):=by
    intro i j h; let a:=(T.point i).2; let b:=(T.point j).2; let x:=(T.point i).1; have hi:T.point i=(x,a):=rfl; have hj:T.point j=(x,b):=(Prod.ext h.symm rfl); have hu:= T.root i; have hv:= T.root j; have he:= T.bump i; have hh:= T.bump j; rw [hi] at hu he; rw [hj] at hv hh
    rcases Bool.eq_or_eq_not a b with H|H
    · rw [H,hv] at hu; exact Subtype.ext hu.symm
    rw [H,R.swapV] at hu; rw [H,← R.swapV,Bool.not_not,hv] at he; rw [hu] at hh; exact (lt_asymm hh he).elim
-- gauge comp and elimination
lemma purity (p: ↥(Bᶜ)): T.Branch (T.point p).1:=⟨p,rfl⟩
def cite {α:Type*}(v:T.Stable→α)(u:T.Free→α)(p:D) := if h:T.Branch p then v ⟨p,h⟩ else u ⟨p,h⟩
@[simp] lemma kept {α:Type*}(v:T.Stable→α)(u:T.Free→α)(p:T.Free): T.cite v u p.val=u p:=by simp only [cite,dif_neg p.property]
@[simp] lemma keptZ {α:Type*}(v:T.Stable→α)(u:T.Free→α)(p:T.Stable): T.cite v u p.val=v p:=by simp only [cite,dif_pos p.property]
lemma keepAll {α:Type*}(w:D→α): T.cite (fun p=> w p.val) (fun p=> w p.val)=w:=by funext i; unfold cite; split <;>rfl
def sweep (u:D→K)(p:V): K:= if h:p ∈ Bᶜ then
   let v: ↥(Bᶜ):=⟨p,h⟩; have _:T.flick (R.lastV (T.point v))<T.flick p:=T.bump v
   sweep u (R.lastV (T.point v))*(taste u (T.point v))⁻¹ else 1
termination_by T.flick p
lemma swept (u:D→K){p:V}(h:p∈ B): T.sweep u p=1:=by rw [sweep,dif_neg (by simpa)]
lemma sweptJ (u:D→K)(p: ↥(Bᶜ)): T.sweep u p=T.sweep u (R.lastV (T.point p))*(taste u (T.point p))⁻¹:=by rw [sweep,dif_pos p.property]
lemma bare_sweep (u:D→K)(p:T.Stable): R.dress (T.sweep u) u p.val=1:=by
    obtain ⟨v,hv⟩:= p.property; have he:T.Stable:=p; let q:=T.point v; have hv:q.1=p.val:=hv; have hh : taste (R.dress (T.sweep u) u) q=1:=by
         rw [R.tasteD,T.root v,T.sweptJ]; dsimp [q]; group
    unfold taste at hh; rw [hv] at hh; split at hh <;>simpa using hh
lemma sweep_spec (u:D→K)(s:V→K)(hs:∀ p∈ B,s p=1)(ht:∀ p:T.Stable,R.dress s u p=1):s=T.sweep u:=by
    funext i; induction v : T.flick i using Nat.strong_induction_on generalizing i with
    | h v ih =>
       by_cases h:i∈Bᶜ
       · let p: ↥(Bᶜ):=⟨i,h⟩; let q:=T.point p
         have he : taste (R.dress s u) q=1:=by simp only [taste,show R.dress s u q.1=1 from ht ⟨_,T.purity p⟩]; simp
         have hh:=ih _ ((T.bump p).trans_eq v) (R.lastV q) rfl
         change s p.val=T.sweep u p.val; rw [T.sweptJ]; rw [R.tasteD,T.root p,hh] at he; exact mul_right_cancel (b:=taste u q) ((mul_inv_eq_one.mp he).trans (by simp [mul_assoc,q]))
       have ht:i ∈ B:=not_not.mp h; rw [hs i ht,T.swept u ht]
lemma treed (s:T.Free→K): T.sweep (T.cite 1 s)=1:=(T.sweep_spec _ 1 (fun _ _=>rfl) (fun p=>by rw [R.dance,T.keptZ];rfl)).symm
def dell (u:D→K)(p:T.Free): K :=R.dress (T.sweep u) u p.val
lemma emits (u:D→K): R.dress (T.sweep u) u=T.cite 1 (T.dell u):=by
      funext i; unfold cite; split_ifs with h; exact T.bare_sweep _ ⟨_,h⟩; rfl
lemma stays (s:T.Free→K): T.dell (T.cite 1 s)=s:=by
      funext i; rw [dell,treed,R.dance,kept]
lemma sweep_reg (s:V→K)(hs:∀ i∈ B,s i=1)(u:D→K): T.sweep (R.dress s u)= (T.sweep u)*s⁻¹ := by
      symm; apply T.sweep_spec; intro p h; simp [hs p h,T.swept u h]; intro p; rw [R.dandy,inv_mul_cancel_right,T.bare_sweep]
lemma dell_reg (s:V→K)(hs:∀ i∈ B,s i=1)(u:D→K): T.dell (R.dress s u)=T.dell u:=by
      funext p; rw [dell,T.sweep_reg s hs,R.dandy, inv_mul_cancel_right]; rfl
-- stand change
lemma alike (H:R.Stand B)(v:D→K): T.dell (H.cite 1 (H.dell v))=T.dell v :=by
      rw [← H.emits,T.dell_reg _ (fun p h=> H.swept v h)]
def drapeX (H:R.Stand B): (T.Free→ K)≃ (H.Free→ K):= ⟨fun s=> H.dell (T.cite 1 s), fun s=> T.dell (H.cite 1 s),fun s=> (T.alike H (T.cite 1 s)).trans (T.stays s),fun s=> (H.alike T (H.cite 1 s)).trans (H.stays s)⟩
end Stand
end Score
end YM.OPE.Cascade
