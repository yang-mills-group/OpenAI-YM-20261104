import YM.RegulatorIR.Quadratic.Vapor
import YM.Pert.Bulk.Inherit

/-! Translation quarry algebra for *full* period (not quotient).
Stationary inter-period identity intentionally exact, recovered from all
integer side identities. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Oracle
open Function Lattice Laurent Bloch Set Filter Budget Spatial Budget.Packet Budget.Tuple Budget.Layer Quadratic
open Pert.Bulk (Market sep)
open scoped Topology ENNReal NNReal BigOperators Classical Matrix
variable {X Y A B C V J K :Type} {P:ℝ} {S T U:Side→Type}
-- model and finite full labels, orientation positive
structure Quarry (X A:Type)(S: Side→Type) where
 toFull : X≃ Market A
 markedP (n) : S n≃ Site n × A

variable (W:Quarry X A S) (F:Quarry Y B T) (D:Quarry V C U)
namespace Quarry
def boom (x:X) := (W.toFull x).fst
def cabin (x:X):= (W.toFull x).snd
def shiftB (d:Cover) : Equiv.Perm X:= (W.toFull.trans (Equiv.prodCongr (Equiv.addLeft d) (Equiv.refl A))).trans W.toFull.symm
lemma to_shift (d:Cover)(x:X): W.toFull (W.shiftB d x)=(d+W.boom x,W.cabin x):= W.toFull.apply_symm_apply _
lemma places (d:Cover)(x:X): W.boom (W.shiftB d x)=d+W.boom x:= congr_arg Prod.fst (W.to_shift ..)
lemma cargos (d:Cover)(x:X): W.cabin (W.shiftB d x)=W.cabin x:=by unfold cabin; rw [to_shift]; rfl
lemma shifts (d e:Cover) : (W.shiftB d).trans (W.shiftB e)= W.shiftB (d+e):=by
 ext1 x; apply W.toFull.injective; change W.toFull (W.shiftB e (W.shiftB d x))=_; rw [to_shift,to_shift,cargos,places,← add_assoc, add_comm d]
def swrap (p:Side)(x:X): S p:= (W.markedP p).symm (wrap p (W.boom x), W.cabin x)
def slift (p:Side)(x:S p) : X:= W.toFull.symm (Lattice.lift (W.markedP p x).fst,(W.markedP p x).snd)
lemma both (p:Side)(x:S p): W.swrap p (W.slift p x)=x:=by rw [swrap,boom,cabin,slift]; simp
lemma periodic (y:X)(v:Cover)(p:Side): W.swrap p y=W.swrap p (W.shiftB (p.val • v) y):=by
 rw [swrap,swrap,places,cargos,map_add,map_nsmul, show p.val • wrap p v=0 from ?_,zero_add]
 ext1 i; change (p.val • (wrap p v) i) =0;rw [nsmul_eq_mul]; simp [Per]
lemma fibers {x y : X}{p:Side} (h: W.swrap p x=W.swrap p y): ∃ v:Cover,y=W.shiftB (p.val • v) x:=by
 obtain ⟨h,h'⟩:=Prod.mk.inj ((W.markedP p).symm.injective h)
 have hU : ∀ i:Axis,(p.val:ℤ)∣ W.boom y i-W.boom x i:= fun i=> (ZMod.intCast_eq_intCast_iff_dvd_sub ..).mp (congr_fun h i)
 choose v hv using hU
 have he: W.boom y=p.val • (v:Cover)+W.boom x:=by
    ext1 i; change _= p.val • v i+ W.boom x i; rw [nsmul_eq_mul]; linarith [hv i]
 exact ⟨v,W.toFull.injective <| by rw [to_shift];exact Prod.ext he h'.symm⟩

end Quarry
open Quarry

-- coarse translation identity

def Albedo (L:Layer X Y):Prop:= ∀ x y d, L (W.shiftB d x) (F.shiftB d y)=L x y
def ledgerRow (L:Layer X Y) (n: Side) : Matrix (S n) (T n) ℝ:= Matrix.of fun i j=> Stalk.collect (F.swrap n) (L (W.slift n i)) j
lemma ledger_at (L:Layer X Y)(h:Albedo W F L)(x:X)(p:Side)(j:T p): ledgerRow W F L p (W.swrap p x) j=Stalk.collect (F.swrap p) (L x) j:=by
 let y:=W.slift p (W.swrap p x); obtain ⟨d,hd⟩:= Quarry.fibers W (show W.swrap p x=W.swrap p y from (W.both p _).symm)
 let v:=p.val • d; let k:Equiv.Perm (Stalk (F.swrap p) j):= Equiv.subtypeEquiv (F.shiftB v) (fun i=> by rw [← F.periodic i d p])
 change (∑'i:Stalk (F.swrap p) j,L y i.val)= _;rw [←k.tsum_eq (f:=fun i=>L y i.val), hd]; exact tsum_congr (fun i :Stalk (F.swrap p) j=> h x _ v)
lemma reaches_ledger (x:X):∀ᶠ i:ℕ in atTop,let p : Side:=⟨i+1,i.succ_pos⟩;W.slift p (W.swrap p x)=x:=by
 let p(i:ℕ):Side :=⟨i+1,i.succ_pos⟩
 have hh(j:Axis):∀ᶠ i in atTop, -((p i).val:ℤ) < 2*W.boom x j ∧ 2*W.boom x j≤(p i).val :=by filter_upwards [eventually_ge_atTop ((2*W.boom x j).natAbs +1)] with w hw; change -(((w+1:ℕ) : ℤ)) < _ ∧ _≤ ((w+1:ℕ):ℤ); omega
 filter_upwards [eventually_all.mpr hh] with i hi
 intro P; rw [Quarry.slift,Quarry.swrap,Equiv.apply_symm_apply,show Lattice.lift (wrap P _)= _ from Lattice.lift_eq_iff.2 ⟨rfl,hi⟩]; exact W.toFull.symm_apply_apply _
private lemma arr {f:X→Y}(g:X→ℝ)(p:Y): Stalk.collect f g p=∑' x:X, if f x=p then g x else 0:=by
 change (∑' i:{x|f x=p}, g i.val)=_; rw [tsum_subtype]; rfl
variable {L:Layer X Y}{c:ℕ→Side}
lemma ledger_head (L:X→ℝ)(h:Summable fun i=>‖L i‖)(x:X):
 Tendsto (fun i:ℕ=>let p:Side:=⟨i+1,i.succ_pos⟩; Stalk.collect (W.swrap p) L (W.swrap p x)) atTop (𝓝 (L x)):=by
 let f (i:ℕ): Side:=⟨i+1,i.succ_pos⟩
 let t(i:ℕ)(y:X):=if W.swrap (f i) y=W.swrap (f i) x then L y else 0
 let g (y:X) := if y=x then L x else 0
 change Tendsto (fun i=>Stalk.collect (W.swrap (f i)) _ (W.swrap (f i) x)) atTop _
 simp_rw [arr]
 have ht:=tendsto_tsum_of_dominated_convergence (𝓕:=(atTop : Filter ℕ)) (f:=t) h (g:=g) (fun z=>?_) (Eventually.of_forall fun i z=>?_)
 · rw [tsum_eq_single x (f:=g) (fun i hi=>if_neg hi)] at ht; simpa [g,t] using ht
 · refine tendsto_const_nhds.congr' ?_; filter_upwards [reaches_ledger W x,reaches_ledger W z] with i hi hv
   unfold t g; by_cases h:x=z
   · simp [h]
   have hz: W.swrap (f i) z≠ W.swrap (f i) x:=fun he=>h (((congr_arg (W.slift (f i)) he)|>.symm.trans hv) ▸ hi.symm) -- fix
   simp [hz,Ne.symm h]
 unfold t; split <;> simp
lemma ledger_limit {L:Layer X Y}(h:Billed L)(he:Albedo W F L)(x:X)(y:Y) : Tendsto (fun i:ℕ=>let p : Side:= ⟨i+1,i.succ_pos⟩; ledgerRow W F L p (W.swrap p x) (F.swrap p y)) atTop (𝓝 (L x y)):=by
 simp_rw [ledger_at W F L he]; apply ledger_head; apply tsum_enorm_ne_top_iff_summable_norm.mp; rw [← quota_base]; exact h.rows _
lemma solely {Q L:Layer X Y}(h:Billed Q)(hp:Billed L)(ha:Albedo W F Q)(hh:Albedo W F L)(he:∀ᶠ i: ℕ in atTop, let p : Side:=⟨i+1,i.succ_pos⟩;ledgerRow W F Q p=ledgerRow W F L p): Q=L:=funext fun i=>funext fun j=> tendsto_nhds_unique ((ledger_limit W F h ha i j).congr' (he.mono fun _ hz=> congr_arg (fun A: Matrix _ _ ℝ=>A _ _) hz)) (ledger_limit W F hp hh i j)
end YM.RegulatorIR.Oracle
