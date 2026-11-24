import YM.FVAAlt2.Winder.Medium
/-! # Exact root materialization for translational torsors (free ONLY in period-lattice index). Need not assume cost on every ℓ.IR.Symmetric rendering. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Budget.FVAAlt2.Wind.Seed
open Function Layer Packet Tuple Set Filter Diagram Oracle Lattice
open scoped ENNReal NNReal BigOperators Classical Topology
variable {X Y I J A W : Type}{F S : Side→ Type} {r:ℕ}
structure Travel (X Y : Type) where
   pack : X→ Y
   hop : Cover→ Equiv.Perm X
   back v x : hop (-v) (hop v x)=x
   ok v x : pack (hop v x)=pack x
   amb (x y:X) : pack x=pack y→ ∃! (v:Cover), hop v x=y
namespace Travel
lemma one {Z:Type}{n:Side} (U: Quarry X Z S)(x:X) {p q: Cover}(h: U.shiftB (n.val • p) x= U.shiftB (n.val • q) x): p=q:=by
 have h0:= congr_arg U.boom h; simp_rw [Quarry.places] at h0; replace h0:= add_right_cancel h0; ext1 z; have h:=congr_fun h0 z; change n.val • p z=n.val • q z at h; rw [nsmul_eq_mul,nsmul_eq_mul] at h; exact mul_left_cancel₀ (by exact_mod_cast n.property.ne') h
noncomputable def march (n:Side)(U:Quarry X A S): Travel X (S n) := by
 refine ⟨ U.swrap n, fun v=> U.shiftB (n.val • v), ?_,fun v x=>(U.periodic x v n).symm, ?_ ⟩
 · intro v x; apply U.toFull.injective; rw [Quarry.to_shift,Quarry.boom,Quarry.cabin,Quarry.to_shift]; change (n.val • (-v)+_,_)=_; rw [smul_neg]; refine Prod.ext ?_ rfl; dsimp only; unfold Quarry.boom; abel
 intro x y h; obtain ⟨v,hv⟩:=U.fibers h; exact ⟨v,hv.symm,fun z hz=> one U x (hz.trans hv)⟩
lemma hoprev (T:Travel X Y)(v:Cover)(x:X): T.hop v (T.hop (-v) x)=x:= by simpa only [neg_neg] using T.back (-v) x
noncomputable def disj (T:Travel X Y)(R: Travel I J): Travel (X⊕I) (Y⊕ J) := {
   pack:= Sum.map T.pack R.pack, hop:=fun v=> Equiv.sumCongr (T.hop v) (R.hop v), back:= by intro v x; cases x <;> simp only [ Equiv.sumCongr_apply, Sum.map_inl,Sum.map_inr,T.back,R.back ], ok:=by intro v x; cases x <;> simp [T.ok,R.ok], amb:=by
      rintro (x|x) (y|y) h
      · simpa using T.amb x y (Sum.inl.inj h)
      · contradiction
      · contradiction
      simpa using R.amb x y (Sum.inr.inj h) }
end Travel
variable (T:Travel X Y)(R:Travel I J)
def Self (T:Travel X Y)(B:Y→X) := ∀ i,T.pack (B i)=i
private abbrev rides (T:Travel X Y)(i:Fin r) (x:X) (p:Tuple Y r→Prop)(z:Tuple X r):= T.pack (z i)= T.pack x∧ p (T.pack ∘ z)
private abbrev sight (T:Travel X Y)(i:Fin r)(x:X)(p:Tuple Y r→Prop)(z:Hold i x):= p (T.pack ∘ z.val)
private abbrev Ride (T:Travel X Y)(i:Fin r) (x:X) (p:Tuple Y r→Prop):= {u// rides T i x p u}
private abbrev Held (T:Travel X Y)(i:Fin r)(x:X)(p:Tuple Y r→Prop):= {u// sight T i x p u}
section Mobility
variable (i:Fin r) (x:X) (p:Tuple Y r→Prop) (B:J→I)
local notation "R₀"=> Ride T i x p
local notation "H₀"=> Held T i x p
private lemma generous (z:R₀): ∃! (v:Cover),T.hop v (z.val i)=x:= T.amb _ x z.property.1
private noncomputable def move (z:R₀): Cover:= Classical.choose ((generous T i x p z).exists)
private lemma moved (z:R₀): T.hop ( move T i x p z ) (z.val i)=x:= Classical.choose_spec ((generous T i x p z).exists)
private lemma amnesty (u:Tuple X r) (v:Cover): T.pack ∘ ( T.hop v ∘ u ) = T.pack ∘ u := funext fun _=> T.ok ..
private def gate (z:R₀): H₀:=
   ⟨⟨T.hop (move T i x p z) ∘ z.val, moved T i x p z⟩,by change p ( T.pack ∘ _) ; rw [amnesty]; exact z.property.2⟩
private def able (z:J × R₀): I × H₀:= ( R.hop (move T i x p z.2) (B z.1), gate T i x p z.2 )
private def inter (v:Cover)(z:H₀):R₀:=⟨ T.hop (-v)∘ z.val.val, by
    change T.pack ( T.hop (-v) _ )= _ ∧ _; rw [T.ok,show z.val.val i=x from z.val.property]; refine ⟨rfl,?_⟩; rw [amnesty]; exact z.property⟩
variable (h:Self R B)
include h
private noncomputable def Tile : J × R₀≃ I× H₀:=by
    refine Equiv.ofBijective (able T R i x p B) ⟨?_,?_⟩
    · rintro ⟨a,z⟩ ⟨b,y⟩ he; let v:= move T i x p z; let w:=move T i x p y; have hz:R.hop v (B a)=R.hop w (B b):=congr_arg Prod.fst he
      have ht:a=b:=(h a).symm.trans <| (( R.ok v _ ).symm.trans ((congr_arg R.pack hz).trans ( (R.ok w _).trans (h b) )))
      subst b
      refine Prod.ext rfl (Subtype.ext ?_); have hm: T.hop v∘ z.val=T.hop w ∘ y.val := congr_arg (fun u:I× H₀=> u.2.val.val) he; -- use earlier w=v. keep
      rw [show w=v from ?_] at hm; exact funext fun _=> (T.hop v).injective (congr_fun hm _)
      exact (R.amb _ _ (R.ok v (B a)|>.symm)).unique hz.symm rfl
    rintro ⟨a,z⟩; obtain ⟨w,hw,-⟩:= R.amb (B (R.pack a)) a (h _)
    let y:=inter T i x p w z; have ht: T.hop w ∘ y.val=z.val.val:= funext (fun j=>T.hoprev w (z.val.val j)); have hc: move T i x p y=w := ( generous T i x p y ).unique ( moved T i x p y ) ((congr_fun ht i).trans z.val.property)
    refine ⟨(R.pack a,y),Prod.ext (by change R.hop (move _ _ _ _ y) _=_; rw [hc]; exact hw) (Subtype.ext (Subtype.ext ?_))⟩; change T.hop (move _ _ _ _ y) ∘ y.val=_; rw [hc,ht]
-- exact material, summability not assumed except ONE root
end Mobility

def Powered (T:Travel X Y)(S:Travel I J)(v:I→ Packet X r):= ∀ h i x,v (S.hop h i) (T.hop h ∘ x) = v i x
def manyS (v:I→ Packet X r): Packet X r:=fun w=>∑' i,v i w
variable (i:Fin r) (x:X) (p:Tuple Y r→Prop) (B:J→I)
local notation "R₀"=> Ride T i x p
local notation "H₀"=> Held T i x p
variable {T R}
variable (h:Self R B){v:I→ Packet X r}(m:Powered T R v)(n: ∀ i,cost (v i)≠ ⊤)
section Bill
include T R h m
lemma travelPrice [Fintype J]: cost (fun s:I × H₀=>v s.1 s.2.val.val) ≤ ∑ j,cost (v (B j)):=by
 let U:= Tile T R i x p B h; change _ ≤ _; refine le_trans ( (quota_perm U (fun s:I × H₀=> _) 1 ).symm.le ) ?_
 change cost (fun s:J × R₀ => v _ (U s).2.val.val) ≤ _
 rw [show (fun s:J× R₀ => v (U s).1 (U s).2.val.val)=(fun s=> v (B s.1) s.2.val) from funext fun s:J× R₀=> m _ _ _,up_prod,tsum_fintype]
 apply Finset.sum_le_sum; intro b _; exact quota_restrict (Subtype.val: R₀→ Tuple X r) Subtype.val_injective (v (B b)) 1
lemma nativeCost [Fintype J] : cost ( manyS v ∘ (Subtype.val: Hold i x→ Tuple X r) ) ≤ ∑ j,cost (v (B j)):= by
 let p:=fun _ : Tuple Y r=> True
 let E: Hold i x ≃ Held T i x p:= { toFun:= fun z=>⟨z,trivial⟩, invFun:= fun z=>z.val,left_inv:= fun _=> rfl, right_inv:=fun _=>rfl }
 let U (z:Hold i x)(j:I):= v j z.val; let B' : Hold i x× I≃ I× Held T i x p:= (Equiv.prodComm (Hold i x) I ).trans (Equiv.prodCongr ( Equiv.refl _ ) E)
 refine (inside_quota U 1 ).trans ( ( quota_prod U 1 ).symm.le.trans ?_ )
 exact ( quota_perm B' (fun s:I × Held T i x p => v s.1 s.2.val.val) 1 ).le.trans (travelPrice i x p B h m)
include n
lemma equals [Fintype J] :
 (∑'z:H₀, manyS v z.val.val) = ∑ j,∑'z:R₀, v (B j) z.val:=by
 let E:= Tile T R i x p B h
 let G(j:I)(z:H₀):= v j z.val.val; let F(j:J)(z:R₀):= v (B j) z.val
 have H(i:J × R₀): G (E i).1 (E i).2=F i.1 i.2:= m _ _ _
 have hu:Summable (fun i : I× H₀=>G i.1 i.2):= amassed _ ( ne_top_of_le_ne_top (ENNReal.sum_ne_top.mpr (fun j (_:j∈Finset.univ)=>n (B j))) (travelPrice i x p B h m ) )
 have hp:Summable (fun i:J× R₀=> F i.1 i.2):=(hu.comp_injective E.injective).congr H
 change (∑'z:H₀,∑'j,G j z)=∑ j,∑'z:R₀,F j z
 rw [hu.tsum_comm,← hu.tsum_prod,← tsum_fintype (L:=SummationFilter.unconditional _),← hp.tsum_prod,← E.tsum_eq]
 simp_rw [H]
lemma acts_here [Fintype J] (u:Hold i (T.pack x)) : Stalk.collect (Arch.projection T.pack i x) (manyS v ∘ Subtype.val) u=∑ j, Stalk.collect (fun x:Tuple X r=> T.pack ∘ x ) (v (B j)) u.val := by
 let p:=fun z:Tuple Y r=> z=u.val
 let E: Stalk ( Arch.projection T.pack i x ) u ≃ Held T i x p := Equiv.subtypeEquivRight (fun k=> (Subtype.ext_iff ))
 let F: Ride T i x p≃ Stalk (fun x:Tuple X r=>T.pack ∘ x) u.val:= Equiv.subtypeEquivRight (fun z=>⟨ fun h=> h.2, fun he=> ⟨ (congr_fun he i).trans u.property,he⟩⟩)
 refine ( E.tsum_eq (fun z=> manyS v z.val.val) ).trans ((equals i x p B h m n ).trans ?_); exact Finset.sum_congr rfl fun j _=>( F.tsum_eq (fun z=>v (B j) z.val) )
end Bill

-- can buy all self-costs W before any positivity-demand. include ∀τ any arch.Frame variant for campaign existence. 
theorem HeldFoot [Fintype J] (R:Travel I J)(T:Travel X Y)(v:I→Packet X r)(B:J→I)(h:Self R B)(m:Powered T R v)(n:∀ i,cost (v i)≠⊤): ∃ C:ℝ≥0∞,C≠⊤ ∧ ∀ x i,cost (manyS v ∘ (Subtype.val: Hold i x→ Tuple X r)) ≤ C:= by exact ⟨_,ENNReal.sum_ne_top.mpr (fun j (_:j∈ Finset.univ)=> n (B j)), fun x i=> nativeCost i x B h m⟩
-- Indexed cost at h stage.FVar.
end YM.RegulatorIR.Budget.FVAAlt2.Wind.Seed

