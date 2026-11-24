import YM.RegulatorIR.Axial.Along

/-!
# Repeated W1 kernel tends to exact bulk entry
Polish may depend erratically on replica size and no representative choices
are assumed locally stable. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Axial
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight PowerSeries Gain Prim Motion Budget.Packet Budget.Deck
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries
variable {W:Type}{G:Gauge} {p r k:ℕ}
variable (p:Signed) (f:Side)

def moveHold (v: Equiv.Perm W)(a:Fin r)(x:W) : Hold a x≃ Hold a (v x) where
 toFun h:=⟨v ∘ h.val,congr_arg v h.property⟩
 invFun h:=⟨v.symm ∘ h.val, (congr_arg v.symm h.property).trans (v.symm_apply_apply x)⟩
 left_inv h:= Subtype.ext (funext (fun k=>v.symm_apply_apply (h.val k)))
 right_inv h:= Subtype.ext (funext (fun k=>v.apply_symm_apply (h.val k)))
lemma stalk_collect {U V:Type}(A:U→V)(p:V)(g:U→ℝ) : Stalk.collect A g p= ∑'i:U,(if A i=p then g i else 0):=by unfold Stalk.collect;convert tsum_subtype {x| A x=p} g using 1 <;> rfl

variable {P l:ℝ}(h:Even f.val)(hp:l*f.val=P)(he:4≤f.val)
local notation "A" => Carto G l P h hp
local notation "Q" => fun z=> playS (G:=G) (Sight.slab z) h hp
variable (T:Packet (Foot G) r) (hh:(Carto G l P h hp).Ready T)
include hh he
lemma melted (x:Tuple (Foot G) r)(i:Fin r)(hm: Summable fun b:Hold i (x i)=> ‖T b.val‖) : Tendsto (fun z=> let y:=((A).wind (spark p z)) ∘ x; (Q z).polish y * (Q z).deckSum T ((Q z).project y)) atTop (𝓝 (T x)):=by
 let v(z:Side):Equiv.Perm (Foot G):=(A).wind (spark p z)
 let y(z:Side):Tuple (Foot G) r:= (v z) ∘ x
 let X :Hold i (x i):=⟨x,rfl⟩;let u(z:Side)(x:Hold i (x i)) : Tuple (Foot G) r:= v z ∘ x.val
 let addE(z:Side)(a:Hold i (x i)):ℝ:=if (Q z).project (u z a)=(Q z).project (y z) then ((Q z).polish (y z))*(Q z).dyed T (u z a) else 0
 have hT z x:T (v z ∘ x)=T x:=by rw [(Deck.ready_iff ..).mp hh]; simp [Motion.sign]
 let g(a:Hold i (x i)):ℝ:= if a=X then T x else 0
 have hs : (∑' a,g a)=T x:= by unfold g; simp
 change Tendsto (fun z:Side=> (Q z).polish _*(Q z).deckSum _ _) _ _
 have He z : (Q z).polish (y z)*(Q z).deckSum T ((Q z).project (y z))= ∑' b,addE z b:=by -- fix pay
    let P :Hold i ((Q z).orbit (y z i)):=⟨(Q z).project (y z),rfl⟩
    rw [Deck.deck_pivot (Q z) (replic h hp _ T hh) ((Q z).project (y z)) i (v z (x i)) rfl, parcel (Q z) T i (v z (x i)) P, stalk_collect,← tsum_mul_left,← (moveHold (v z) i (x i)).tsum_eq]
    apply tsum_congr;intro a;unfold addE
    by_cases hx:(Q z).project (u z a)=(Q z).project (y z)
    · rw [if_pos hx,if_pos (Subtype.ext hx)]
      rfl
    rw [if_neg hx,if_neg (mt Subtype.ext_iff.mp hx),mul_zero]
 rw [show (fun z:Side=> _*(Q z).deckSum _ _)=fun z=> ∑' b,addE z b from funext He, ← hs]
 refine tendsto_tsum_of_dominated_convergence hm (fun b : Hold i (x i)=>?_) (Eventually.of_forall ?_)
 · suffices hp: (fun z=> g b)=ᶠ[atTop] fun z=> addE z b from tendsto_const_nhds.congr' hp
   have hp' :∀ᶠ z:Side in atTop,∀ t: Fin r, (Q z).orbit (v z (b.val t))= (Q z).orbit (v z (x t)) → b.val t=x t:= eventually_all.mpr fun t=> clear p f h hp he (b.val t) (x t)
   filter_upwards [hp'] with z hz
   unfold addE;dsimp only; split
   next he=> have hh:b=X:=Subtype.ext (funext fun i=> hz i (congr_fun he i));subst b; unfold g; rw [if_pos rfl]; unfold dyed;rw [mul_left_comm, show u z X=y z from rfl,polish_sq,mul_one]; exact (hT z x).symm
   next he=> unfold g;rw [if_neg (fun hv=>he (by rw [hv]))]
 intro z a; unfold addE;split
 next h'=>
   let A':= Q z
   have hh: ‖A'.polish (y z)*A'.dyed T (u z a)‖ₑ= ‖T a.val‖ₑ:=by rw [enorm_mul,A'.dyed_cost, A'.polish_cost,one_mul,hT] -- hT evt
   exact (show _=_ from by simpa using congr_arg ENNReal.toReal hh).le
 next=> rw [norm_zero];exact norm_nonneg _
end YM.RegulatorIR.Axial
