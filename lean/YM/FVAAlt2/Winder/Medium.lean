import YM.FVAAlt2.Winder.Arch
import YM.RegulatorIR.Oracle.Fitness
/-! # Tape fields matrix qualifications. Apply to Step Layers with only ordinary period assumption. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Budget.FVAAlt2.Wind
open Set Filter Function Packet Layer Tuple Oracle Quadratic Lattice RG
open scoped Topology ENNReal NNReal BigOperators Classical
variable {X Y W Z J V : Type} {R S : W→Type}{M:Side→Type}{C D : ℝ≥0∞}{l:Filter W}
lemma circular (N : Quarry X Y M)(q:W→Side)(hq:Tendsto (fun i=>(q i).val) l atTop)(x:X): ∀ᶠ w in l,N.slift (q w) (N.swrap (q w) x)=x:= by
 have hh(j:Axis):∀ᶠ i in l, -((q i).val:ℤ) < 2*N.boom x j ∧ 2*N.boom x j ≤(q i).val:=by filter_upwards [hq.eventually_ge_atTop ((2*N.boom x j).natAbs+1)] with i hi; omega
 filter_upwards [eventually_all.mpr hh] with i hi; rw [Quarry.slift,Quarry.swrap, Equiv.apply_symm_apply,show Lattice.lift (wrap (q i) _) = _ from Lattice.lift_eq_iff.2 ⟨rfl,hi⟩ ]; exact N.toFull.symm_apply_apply _
noncomputable def arcP (N:Quarry X Y M)(q:W→Side)(hq:Tendsto (fun i=>(q i).val) l atTop): Arch X l (fun w=> M (q w)):={ spring:=fun i=> ⟨ N.slift (q i), (Function.LeftInverse.injective (N.both (q i))) ⟩ , pack:= fun i=> N.swrap (q i), due:=fun i=> N.both (q i), tides:=circular N q hq }
namespace Arch
variable (T:Arch X l R)(P:Arch Y l S)
lemma blank : wing T P 0 (fun _=>0) := fun _ _=> Eq.symm (funext fun _=> tsum_zero)
lemma interior : wing T T (ID X) (fun w=>ID (R w)) := by
 intro w x; ext1 y; unfold ID; dsimp only;  split
 · next hv=> subst y; unfold Stalk.collect; rw [tsum_eq_single ⟨x,rfl⟩]; simp; intro i hi; exact if_neg (fun (h:x=i.val)=> hi (Subtype.ext h.symm))
 next hv=> refine Eq.symm ((tsum_congr (g:=fun _=>0) (fun i : Stalk ( T.pack w ) y=>?_)).trans tsum_zero); exact if_neg fun (h:x=i.val)=> hv (h.symm ▸ i.property) -- implicit
lemma stroked : swap (ID X)=ID X:=by ext1 i; ext1 j; by_cases hx:i=j; subst i; rfl; simp [ID,swap,hx,Ne.symm hx] -- type X implicitly known
lemma inLeft (p:X→Z)(q:Y→J)(x:Z)(T:(X⊕ Y)→ℝ) : Stalk.collect ( Sum.map p q ) T (Sum.inl x)= Stalk.collect p (T ∘ Sum.inl) x:= by
 let E : Stalk p x≃ Stalk (Sum.map p q) (Sum.inl x):= by
    refine Equiv.ofBijective (fun i=>⟨ Sum.inl i.val,congr_arg Sum.inl i.property ⟩) ⟨fun a b h=> Subtype.ext (Sum.inl.inj (Subtype.mk.inj h)),?_⟩; rintro ⟨ y|y,hy ⟩; exact ⟨⟨y,Sum.inl.inj hy⟩,rfl⟩; contradiction
 exact Eq.symm (E.tsum_eq (T ∘ Subtype.val))
lemma inRight (p:X→Z)(q:Y→J)(y:J)(T:(X⊕ Y)→ℝ): Stalk.collect (Sum.map p q) T (Sum.inr y)=Stalk.collect q (T ∘ Sum.inr) y:=by
 let E : Stalk q y≃ Stalk (Sum.map p q) (Sum.inr y):=by
    refine Equiv.ofBijective (fun i=>⟨ Sum.inr i.val,congr_arg Sum.inr i.property ⟩) ⟨fun a b h=> Subtype.ext (Sum.inr.inj (Subtype.mk.inj h)),?_⟩; rintro ⟨ z|z,hz ⟩; contradiction; exact ⟨⟨z,Sum.inr.inj hz⟩,rfl⟩
 exact Eq.symm (E.tsum_eq (T ∘ Subtype.val))
section Glue
variable {T P} {A:Layer X X} {B:Layer X Y}{Γ:Layer Y X}{H:Layer Y Y}{a:(i:W)→Layer (R i) (R i)}{b:(i:W)→ Layer (R i) (S i)}{c:(i:W)→ Layer (S i) (R i)}{d:(i:W)→Layer (S i) (S i)}
lemma wing.glues (h:wing T T A a)(i:wing T P B b)(j:wing P T Γ c)(k:wing P P H d):wing (T.allSum P) (T.allSum P) (glued A B Γ H) (fun i=> glued (a i) (b i) (c i) (d i)):=by
 intro w z; ext1 y; unfold Arch.pos Arch.allSum; dsimp only
 cases z <;> cases y <;> rename_i z y <;> simp only [Sum.map_inl,Sum.map_inr,inLeft,inRight] <;> first|exact congr_fun (h w z) y|exact congr_fun (i w z) y| exact congr_fun (j w z) y| exact congr_fun (k w z) y
lemma Baked.glues (h:Baked T T A a)(i:Baked T P B b)(j:Baked P T Γ c)(k:Baked P P H d): Baked (T.allSum P) (T.allSum P) (glued A B Γ H) (fun i=>glued (a i) (b i) (c i) (d i)):=by unfold Baked; simp_rw [Oracle.mirror_led]; exact ⟨ h.1.glues i.1 j.1 k.1, h.2.glues j.2 i.2 k.2 ⟩
lemma goes (h: Billed A)(i:Billed B)(j:Billed Γ)(k:Billed H): Billed (glued A B Γ H):=by
 obtain ⟨a,ha,hh⟩:=h; obtain ⟨b,hb,h'⟩:=i; obtain ⟨c,hc,h''⟩:=j; obtain ⟨d,hd,h'''⟩:=k; refine ⟨max (a+b) (c+d),by finiteness, ?_⟩; rintro (x|x) <;> rw [Oracle.halo_p]
 · exact (add_le_add (hh _) (h' _)).trans (le_max_left ..)
 exact (add_le_add (h'' _) (h''' _)).trans (le_max_right ..)
lemma free0 : Billed (0: Layer X Y) := ⟨0,ENNReal.zero_ne_top,fun _=>(quota_zero _).le⟩
-- Layer combined ID proof using these ports
lemma hidden {B:Arch X l R}{Z:Arch Y l S} : Baked B Z 0 (fun _=>0):= ⟨blank B Z,blank Z B⟩
lemma clear (P:Arch X l R) : Baked P P (ID X) (fun i=>ID (R i)):= by unfold Baked; simp_rw [stroked]; exact ⟨interior P,interior P⟩
def Trust (T:Arch X l R)(P:Arch Y l S) (B:Layer X Y)(b:(i:W)→ Layer (R i) (S i)):= ∃ C, SplitT l C B fun i=> Lift.shore (T.cen i) (P.cen i) (b i)
lemma trust_of (h:Baked T P B b)(he:Billed B) (hv:Billed (swap B)) : Trust T P B b:=by
 obtain ⟨c,hc,hc'⟩:=he; obtain ⟨d,hd,hd'⟩:=hv; exact ⟨max c d, earns_split h (fun x=>(hc' x).trans (le_max_left ..)) (fun y=>(hd' y).trans (le_max_right ..)) (by finiteness) ⟩
lemma Trust.petal (h:Baked T T A a)(he:Billed A)(hv:Billed (swap A))(P:Arch Y l S) : Trust (T.allSum P) (T.allSum P) (petals A) (fun i=> petals (a i)):= by unfold petals; apply trust_of (Baked.glues h hidden hidden hidden) (goes he free0 free0 free0); rw [Oracle.mirror_led]; exact goes hv free0 free0 free0
lemma Trust.hose (h:Baked T P B b)(he:Billed B)(hv:Billed (swap B)) : Trust (T.allSum P) (T.allSum P) (swap (hoses B)) (fun i=> swap (hoses (b i))):=by
 let k:Baked (T.allSum P) (T.allSum P) (hoses B) (fun i=> hoses (b i)):= Baked.glues hidden h hidden (clear _); apply trust_of (show Baked _ _ _ _ from ⟨k.2,k.1⟩)
 · unfold hoses; rw [Oracle.mirror_led,stroked]; exact goes free0 free0 hv Quadratic.billed_id
 exact goes free0 he free0 billed_id
end Glue
end Arch
end YM.RegulatorIR.Budget.FVAAlt2.Wind
