import YM.OPE.Compatible.Grotto.Dual
/-!
# Angular phase spectra.Lifting station members multilinearly. erased.B.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function Filter Set ContinuousLinearMap Asymptotics
open scoped Topology BigOperators Classical
variable {d k i j s:ℕ}{E:Fin s→Type}{G:ℕ→Type}[∀ i,NormedAddCommGroup (E i)][∀ i,NormedSpace ℝ (E i)] [∀ i,NormedAddCommGroup (G i)] [∀ i,NormedSpace ℝ (G i)]
variable {b r x v u:ℝ}{μ:ℕ→ℝ}
local notation "S!"=> Mints E
local notation "L!"=> S! →L[ℝ] S!
variable {T:∀ i: Fin s,Cuts d μ v b (E i) G}
variable {p:(∀ i:Fin s,E i) →L[ℝ] (∀ i:Fin s,E i)}
def Fruition (p:L!)(x:ℝ):Submodule ℝ S!:= LinearMap.ker (Ux p x ^s).toLinearMap
def Nut (i:ℕ)(E:Fin s→Type)[∀ i, NormedAddCommGroup (E i)][∀ i,NormedSpace ℝ (E i)]:Submodule ℝ (Mints E):={ carrier:={v|trims i v},zero_mem':=fun _ _=>rfl,add_mem':=trims.plus,smul_mem':=fun a _ ht=>trims.unit ht a }
abbrev KernNut (p:L!)(x:ℝ)(i:ℕ):= Fruition p x ⊓ Nut i E
local notation "X!"=>Ux p (μ k)
variable [∀ i,CompleteSpace (E i)][∀ i,CompleteSpace (G i)]
variable (h:Assist T p)(hk:k<d)(hr:∀ i,ShadeR (T i) (k+1) r)
include h hk hr
lemma sleeve : ∀ i:ℕ,i ≤ s→∀ z:S!,trims i ((X!^i) z) →∃ u:S!, trims i (z-u) ∧ u∈Fruition p (μ k):=by
    intro i hi; induction hi using Nat.decreasingInduction with
    | self=> exact fun z hz=>⟨z,(by rw [sub_self];exact fun _ _=>rfl),hz.limb⟩
    | of_succ i hi ih=>
         intro z hz; let j:Fin s:=⟨i,hi⟩; let P:= stride X! j; have ht:=xDeep (T j) (h.gait j) hk (hr _) ((X!^i) z j) i; rw [← byjack] at ht; obtain ⟨a,b,hy,hq⟩:= ht; let w:= Pi.single j b; let t:=z-w; have hp: Edgewise X!:= combe h.arum; have he:trims i ((X!^i) t):=(show trims i ((X!^i) (z-w)) from by rw [map_sub]; exact hz.sub (followPow hp i _ _ (nt j b))); have hx:(X!^i) t j=a:=by unfold t; rw [map_sub,Pi.sub_apply,snow hp j i (nt j _),hy,Pi.single_eq_same,add_sub_cancel_right]
         have hm: trims (i+1) ((X!^(i+1)) t):=by rw [pow_succ']; change trims _ (X! ((X!^i) t)); apply trims.up j (hp i _ he); rw [scissor hp j _ he,hx]; exact hq
         obtain ⟨u,hu,hh⟩:= ih _ hm; refine ⟨u,?_,hh⟩; rw [show z-u=w+(t-u) from by unfold t; abel]; exact (nt j b).plus (hu.drop (Nat.le_succ _))
variable (T)
lemma lifty (i:Fin s)(x:G k):∃ v:S!, v∈ KernNut p (μ k) i.val∧ (T i).Tap k (v i)= x:=by
     obtain ⟨u,hp,hu,hU⟩:= liftLayer _ (h.gait i) hk (hr i) x; let y:= Pi.single i u; have hy:y∈ Nut i.val E:=nt i u; have hA: trims (i.val+1) ((X!^(i.val+1)) y):=by
          have hx: Edgewise X!:= combe h.arum; apply trims.up i (followPow hx _ _ _ hy); rw [snow hx i (i.val+1) (show trims _ y from hy),byjack,pow_succ,byway,show y i=u from Pi.single_eq_same ..,hU,map_zero]
     obtain ⟨v,hv,hv'⟩:= sleeve (p:=p) h hk hr (i.val+1) i.isLt y hA; have hw: trims i.val v:=(show trims i.val v from by nth_rw 1 [show v=y-(y-v) from by abel]; exact (show trims i.val y from hy).sub (hv.drop (by omega)))
     have he:y i=v i:= sub_eq_zero.mp (hv i (by omega)); exact ⟨v,⟨hv',hw⟩,by rw [← he,show y i=u from Pi.single_eq_same ..];exact hu⟩
-- degree layer inject.
omit [∀ i, CompleteSpace (E i)] in
lemma jumpKnow (i:Fin s)(z:S!)(hz:z∈ Fruition p (μ k))(ht:trims i.val z): Ux (stride p i) (μ k) (z i)=0:=by
     apply kern (h.gait i) hk (hr _) s; rw [←byjack,← snow (combe h.arum) i s ht]; rw [show (X!^s) z=0 from hz]; rfl
omit hr [∀ i,CompleteSpace (E i)][∀ i, CompleteSpace (G i)] in
lemma phaseLeaf (i:Fin s)(z:S!)(hz:z∈ Fruition p (μ k))(ht:trims i.val z): z i∈ (T i).flag k:=by
     apply not_eig (h.gait i) hk _ s; rw [←byjack,← snow (combe h.arum) i s ht]; rw [show (X!^s) z=0 from hz]; rfl
omit [∀ i,CompleteSpace (E i)] in
lemma toss (i:Fin s)(z:S!)(hz:z∈ KernNut p (μ k) i.val)(he:(T i).Tap k (z i)=0): z∈ KernNut p (μ k) (i.val+1):=by
     obtain ⟨hz,hp⟩:= hz; exact ⟨hz,trims.up i hp (exitE (h.gait i) hk (hr _) (z i) (((T i).next k hk _).mpr ⟨phaseLeaf T h hk i z hz hp,he⟩) (jumpKnow T h hk hr _ z hz hp))⟩
end YM.OPE.Hark
