import YM.OPE.Compatible.Karls.Span
/-! # homogeneous crowns, going backwards. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function Filter Set ContinuousLinearMap Asymptotics
open scoped Topology BigOperators Classical
variable {d k i j s:ℕ}{E:Fin s→Type}{G:ℕ→Type}[∀ i,NormedAddCommGroup (E i)][∀ i,NormedSpace ℝ (E i)] [∀ i,NormedAddCommGroup (G i)] [∀ i,NormedSpace ℝ (G i)]
variable {b r x v u:ℝ}{μ:ℕ→ℝ}
local notation "S!"=> Mints E
variable {T:∀ i: Fin s,Cuts d μ v b (E i) G}
variable {p:(∀ i:Fin s,E i) →L[ℝ] (∀ i:Fin s,E i)}
open Drift
variable {H:Type}{L:H→ℕ→ Mints E→L[ℝ] Mints E}{W:Fin s→Type}{a w:H→ℝ}{f g:H→ℕ→ Mints E}
variable {P:ℕ→Mints E→L[ℝ] Mints E}{X:Mints E→L[ℝ] Mints E}
open Quit.PriceZ
variable [∀ i,CompleteSpace (E i)][∀ i,CompleteSpace (G i)][FiniteDimensional ℝ (G k)]
variable {q y e z:ℝ}
-- All.Life.Support
section
omit [∀ i,CompleteSpace (E i)][∀ i,CompleteSpace (G i)][FiniteDimensional ℝ (G k)]
variable (P:((Mints E)→L[ℝ] (Mints E)))(R:((Mints E)→L[ℝ] (Mints E))) {x:ℝ}
lemma SagaP (h:P*R=R*P):P*Ux R x=Ux R x*P:=by unfold Ux; rw [mul_sub,sub_mul,h,mul_smul_comm,mul_one,smul_mul_assoc x,one_mul]
def Fellow (x:ℝ)(h:P*R=R*P): Fruition R x→L[ℝ] Fruition R x:= ( P ∘L (Fruition R x).subtypeL).codRestrict _ (by
    intro i; change (Ux R x^s) (P i.val)=0; have hv:(Ux R x^s) i.val=0:= i.property; rw [← byway, ← (Commute.pow_right (show Commute P (Ux R x) from SagaP P R h) s).eq,byway,hv,map_zero])
lemma Fork (g:ℕ→ ((Mints E)→L[ℝ] (Mints E)))(hv:Tendsto g atTop (𝓝 X))(h:∀ i,P*g i=g i*P): P*X=X*P:=by apply tendsto_nhds_unique (a:=P*X) (b:=X*P) (f:=fun i=>P*g i) (hv.const_mul P); rw [show (fun i=>P*g i)= _ from funext h]; exact hv.mul_const P
end
namespace Eave
variable (K:Eave L X T a r q u k)(P:((Mints E)→L[ℝ] (Mints E)))(p:H)(hp:∀ i,P*(L p i)=(L p i)*P)(hs:u <1)
include K hs
omit [∀ i,CompleteSpace (E i)][∀ i,CompleteSpace (G i)][FiniteDimensional ℝ (G k)] in
lemma moves : Tendsto (L p) atTop (𝓝 X):=by
      obtain ⟨h,hV,H⟩:= K.Yi.2; have ht:= (tendsto_pow_atTop_nhds_zero_of_lt_one K.T2 hs).const_mul (h p); rw [mul_zero] at ht; have hh:Tendsto (fun i=>‖L p i-X‖) atTop (𝓝 0):= squeeze_zero (fun i=>norm_nonneg _) (H p) ht; exact tendsto_iff_norm_sub_tendsto_zero.mpr hh
include hp
omit [∀ i,CompleteSpace (E i)][∀ i,CompleteSpace (G i)][FiniteDimensional ℝ (G k)] in
lemma commX : P*X=X*P := Fork P (L p) (K.moves p hs) hp -- implicit ks
omit K hs
omit [∀ i,CompleteSpace (E i)] in
lemma racePin (x:S!):race (L p) 0 (P x) = fun i=> P (race (L p) 0 x i):=by
     funext i; induction i with
     | zero=>rfl
     | succ i ih=>
        let Q:= L p i; let y:= race (L p) 0 x i; have ht: L p i (race (L p) 0 (P x) i)=P (Q y):=by rw [ih]; exact DFunLike.congr_fun (hp i).symm _
        rw [propel, Pi.zero_apply,add_zero,ht,propel,Pi.zero_apply,add_zero]
local notation "Π"=> Lingo r (L p)
noncomputable def sailV : Lingo r (L p) →L[ℝ] Lingo r (L p):=(P.comp (Lingo r (L p)).subtypeL).codRestrict _ (fun i=>by obtain ⟨c,H⟩:=switchL i; refine ⟨‖P‖*c, ?_⟩; change Hex r (race (L p) 0 (P i.val)) _; rw [racePin _ p hp]; exact Hex.invoke P H)
include K hs
lemma ZUp (x:Lingo r (L p)) : K.PO p (sailV P p hp x)= Fellow P X (μ k) (K.commX P p hp hs) (K.PO p x):=by
      let J:= K.PO p; let z:= sailV P p hp x; let q':=J x; let A:= Fellow P X (μ k) (K.commX P p hp hs); obtain ⟨c,h⟩:= K.taleF p x; obtain ⟨b,H⟩:=K.taleF p z; refine K.portion p z.val (J z) (A q') b (‖P‖*c) H ?_; rw [show z.val=P x.val from rfl,racePin _ p hp]; have he : ((fun i=>P (race (L p) 0 x.val i))- tale X (A q').val)=(fun i=>P ((race (L p) 0 x.val i)-(tale X q'.val i))):=by
           funext i; have hv:= Commute.pow_right (show Commute P X from K.commX P p hp hs) i; rw [Pi.sub_apply]; unfold tale; rw [map_sub]; exact congr_arg (P _-·) (( DFunLike.congr_fun hv.eq q'.val).symm)
      rw [he]; exact Hex.invoke P h
end Eave
end YM.OPE.Hark
