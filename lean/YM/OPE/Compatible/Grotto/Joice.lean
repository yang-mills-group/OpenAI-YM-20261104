import YM.OPE.Compatible.Grotto.Rich
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
open Drift
variable {H:Type}{L:H→ℕ→ Mints E→L[ℝ] Mints E}{W:Fin s→Type}{a w:H→ℝ}{f g:H→ℕ→ Mints E}
variable {X:Mints E→L[ℝ] Mints E}
namespace Eave
variable {θ:ℝ}(U:Eave L X T a r θ u k)
include U
variable [∀ i,CompleteSpace (E i)][∀ i,CompleteSpace (G i)][FiniteDimensional ℝ (G k)]
lemma Station (x:∀ i,Lingo r (L i))(hx:Wealth (fun i=>(x i).val) a w)(hw:0≤ w):
     let g(i):= (PO U i (x i)).val
     Wealth g a w∧ TameP θ a w (sprint L (fun i=>(x i).val)-Vapor X g):=by
          intro g; let p(i):=(x i).val; obtain ⟨y,hY,hF,hx'⟩:= backFolks U.fits hw U.Yi.2 U.HB U.slope U.T2 U.mark U.T1 U.chip (sprint L p) (speed U.HP U.fits hw U.Yi.1 U.slope p hx (fun i=>(x i).property)) fun _=> propel _ _; rw [show g=y from ?_]; exact ⟨hF,hx'⟩; funext i; obtain ⟨b,hb,hB⟩:= hx'; obtain ⟨c,hC⟩:= U.taleF i (x i); exact congr_arg Subtype.val (U.portion i (p i) _ ⟨y i,hY i⟩ _ _ hC (show Hex θ _ (b i) from hB i))
variable (j:H)
local notation "V!"=> Lingo r (L j)
local notation "S"=>stride X
lemma fruitsZ (x:V!) : U.PO j x=0↔ x.val∈Lingo θ (L j):=by
    constructor
    · intro he; obtain ⟨c,hc⟩:=U.taleF _ x; rw [he, show tale X (0:Fruition X (μ k)).val=0 from funext fun i=>map_zero (X^i),sub_zero] at hc; exact ⟨_,hc⟩
    intro hh; obtain ⟨c,hc⟩:=hh; obtain ⟨b,hx⟩:=U.taleF _ x; refine U.portion j x.val _ _ _ c hx ?_; rw [show tale X (0:Fruition X (μ k)).val=0 from funext fun i=>map_zero (X^i),sub_zero]; exact hc
lemma herald (i:ℕ)(hi:i≤s)(x:V!)(hp:trims i x.val):trims i (U.PO j x).val:=by
    let g:= race (L j) 0 x.val; let C:=U.PO j x; have hg(n):trims i (g n):= runsK (fun n=>(U.HP j n).arum) (propel _ _) hp n
    induction i with
    | zero=> exact trims.be _
    | succ i ih=>
       let u:Fin s:=⟨i,hi⟩; have hx:trims u.val C.val:= ih (by omega) (hp.drop (by omega)) fun n=> (hg n).drop (by omega); obtain ⟨b,hb⟩:= U.taleF j x; let p':=stride X u; have ht(i):tale X C.val i u=tale p' (C.val u) i:=snow U.HB.arum u i hx
       let Q:= proj (R:=ℝ) (φ:=E) u; apply trims.up u hx; refine Ipso (T:=p') (v:=C.val u) (show _ from (show (Ux p' (μ k) ^1) (C.val u)=0 from (by rw [pow_one]; exact jumpKnow T U.HB U.mark U.chip u C.val C.property hx))) U.trot U.ThetaPitch ⟨‖Q‖*b,?_⟩
       intro i'; have he:= hb.invoke Q i'; change ‖g i' u- tale X C.val i' u‖≤ _ at he; rw [ht, hg _ u (Nat.lt_succ_self i),zero_sub,norm_neg] at he; exact he
lemma keeps (i:Fin s)(x:V!)(hp:trims i.val x.val):
      (T i).Tap k ((U.PO j x).val i)= (T i).Tap k (x.val i):=by
          let y:=x.val; let z:=race (L j) 0 y; have hz:Run (gr L j i) (fun n=>z n i) 0:= runT (fun n=> (U.HP j n).arum) (propel _ _) i hp; let P:=U.PO j x; let f:= tale X P.val; have he:= herald U j i.val i.isLt.le x hp; have hF:Run (Ford (S i)) (fun n=> f n i) 0:= runT (fun _=> U.HB.arum) (TALE X P.val) i he; have hx:z 0 i ∈ (T i).flag k:=by -- syntax Y
               obtain ⟨c,H⟩:=x.property; exact inLayer (U.slope i).Fast (fun n=> (U.HP j n).gait i) hz U.mark.le (U.slope i).slow ((show Hex r z c from H).invoke (proj i))
          let C:= ((T i).Tap k)∘L (proj (R:=ℝ) (φ:=E) i); have hZ:= Run.tap hz (fun n=> (U.HP j n).gait i) U.mark hx; have hw':= Run.tap hF (fun _=> U.HB.gait i) U.mark (phaseLeaf T U.HB U.mark i _ P.property he); obtain ⟨a,ha⟩:= U.taleF j x; have hy :Hex θ ((fun b=>C (z b))-fun b=>C (f b)) (‖C‖*a):=by convert! ha.invoke C using 1; funext n; rw [Pi.sub_apply]; erw [map_sub]
          exact Eq.symm (sub_eq_zero.mp (show (T i).Tap k (z 0 i)-(T i).Tap k (f 0 i)=0 from det U.ThetaPitch U.trot (sub_zero (0:ℕ→ G k) ▸Run.sub hZ hw') hy))
end Eave
end YM.OPE.Hark
