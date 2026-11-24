import YM.OPE.Compatible.Grotto.Joice
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
local notation "F!"=> Fruition X (μ k)
omit [∀ i,CompleteSpace (E i)][FiniteDimensional ℝ (G k)] in
lemma still (z:Fin s)(p:H→ E z)(hh:∀ i,p i∈ (T z).flag k)(hw:0 ≤ w)(hp:Wealth p a w) : ∃ x:∀ i,Lingo r (L i), Wealth (fun i=>(x i).val) a w∧∀ i,trims z.val (x i).val ∧ (x i).val z=p i:=by
    obtain ⟨p,hP,hF⟩:= pests U.HP U.Yi.1 U.fits hw U.slope z p hp hh; have hx:= hP.place 0; obtain ⟨B,H,hT⟩:= hP; exact ⟨fun i=>⟨p i,B i,hT i⟩,hx,hF⟩ -- defeq
lemma lofty (hw:0 ≤ w)(i:ℕ)(hi:i ≤ s):∀ p:H→ F!,Wealth p a w→ (∀ j,trims i (p j).val)→ ∃ x:∀ j,Lingo r (L j),Wealth (fun j=> (x j).val) a w∧∀ j, U.PO j (x j)=p j ∧ trims i (x j).val:=by
    induction hi using Nat.decreasingInduction with
    | self=>
       refine fun p _ h=>⟨0,wealthZ a w,fun j=>⟨?_,fun _ _=>rfl⟩⟩; rw [Pi.zero_apply,map_zero]; exact Subtype.ext (h j).limb.symm
    | of_succ n hn ih=>
       intro p hp hQ; let z:Fin s:=⟨n,hn⟩; let q(i:H):= (p i).val z; have hZ(i):q i∈(T z).flag k:=phaseLeaf T U.HB U.mark z _ (p i).property (hQ _); obtain ⟨P0,hX,hh⟩:= still U z q hZ hw (aimW ((proj (φ:=E) (R:=ℝ) z) ∘L (F!).subtypeL) hp); have ht:= (Station U P0 hX hw).1; let y:=p-fun i=> U.PO i (P0 i);
       have hY:Wealth y a w:= subW U.fits hw hp (normDig ht (fun _=>le_rfl)); have hv(i): (y i).val ∈ KernNut X (μ k) (n+1):=by
           refine toss T U.HB U.mark U.chip z (y i).val ⟨(y i).property,(hQ i).sub (U.herald i z.val z.isLt.le (P0 i) (hh i).1)⟩ ?_; change (T z).Tap k ((p i).val z-(U.PO _ (P0 i)).val z)=0; rw [map_sub,keeps U _ _ _ (hh i).1,(hh i).2]; exact sub_self _
       obtain ⟨x,hx,hF⟩:= ih y hY fun i=> (hv i).2
       refine ⟨P0+x,fortSum hX hx U.fits hw,fun j=>⟨?_,?_⟩⟩; rw [Pi.add_apply,map_add,(hF j).1]; unfold y; rw [Pi.sub_apply]; abel; exact (hh j).1.plus ((hF j).2.drop (Nat.le_succ _))
lemma slotInv {J:Type}(x:J→ H)(j:J)(p:Lingo r (L (x j))) : U.PO (x j) p=(U.annex x).PO j p:=by
     obtain ⟨b,hb⟩:= (U.annex x).taleF j p; obtain ⟨c,hc⟩:=U.taleF (x j) p; exact portion U (x j) p.val _ _ _ b hc hb
lemma underW (hw:0≤ w)(x':H→F!)(hx: Wealth x' a w): ∃ y: ∀ i,Lingo r (L i), Wealth (fun i=> (y i).val) a w ∧ ∀ i,U.PO i (y i)=x' i:=by
     obtain ⟨p,hP,hF⟩:= lofty U hw 0 (by omega) x' hx fun _=> trims.be _; exact ⟨p,hP,fun i=>(hF i).1⟩
end Eave
end YM.OPE.Hark
