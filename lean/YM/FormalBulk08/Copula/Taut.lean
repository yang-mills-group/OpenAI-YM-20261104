import YM.FormalBulk08.Copula.Bill
import YM.FormalBulk08.Turner.Bank

/-! Selfstanding recursion for constant block auxiliary scheme, with
coarse rooted outputs counted by number of steps down from top. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Copula
open Rial Series Wick Jets Orb Matrix Filter Function PowerSeries
open Lattice RG Laurent Precision Stationary Reef Flat Bank Mesa Lava City Wine Aster Dove Elm Quire Lotus Kemp Pose Roof Next.Free Bloch Source Source.Drops Labels
open scoped Topology ENNReal BigOperators ContDiff Classical
variable {G:Gauge}{A:Levels G}{K:KernelChoices}{ρ:ChartRatio G}{c f:Side}{d D i i' j j':ℕ}
variable (P:Patch)
def headV (T: Train P.J): Flight P.J P.J:= ⟨P.L,P.odd_side,P.coarse,P.order_cut,le_rfl,Nat.le_succ _,T⟩
def Diagram : ℕ→ Train P.J
   | 0=>Train.top _
   | n+1=> (headV P (Diagram n)).land

def flyP (n:ℕ) := headV P (Diagram P n)
variable (h:P.Branches K G) (a:hue G)
variable (ρ)
def campaign : ℕ→ Pot G
   | 0=> Enter G
   | n+1=> taxi ρ a (flyP P n) (routes _) h (campaign n)
def momentsK (n:ℕ): Pence:= Roof.epoch a (flyP P n) (routes _) K (campaign ρ P h a n) ρ h
variable (F:Frame G d)(T:SectionData F)(hd:d+1≤D)
lemma heightVk (P:Patch) : 2≤ P.L.val := le_trans (show _≤3 by decide) P.coarse
def Markbook : ℕ → Roof.Plaza F D
   | 0=> sectionY T hd
   | n+1=>avenue F ρ a (flyP P n) (routes _) h (heightVk P) (campaign ρ P h a n) (Markbook n)
def stageC(n:ℕ) : Tilework F := pTrain F ρ a (flyP P n) (routes _) h (heightVk P) (campaign ρ P h a n) (Markbook ρ P h a F T hd n)
-- contexts Keq
lemma taxis {X:Flight i j}{V:Flight i' j'}(p:i=i')(q:j=j')(u:X≍V)(hx:X.patch.Branches K G)(hv: V.patch.Branches K G)(W:Pot G): taxi ρ a X (routes _) hx W= taxi ρ a V (routes _) hv W:= by subst i;subst j;obtain rfl:=eq_of_heq u;rfl
lemma avenueTp {X:Flight i j}{V:Flight i' j'}(p:i=i')(q:j=j')(u:X≍V)(hx:X.patch.Branches K G)(hv: V.patch.Branches K G)(W:Pot G)(Y:Roof.Plaza F D): avenue F ρ a X (routes _) hx (heightVk X.patch) W Y=avenue F ρ a V (routes _) hv (heightVk V.patch) W Y ∧ pTrain F ρ a X (routes _) hx (heightVk X.patch) W Y= pTrain F ρ a V (routes _) hv (heightVk V.patch) W Y ∧epoch a X (routes _) K W ρ hx=epoch a V (routes _) K W ρ hv:= by subst i; subst j; obtain rfl:=eq_of_heq u; exact ⟨rfl,rfl,rfl⟩
lemma soloP {X:Flight i j}{V:Flight i' j'} (p:i=i')(q:j=j')(u:X≍V) : X.land≍V.land:=by subst i;subst j;obtain rfl:=eq_of_heq u;rfl
lemma hopP {X:Flight i j}{V:Flight i' j'} (p:i=i')(q:j=j')(r:X.L=V.L)(u:X.wing≍V.wing): X≍V := by
   subst i; subst j; obtain ⟨x,e,o,hx,hq,hc,w⟩:=X; obtain ⟨y,b,d,hk,hm,h',t⟩:=V; obtain rfl:x=y := r; obtain rfl:w=t:=eq_of_heq u; rfl
lemma topP (e:i=j): Train.top i ≍ Train.top j:= by rw [e]
structure Like (A: Levels G)(P:Patch)(N:ℕ): Prop where
    smoothing : ∀ i,i ≤ N → A.clock.J i=P.J
    madeL : ∀ i,i < N → A.S.block i=P.L
    kern : A.clock.kernel=K -- K implicit hidden since variable
variable {P} -- bad n
lemma constantV {m n:ℕ}(w:Like (K:=K) A P n)(i:ℕ) (h:i+m≤ n): flying A m i ≍ Diagram P m:= by
    induction m generalizing i with
    | zero=> rw [flying,Diagram]; exact topP (w.smoothing i (by omega))
    | succ m ih=>rw [flying, Diagram]; exact soloP (w.smoothing (i+1) (by omega)) (w.smoothing i (by omega)) (hopP (w.smoothing (i+1) (by omega)) (w.smoothing i (by omega)) (w.madeL i (by omega)) (ih (i+1) (by omega)))
lemma constantF {m n:ℕ}(w:Like (K:=K) A P n)(i:ℕ)(p:i+m<n): stageHop A i (flying A m (i+1))≍ flyP P m:= hopP (w.smoothing (i+1) (by omega)) (w.smoothing i (by omega)) (w.madeL i (by omega)) (constantV w (i+1) (by omega))
lemma constantP {m n:ℕ}(w:Like (K:=K) A P n)(u:∀ j,(A.clock.op j 0).patch.Branches K G)(i:ℕ)(v:i+m ≤ n): Dove.voyage A (fun _=>routes _) u ρ a m i=campaign ρ P h a m:=by
   induction m generalizing i with
   | zero=> rw [voyage,campaign]
   | succ m ih=> rw [voyage,campaign,ih (i+1) (by omega)]; exact taxis ρ a (w.smoothing _ (by omega)) (w.smoothing i (by omega)) (constantF w i (by omega)) _ h _
lemma constantT {m n:ℕ}(w:Like (K:=K) A P n)(u:∀ j,(A.clock.op j 0).patch.Branches K G)(i:ℕ)(v:i+m ≤ n): Elm.walkF ρ A (fun _=>routes _) u a F T hd m i= Markbook ρ P h a F T hd m:= by
   induction m generalizing i with
   | zero=>rw [walkF, Markbook]
   | succ m ih=>rw [walkF, Markbook,ih (i+1) (by omega),constantP _ h a w _ (i+1) (by omega)]; exact (avenueTp _ a F (w.smoothing _ (by omega)) (w.smoothing _ (by omega)) (constantF w i (by omega)) (u i) _ _ _).1
end YM.FormalBulk08.Copula
