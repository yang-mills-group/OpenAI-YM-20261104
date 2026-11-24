import YM.OPE.Compatible.Song.Focus
/-!
# Lower phase crops. Don't wash out ρ. costs included
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Merchant
open Function Filter MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset Tensor
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}
attribute [local instance] Gauge.frobInner
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Score
open Flock Libra.Shell Next.Foundations Weir Exterior Bloch Next.Free Frequency Streamer Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Variance StepsL Claw Prom Ibis
variable {i j d k m r l b:ℕ}{n:Side}
variable {I W:Type} {B:I→ Finset (Edge Cover)}{N:I→ Side}{φ:Filter I}{Z:I→ℝ}{p q: Forge G N}
open Quit.Jac
-- Cast correction shifts throwing above authorized rank(s)
noncomputable def LiftA (s:Phase)(p:Forge G N):Forge G N:= fun i x=> Ū^(s.val)*p i x
lemma fling (a:Phase) (p:Forge G N): eyeR (LiftA a p) a=eyeR p 0 :=by funext i x; fin_cases a<;> simp [eyeR, LiftA, pow_succ,Ū,JetS.seq] -- inspect
lemma early (a b:Phase)(p:Forge G N)(hv:b<a):eyeR (LiftA a p) b=0:=by funext i x; fin_cases a<;>fin_cases b<;> first| (exfalso; revert hv; decide)| (simp [eyeR,LiftA, pow_succ,Ū,JetS.seq])
lemma usually (a b t:Phase)(p:Forge G N)(h:t.val=b.val+a.val):eyeR (LiftA a p) t=eyeR p b:=by funext i x; fin_cases a<;>fin_cases b<;>fin_cases t<;> first| (exfalso;revert h;decide)| (simp [eyeR,LiftA, pow_succ,Ū,JetS.seq])
lemma vpFan (a:Phase)(h:Divining φ p): Divining φ (LiftA a p):=⟨h.he.mono fun _ hi=> prodMar (tor _) (staysP _ (Ū^a.val)) hi⟩
lemma Divining.zeroP: Divining φ (0:Forge G N):=⟨Eventually.of_forall fun _=> staysP _ _⟩
lemma Divining.sumB (h:Divining φ p)(hp:Divining φ q): Divining φ (p+q):=⟨(h.he.and hp.he).mono fun _ hi=> addMar _ hi.1 hi.2⟩
lemma Divining.subB (h:Divining φ p)(hp:Divining φ q): Divining φ (p-q):=by
       have he: ∀ᶠ i in φ,(tor (N i)).Marbles (fun x=> (- (1:Token))*(q i x)):= hp.he.mono fun i hi=> prodMar (tor (N i)) (staysP _ (- (1:Token))) hi; rw [sub_eq_add_neg]; apply h.sumB; constructor; filter_upwards [he] with i hi; have hu:(-q) i=(fun x=> (-(1:Token))*q i x):=(funext fun j=> by simp); rw [hu]; exact hi
variable (ht:Tendsto Z φ atTop)
namespace PlaneQ
include ht
lemma zoomP(a:Phase) (h:PlaneQ B φ Z p k)(hp:k ≤ d+a.val): PlaneQ B φ Z (LiftA a p) d:=by
       constructor; intro b; rcases lt_or_ge b a with hb|hb
       · rw [early a b p hb]; exact Filμ.empty ht
       have hz:a.val≤ b.val:= hb; let j:Phase:=⟨b.val-a.val, by have ht:= b.isLt; omega⟩; have hy:b.val=j.val+a.val:=by unfold j; dsimp only; omega
       rw [usually a j b _ hy]; exact Filμ.care (h.roll j) (by omega)
lemma empty : PlaneQ B φ Z (0:Forge G N) k:= by constructor; intro s; fin_cases s<;>exact Filμ.empty ht
lemma Shade (h:PlaneQ B φ Z p k)(hp:PlaneQ B φ Z q k):PlaneQ B φ Z (p+q) k:=by
        constructor; intro r; fin_cases r<;>first|exact ((h.roll 0).strike ht (hp.roll 0))|exact ((h.roll 1).strike ht (hp.roll 1))|exact ((h.roll 2).strike ht (hp.roll 2))
lemma shiftz (h:PlaneQ B φ Z p k)(hp:PlaneQ B φ Z q k):PlaneQ B φ Z (p-q) k:=by
        constructor; intro r; fin_cases r<;> first|exact Filμ.minus ht (h.roll 0) (hp.roll 0)|exact Filμ.minus ht (h.roll 1) (hp.roll 1)|exact Filμ.minus ht (h.roll 2) (hp.roll 2) -- sub vs?
omit ht in lemma pit (h:PlaneQ B φ Z p k)(hp:k≤ m):PlaneQ B φ Z p m:=⟨fun i=>Filμ.care (h.roll i) (by omega)⟩
lemma prod (h:PlaneQ B φ Z p k)(hp: PlaneQ B φ Z q d): PlaneQ B φ Z (p*q) (k+d):=by
       have he(i j s:Phase)(hv:i.val+j.val=s.val):Filμ B φ Z (eyeR p i * eyeR q j) (k+d+s.val):= ((h.roll i).mult (hp.roll j)).care (by omega)
       constructor; intro i; fin_cases i; exact he 0 0 0 rfl; exact Filμ.strike ht (he 0 1 1 rfl) (he 1 0 1 rfl); exact Filμ.strike ht (Filμ.strike ht (he 0 2 2 rfl) (he 1 1 2 rfl)) (he 2 0 2 rfl)
lemma totals (X:Finset W)(f:W→Forge G N)(h:∀ i∈X,PlaneQ B φ Z (f i) k):PlaneQ B φ Z (∑ i∈X,f i) k:=by
       induction X using Finset.induction_on with
       | empty=> rw[sum_empty];exact empty ht
       | insert i s hi ih=>rw [sum_insert hi]; exact Shade ht (h _ (mem_insert_self ..)) (ih (fun j hj=>h _ (mem_insert_of_mem hj)))
end PlaneQ
end YM.OPE.Merchant
