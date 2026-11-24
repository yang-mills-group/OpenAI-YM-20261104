import YM.OPE.Compatible.Sward.Tic
import YM.OPE.Compatible.Frog.Eye
/-!
# Wick drag on infinite support gauge frames, fixed period as chosen.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Silt.Phere
open Next.Free Bloch MeasureTheory Function Filter Finset Lattice Laurent Flume Flume.Script Flume.Page Precision Module Libra Shell Char RG Work.F08 Float
open scoped Topology BigOperators Classical
variable {I G K E F X:Type}{m r i j n k:ℕ}{C D:ℝ} {H:Gauge}
open Cloud JetS
open scoped ContDiff
variable {v y:fieldX (Shade H)}
open Tensor WardBin
-- budget C estimate.O. Use masks of bad axes
open Cascade Terp Paver Rill Shell FreeResolvent Exterior MSbar.Tree MSbar.Tree.Resolvent Frequency Streamer
open Votive
variable {N:Side}{L:KernelChoices} (x:Site N)
open Drift Shell Char
variable {τ :Char.Phase→ℕ}{d:ℕ}
open PertExtension Series GaussianScore
open Matrix
section
variable {P:Sponsor H}(v:Train r)(h:4 ≤ r)(hp:Aware d τ)
lemma noteP {a b:Seat k m I}(H:Deep (m:=m) a i)(hp:Deep (m:=m) b i): Deep (m:=m) (a-b) i:=fun j hj=>by rw[map_sub,Pi.sub_apply,H j hj,hp j hj,sub_self]
lemma hush (i:ℕ):Deep (I:=I) (k:=k) (m:=m) 0 i:=fun j _=>by rw[map_zero];rfl
lemma branchC {p q:Tower (Shade H) d τ}(ht:TrueRay (L:=L) v h p k)(hq: TrueRay (L:=L) v h q k): TrueRay (L:=L) v h (p-q) k:=by
       intro j; rw [Pi.sub_apply,map_sub]; exact noteP (ht j) (hq j)
-- inversion of orbit.Fil
lemma secs (x:Tracts H d τ)(hx: TrueRay (L:=P.K) v h (Fallix H hp P v h x).val k):ratios x k:=by
       let K:=fun (a:Tracts H d τ)=>(Fallix H hp P v h a).val
       let f(i:Phase):Prop:=Deep (m:=τ i) (x i).val (k+3*(2-i.val))
       have ht(a:ℕ):∀ i:Phase, i.val=a→ f i:=by
            induction a using Nat.strong_induction_on with
            | h a ih=>
               intro i hi; let y:Tracts H d τ:= fun p=> if p < i then x p else 0; have hg:ratios y k:=by
                    intro j; by_cases he:j < i; rw [show y j=x j from if_pos he]; exact ih j.val (hi ▸ Fin.lt_def.mp he) j rfl; rw [show y j=0 from if_neg he]; exact hush _
               have hy:= OrbitS (P:=P) v h hp y hg; let X:= x-y; have hP:TrueRay (L:=P.K) v h (K X) k:=by rw[show K X=K x-K y from by unfold X K; rw[map_sub];rfl]; exact branchC v h hx hy
               have hh:= starMark (K:=P) hp X v h i (show rare i X from fun j hj=>sub_eq_zero.mpr ((show y j=x j from if_pos hj).symm))
               have hz:= hP i; rw [show K X i= _ from hh.2, sustain,show X i=x i from by unfold X y; simp] at hz; exact hz
       exact fun i=> ht _ i rfl
end
end YM.OPE.Silt.Phere
