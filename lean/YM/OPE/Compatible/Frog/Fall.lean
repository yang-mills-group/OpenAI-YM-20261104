import YM.OPE.Compatible.Frog.Alta
/-!
# Luminary topologies
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Drift
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Paver Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module
variable {n c f:Side}{I J:Type}{G:Gauge}{r i j d m l k:ℕ}{x:ℝ}
variable {τ:Phase→ℕ}
local notation "T!"=> Tower (Shade G) d τ
-- leading and billing
lemma green (h:Aware d τ) (x:Phase){p:Seat (d+x.val) (τ x) (Shade G)} (hp:p∈bed G (d+x.val) (τ x)): baby (τ:=τ) x p x=lilies (τ x) _ _ p ∧ ∀ t:Phase,t<x→ baby (τ:=τ) x p t=0:=by
      let D:= lilies (τ x) (d+x.val) (Shade G) p; have ht:= sproutV (τ x) _ p; let b:=baby (τ:=τ) x p
      constructor; swap; · intro i hi; unfold baby; rw [Finset.sum_apply]; exact Finset.sum_eq_zero fun _ _=> glide_nil _ hi
      have he(i:Fin (d+x.val+1)): glide (Grid.lance (D i.val)) x x=Shell.throw (D i.val):=by
           have h1:= merit hp i.val; rw [glide_me]; change Shell.throw (timbre ships (D i.val) i.val)=_; rw [frameO h1.1 h1.2.1 (ht.2 i.val) (he:=by have h:=h.credit x;have hx:=x.isLt;omega)]
      funext j; unfold baby; rw [Finset.sum_apply,Finset.sum_apply]; change (∑ i: Fin (d+x.val+1), glide (Grid.lance (D i.val)) x x j)=_; simp_rw [he]; by_cases hy:j< d+x.val+1
      · rw [Finset.sum_eq_single (⟨j,hy⟩:Fin (d+x.val+1))]; exact Pi.single_eq_same j _; exact fun u _ hu=> hubbub (Ne.symm (fun hz=>hu (Fin.ext hz))); simp
      rw [ht.1 _ (by omega)]; exact Finset.sum_eq_zero fun i _=>hubbub (by omega)
lemma youthful (G:Gauge)(h:Aware d τ)(x:Phase):∃ a:ℝ,0 ≤ a∧∀ (p:bed G (d+x.val) (τ x)),∀ i:Phase,Volume (baby (τ:=τ) x p.val i) (d+i.val) (if i=x then τ i else τ i+1) (a*‖p‖):=by
      let v:=d+x.val+1; choose c hc H using burst (G:=G) h x; let z(i:Phase):=∑ j,c j i; have hv(i):0≤z i:=Finset.sum_nonneg fun j _=> hc j i; refine ⟨∑ i,z i,Finset.sum_nonneg fun i _=>hv i,fun p i=>?_⟩
      let f:=baby (τ:=τ) x p.val; let X:= lilies (τ x) _ _ p.val; let q(j:Fin v):= glide (Grid.lance (X j.val)) x i; have hp(j:Fin v):Volume (q j) (d+i.val) (if i=x then τ i else τ i+1) (c j i*‖p‖):= H j i _ _ (merit p.property j.val).2.1 (merit p.property j.val).1 ((sproutV _ _ p.val).2 j.val)
      rw [show baby (τ:=τ) x p.val i=∑ j,q j from Finset.sum_apply ..]; apply Volume.raise _ (Volume.sum q (fun j=> c j i*‖p‖) Finset.univ (fun j _=>hp j)) le_rfl; rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (f:=z) (fun i _=>hv i) (Finset.mem_univ _)) (norm_nonneg _)
lemma War_glue (X: Finset I)(p:I→Muse G)(g:I→ℝ) (hp:∀ i∈X,Rainbow (p i)∧Pathic d (p i)∧ Tide (p i) d m (g i)): Rainbow (∑ i∈X,p i)∧ Pathic d (∑ i∈X,p i):=by
      induction X using Finset.induction_on with
      | empty=> simp only [Finset.sum_empty]; let τ:Phase→ℕ:=fun _=>0; rw [show (0:Muse G)=spread G d τ 0 from (map_zero _).symm]; exact (solar G d τ).zero_mem
      | insert i s hi ih=>
          obtain ⟨h,hP,hC⟩:= hp i (Finset.mem_insert_self ..); have he (i)(h:i∈s):= hp i (Finset.mem_insert_of_mem h); obtain ⟨hg,hK⟩:= ih he; have hZ:Tide (∑ i∈s,p i) d m (∑ i∈s,g i):=by
               intro j; rw [Finset.sum_apply]; exact Volume.sum (fun i=>p i j) g s (fun i hi=> (he i hi).2.2 j)
          rw [Finset.sum_insert hi]; refine ⟨bright h hg,fun n x=>?_⟩; rw [show inkM _ _ x= _ from funext fun i=>Ink_sum x i _ _ _ _ _ hC hZ]; exact addMar _ (hP _ _) (hK _ _)
lemma geared (G:Gauge)(h:Aware d τ)(x:Phase)(p:bed G (d+x.val) (τ x)): Rainbow (baby (τ:=τ) x p.val)∧ Pathic d (baby (τ:=τ) x p.val):=by
      let Y:=lilies (τ x) (d+x.val) _ p.val; let f(i:Fin (d+x.val+1)):= glide (Grid.lance (Y i.val)) x; have hp(z: ℕ): soot (τ x) (Y z) ‖p‖:=(sproutV _ _ p.val).2 z
      choose c hc H using burst (G:=G) h x; let u(j:Fin _):=∑ i,c j i; apply War_glue Finset.univ f (m:=0) (fun i=>u i*‖p‖); intro i _; obtain ⟨hz,ht,hh⟩:=merit p.property i.val; refine ⟨lancing _ _,glider _ x (Grid.duly (hp i.val) ?_ ?_ hh),fun j=>?_⟩
      · omega
      · have hv:=h.credit x; have hx:=x.isLt; omega
      obtain ⟨h1,h2⟩:=H i j (Y i.val) ‖p‖ ht hz (hp _); exact ⟨h1,fun k=> (soot_le_k _ _ (h2 k) (by omega : 0 ≤ _)).tips (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun j _=>hc i j) (Finset.mem_univ _)) (norm_nonneg _))⟩
end YM.OPE.Drift
