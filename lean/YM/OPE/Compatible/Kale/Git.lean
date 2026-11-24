import YM.OPE.Compatible.Kale.Sect
/-! # Finite leaders over the measured quotient.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Quit
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e t:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{v v':ℝ}{C:KernelChoices}{P:Patch}{R:ChartRatio G}{p:Clip}{b:ℝ}
open Hark Eave
lemma VliftPlus {p q:Seat k m I}(hp:Prairies.visit p)(hx:Prairies.visit q):Prairies.visit (p+q):=fun i=>by rw [map_add,Pi.add_apply]; exact plusA (hp i) (hx i)
lemma tailored {D:ℕ}(hp:D ≤ d)(hv:D ≤ k)(ht:D < m)(x:bed G k m):∃ p: bed G k m, x-p∈fillet G k m (D+1) (by omega) ∧ Prairies.visit p.val:=by
     induction D with
     | zero=>
       obtain ⟨p,hp,H,hx,hs⟩:= newV ht.le hv (stepRead G d 0 k m ht.le x)
       exact ⟨p, (slogan ht (d:=d) (Nat.zero_le _) _ (dawn (x-p))).1 (by rw [map_sub,H,sub_self]),hx⟩
     | succ n ih=>
        obtain ⟨p,hP,h⟩:=ih (show n≤d from by omega) (by omega) (by omega); obtain ⟨v,hy,hV,hx,hs⟩:= newV ht.le hv (stepRead G d (n+1) k m ht.le (x-p)); refine ⟨p+v,(show x-(p+v)=x-p-v from (sub_sub ..).symm) ▸ ?_, VliftPlus h hx⟩ -- `▸` reversal check
        exact (slogan ht hp _ (show x-p-v ∈ _ from Submodule.sub_mem _ hP hy)).1 (by rw [map_sub,hV,sub_self])
variable {u r' θ:ℝ}{X:Tracts G d τ →L[ℝ] Tracts G d τ}
variable {S:M→ ℕ→Tracts G d τ →L[ℝ] Tracts G d τ} {w:M→ℝ}
variable (ht:Stern K P τ k d v)(he:e≤k)(U:Eave S X (Turns ht) w r' θ u e) (p:M)
-- α.C
include ht he U
lemma stationF (a:Phase)(x: bed G (d+a.val) (τ a))(h:x∈ fillet G (d+a.val) (τ a) e (by have hx:= sternCap ht a;omega)):
     ∃ z:Lingo r' (S p), trims a.val z.val ∧ z.val a=x:=by
          let V:=U.annex (fun (_:Unit)=>p); have he:x∈(Drift.Turns ht a).flag e:=by simp only[Drift.Turns,tuneG,Nat.min_eq_left (show e≤k+1 by omega)]; exact h
          let f(_: Unit):=x; have hw : Wealth f (w∘fun _=> p) 1:=by refine ⟨‖x‖,norm_nonneg _,0,?_⟩; rintro ⟨⟩; simp [f]
          obtain ⟨R,hR,hZ⟩:= V.still a f (fun _=>he) (by simp : (0:Unit→ℝ) ≤ 1) hw; exact ⟨R (),hZ ()⟩
lemma station_brief (a:Phase)(x: bed G (d+a.val) (τ a))(h:x∈ fillet G (d+a.val) (τ a) e (by have hx:= sternCap ht a;omega))(hp: Prairies.visit x.val):
     ∃ z:Lingo r' (S p), trims a.val z.val ∧ z.val a=x ∧∀ i:Phase,Prairies.visit (z.val i).val:=by
          obtain ⟨Z,H,H'⟩:= stationF ht he U p a x h
          have hz(i:ℕ):∃ z:Lingo r' (S p), trims a.val z.val∧ z.val a=x∧∀ j:Phase,j.val< i→Prairies.visit (z.val j).val:=by
               induction i with
               | zero=> exact ⟨Z,H,H',fun j hj=>by omega⟩
               | succ i ih=>
                    obtain ⟨z,hs,hP,hY⟩:=ih; by_cases h:i<3; swap; · exact ⟨z,hs,hP,fun j hj=> hY j (by have hv:=j.isLt; omega)⟩
                    let b:Phase:=⟨i,h⟩; by_cases h': b≤a
                    · refine ⟨z,hs,hP, fun j hj=>?_⟩; by_cases ht:j=b;swap; · apply hY j; have hz:= Fin.val_injective.ne ht; change _≠ i at hz; omega
                      subst j; by_cases hx:a=b; subst a; rw [hP]; exact hp; rw [hs b (Fin.lt_def.mp (lt_of_le_of_ne h' (Ne.symm hx)))]; intro i; rw [Submodule.coe_zero,map_zero]; exact blankV
                    let y:=z.val b; have htS:=sternCap ht b
                    obtain ⟨v,hB,hv⟩:= tailored (D:=e) (show e≤ k from he) (show e≤ d+b.val from he.trans (ht.mark.trans (Nat.le_add_right ..))) (by omega) y
                    have hR:=prev (y-v) (Nat.le_succ e) hB (h:=show e≤τ b+1 by omega); obtain ⟨P',ht,H⟩:= stationF ht he U p b (y-v) hR; let l:=z-P'
                    have hx(j:Phase)(hp:j.val< i): (l.val j)= z.val j:=sub_eq_self.mpr (ht j (show j.val<b.val from hp))
                    have hr:l.val b=v:=by change z.val b-P'.val b=_; rw [H]; exact sub_sub_cancel ..
                    have hh: a.val< i:= Fin.lt_def.mp (lt_of_not_ge h'); exact ⟨l,fun k hk=>(hx k (lt_trans hk hh)).trans (hs k hk), (hx a hh).trans hP, fun k hk=>by
                       by_cases hv': k.val=i
                       · rw [show k=b from Fin.ext hv', hr]; exact hv
                       rw [hx k (by omega)]; exact hY k (by omega)⟩
          obtain ⟨z,Hz,hV,h'⟩:=hz 3; exact ⟨z,Hz,hV, fun i=> h' i i.isLt⟩
end YM.OPE.Quit
