import YM.OPE.Compatible.LevelX.View
/-!
# finite filtered read. unique moments modulo absent higher.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Drift
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Paver Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Pose Votive Alps Roles
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e t:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{v v':ℝ}{C:KernelChoices}{P:Patch}{R:ChartRatio G}{p:Clip}{b:ℝ}
local notation "B!"=> bed G k m
abbrev Bead (G:Gauge)(d e:ℕ) := (i:Fin (e+1)) → TagW G d e i.val
noncomputable def stepRead (G:Gauge)(d e k m:ℕ)(h:e≤m): bed G k m→L[ℝ] Bead G d e:=ContinuousLinearMap.pi (fun i=> { grasps G d e k m i.val ((Nat.sub_le ..).trans h) with cont:=alumni .. }) -- spr type order
noncomputable def fillet (G:Gauge)(k m e:ℕ)(h:e ≤m+1):Submodule ℝ (bed G k m):= ⨅ i:ℕ, (Hollow G i m (e-i) ((Nat.sub_le ..).trans h)).comap (terrace G k m i)
variable (h:e<m) (he:e≤d)
lemma decrement {h:e ≤ m+1}(p:B!) : p ∈ fillet G k m e h ↔ ∀ i:ℕ,Bells (lilies m k _ p.val i) (e-i):=by
     unfold fillet; rw [Submodule.mem_iInf];rfl
lemma dawn (p:B!) : p∈fillet G k m 0 (Nat.zero_le _):=(decrement _).mpr fun i x l hl=> by simp at hl
include h he
lemma slogan (p:B!)(hm:p∈ fillet G k m e (by omega)): ((stepRead G d e k m h.le) p=0) ↔ p∈ fillet G k m (e+1) (by omega):=by
     rw [decrement]; let g:= stepRead G d e k m h.le; have ht(i:Fin (e+1)): g p i=0 ↔ Bells (lilies m k _ p.val i.val) (e+1-i.val):=by
          let Z:= terrace G k m i.val p; let Q:= Flume.Script.tiller G i.val m (e-i.val) (by omega) d; let C:= coordinateQ G d e i.val; have hz:g p i=C (Q Z):=rfl; rw [hz,map_eq_zero_iff C C.injective]; rw [show (e+1-i.val)= (e-i.val)+1 by omega]; change Q Z=0 ↔ Bells Z.val _; rw [← (show honeyX Z.val (patent_till _) (show e-i.val≤m from by omega) d=0 ↔ _ from roll_inject _ _ (by omega) (by omega) ((patent Z).2.1) ((decrement p).1 hm i.val))] -- eq zero
          exact ⟨fun hx=>congr_arg Subtype.val hx, fun hx=>Subtype.ext hx⟩
     constructor
     · intro hx i; by_cases H:i<e+1; exact (ht ⟨_,H⟩).1 (congr_fun hx _); rw [show e+1-i=0 from Nat.sub_eq_zero_of_le (Nat.not_lt.mp H)]; intro i l hl; omega
     intro hg;exact funext fun i=> (ht i).2 (hg i.val)
include h he
omit h he in
lemma prev {h:e ≤ m+1}(p: bed G k m){hk:t ≤ m+1}(hj:e≤ t)(hh:p∈ fillet G k m t hk): p∈ fillet G k m e h:=(decrement p).2 fun i x l hl=>(decrement p).1 hh i x l (hl.trans_le (Nat.sub_le_sub_right hj i))
lemma downSector : IsClosed ((fillet G k m (e+1) (by omega)):Set (bed G k m)):=by
     let S:=fun i: Fin (e+1)=> stepRead G d i.val k m (by omega)
     suffices hk: ((fillet G k m (e+1) (by omega)):Set (bed G k m))= ⋂ i:Fin (e+1),{p| S i p=0} by rw [hk]; exact isClosed_iInter (fun i=> isClosed_eq (S i).continuous continuous_const)
     ext p; rw [Set.mem_iInter]; constructor
     · intro hP i; have H:p∈fillet G k m (e+1) (by omega):=hP; exact ((slogan (e:=i.val) (d:=d) (by omega) (by omega) p (prev p (by omega) H))|>.mpr (prev p (by omega) H)) -- he leaps
     intro hx; have hx' :∀ t:ℕ,∀ h':t≤ e+1,p∈fillet G k m t (by omega) :=by intro t h'; induction t with | zero=> exact dawn p| succ i ih=> exact (slogan (e:=i) (by omega) (d:=d) (by omega) p (ih (by omega))).1 (hx ⟨i,by omega⟩)
     exact hx' (e+1) le_rfl
end YM.OPE.Drift
