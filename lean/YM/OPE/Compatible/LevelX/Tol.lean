import YM.OPE.Compatible.LevelX.Fond
/-!
# Ball top mean eta.
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
lemma stripOne {r:ℕ}(h:e-r≤m) (x:TagW G d e r):∃ p: Script (Shade G) r,∃ c,∃ hh:p∈cope G r m,∃ _hp:soot m p c, Brief p ∧ Bells p (e-r)∧ Flume.Script.tiller G r m (e-r) h d ⟨p,hh⟩=(coordinateQ G d e r).symm x :=by
      let A:= (coordinateQ G d e r).symm x; obtain ⟨p,hp,hE⟩:=crystal A.val; obtain ⟨c,hc⟩:=briefFee hp m; obtain ⟨hM,ht,hK⟩:=grammar A hc hE; refine ⟨p,c,⟨⟨c,hc⟩,ht,hK,hM⟩,hc,hp,graded_horizon A hc h hE,Subtype.ext ?_⟩; exact earns A hc h hE
lemma obtains (d:ℕ)(h:e ≤m)(hp:e≤k)(x:Bead G d e): ∃ p:bed G k m,p∈fillet G k m e (by omega) ∧ stepRead G d e k m h p=x:=by
      choose S C H hS hr Ht hx using fun i:Fin (e+1)=> stripOne (r:=i.val) (show e-i.val≤m by omega) (x i); let f:=∑ i:Fin (e+1),Shell.throw (S i)
      have ht(i:Fin (e+1)): f i.val=S i:=by
           unfold f; rw [Finset.sum_apply,sum_eq_single i]; exact Pi.single_eq_same _ _; exact fun j _ hj=> hubbub (Ne.symm (Fin.val_injective.ne hj)); simp
      have hh(i:ℕ)(hx:e < i): f i=0:=by unfold f; rw [Finset.sum_apply]; exact sum_eq_zero fun j _=> hubbub (by omega)
      let c:=∑ i,C i; have hc(i):0 ≤ C i:=Sack.coins (hS i); have hC :0 ≤ c:=sum_nonneg fun _ _=>hc _; have hg: Volume f k m c:=by
           refine ⟨fun i hi=>hh i (by omega),fun i=>?_⟩; by_cases hx:e < i; rw [hh i hx]; exact Sack.zero hC _; let j:Fin (e+1):=⟨i,by omega⟩; rw [show f i= S j from ht j]; exact (hS j).tips (single_le_sum (f:=C) (fun i _=>hc i) (mem_univ _))
      let u:=fundus f c hg; have hu:u∈bed G k m:=by intro i; rw [sproutsX]; by_cases hx:e < i; rw [hh _ hx]; exact Submodule.zero_mem _; let j:Fin (e+1):=⟨i,by omega⟩; erw [ht j]; exact H j
      let a:bed G k m:=⟨u,hu⟩; refine ⟨a,(decrement a).2 (fun i=>?_),funext fun i=>?_⟩
      · rw [show lilies _ _ _ a.val=f from sproutsX _ hg]; by_cases hx:e < i; rw [show e-i=0 by omega]; exact fun _ l hl=>by omega
        let j:Fin (e+1):=⟨i,by omega⟩; erw [ht j]; exact Ht j
      let E:= terrace G k m i.val; have he:E a=⟨S i,H i⟩:=Subtype.ext (show lilies m k _ u i.val=S i from (congr_fun (sproutsX _ hg) _).trans (ht i)); change coordinateQ G d e i.val (Flume.Script.tiller G i.val m (e-i.val) _ d (E a))= _; rw [he,hx i, LinearEquiv.apply_symm_apply]
end YM.OPE.Drift
