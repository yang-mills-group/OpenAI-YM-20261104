import YM.OPE.Compatible.Chain.Cans
/-! # Floated distinct only on eventual supports -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Terp
open Function Filter Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Matrix Score Libra Votive
open scoped Topology BigOperators ComplexConjugate Classical ContDiff
variable {G:Gauge}{n:Side}
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency Streamer Flume.Script Finset Metric
open PertExtension Series Asymptotics MSbar.Tree MSbar.Tree.Resolvent Further.FreeCovariance.KP GaussianScore Work.F06 Work.F08
variable {I:Type*}{l:Filter I}{K:I→Side}(u:(i:I)→Site (K i))(H:∀ i,Even (K i).val) (hk:Tendsto (fun i=>(K i).val) l atTop)
include hk
lemma pouring (p q:Edge Cover)(h:p≠q) : ∀ᶠ i in l, pathX (H i) (warpAt (u i) p)≠pathX (H i) (warpAt (u i) q):=by
    have hf : ∀ᶠ i in l, warpAt (u i) p≠warpAt (u i) q:=by
       let U:=2*(size p.1+size q.1); filter_upwards [hk.eventually (eventually_gt_atTop U)] with i (hz:U < _); intro e; apply h; unfold warpAt at e; rw [Prod.mk.injEq, add_right_inj] at e; refine Prod.ext ?_ e.2; rw [← size_centers (K i) p.1 le_rfl (by unfold U at hz; omega),e.1]; exact size_centers _ _ le_rfl (by unfold U at hz; omega)
    have hv(k:Kv):∀ᶠ i in l,k≠0 → warpAt (u i) p ≠ ferry k (warpAt (u i) q):= by
        by_cases ht:k=0
        · filter_upwards with i h; exact (h ht).elim
        filter_upwards [(images_gone u hk p q k ht).eventually (eventually_gt_atTop 0)] with i hi h e; rw [e] at hi; exact (not_lt_of_ge (Nat.le_of_eq (separation_self _))) hi
    filter_upwards [hf,eventually_all.mpr hv] with i hj hn; intro e; let x:=warpAt (u i) p; let y:= warpAt (u i) q; let k:= (edgesK (H i)).tick y; let j:= (edgesK (H i)).tick x; have ha: ferry j (pathX (H i) x).val=x:=(edgesK (H i)).ticket x; have ht:ferry k (pathX (H i) y).val=y:=(edgesK (H i)).ticket y; change pathX (H i) x=pathX (H i) y at e; rw [e] at ha
    have hr:ferry (j+k) y=x:=by
       rw [show ferry (j+k) y=ferry (j+k) (ferry k (pathX (H i) y).val) from congr_arg _ ht.symm, ← ferry_plus (H i), add_assoc,twinned,add_zero,ha]
    by_cases hy:j+k=0
    · rw [hy,ferry_0] at hr;exact hj hr.symm
    exact hn (j+k) hy hr.symm
lemma radIn {α:Type*}[Finite α](e: α→Edge Cover)(ht:Injective e) : ∀ᶠ i in l, Injective fun j=> pathX (H i) (warpAt (u i) (e j)):= by
    have h(j k:α):∀ᶠ i in l, pathX (H i) (warpAt (u i) (e j))=pathX (H i) (warpAt (u i) (e k))→ j=k:=by
        by_cases hp:j=k
        · exact Eventually.of_forall fun _ _=>hp
        exact (pouring u H hk _ _ (ht.ne hp)).mono fun i hi he=>(hi he).elim
    filter_upwards [eventually_all.mpr fun j=> eventually_all.mpr (h j)] with i hb using fun j k he=> hb j k he
end YM.OPE.Cascade.Terp
