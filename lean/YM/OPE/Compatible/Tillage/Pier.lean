import YM.OPE.Compatible.Bowman.Teller
/-! # Linearity and loans -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Work.F05 Votive Tree
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{n c f L:Side}{P:Patch}{K:KernelChoices}{I J M:Type}{m k r d:ℕ}{σ C z:ℝ}
namespace Script
open Page Virgin Planned.PrimaryIntegral295.Carrier
section
variable [Fintype J] {T:Cross L I J} {p q:Script I r}
omit [Fintype J] in
lemma volVShape (p:Script I r)(T:Cross L I J)(u:ℝ): payVolume T (u • p) = u • payVolume T p:=by unfold payVolume; simp_rw [hoistS, silt_scale]; rw [Finset.smul_sum]
lemma volVAdd (h:Whole T)(hp:folk p)(hx:folk q): payVolume T (p+q)= payVolume T p+payVolume T q:=by
    unfold payVolume; simp_rw [hoist h _ (hp 0).choose_spec (hx 0).choose_spec, silt_add (wordAll T h p _ (folk_whole hp)) (wordAll T h q _ (folk_whole hx)), Finset.sum_add_distrib]
lemma volVSub (h:Whole T)(hp:folk p)(hx:folk q): payVolume T (p-q)=payVolume T p - payVolume T q:=by
   rw [sub_eq_add_neg,show -q=(-1:ℝ) • q by simp,volVAdd h hp (folkS hx _),volVShape]; simp [sub_eq_add_neg]
lemma folk_volP (h:Whole T)(hp:folk p):folk (payVolume T p):=fun i=>volume_bill _ h _ i (hp i).choose_spec
lemma raftV (p: Script I r)(T:Row I J)(u:ℝ): raft T (u • p)= u • raft T p:=volVShape p _ u
lemma raftPlus (T:Row I J)(h:Whole T)(hp:folk p)(hx:folk q):raft T (p+q)= raft T p+raft T q:=volVAdd (payact T h) hp hx
lemma raftSub (T:Row I J)(h:Whole T)(hp:folk p)(hx:folk q):raft T (p-q)= raft T p-raft T q:=volVSub (payact T h) hp hx
omit [Fintype J] in
lemma stitchSub (h:folk p)(hp:folk q):stitch (p-q)=stitch p-stitch q:=by unfold stitch; rw [bouquetSub,silt_sub]; exact sootS (adjusted (h 0).choose_spec); exact sootS (adjusted (hp 0).choose_spec)
omit [Fintype J] in
lemma stitchAdd (h:folk p)(hp:folk q):stitch (p+q)=stitch p+stitch q:= by apply sub_eq_iff_eq_add.mp; rw [← stitchSub (folkF h hp) hp]; simp
end
section
variable {p q:M→ Script I r}{X v:M→ℝ}
lemma Loan.debit (h:Loan m p v X)(hp:Loan m q v X)(hg:1≤X)(hv:0≤ v): Loan m (p-q) v X:= sub_eq_add_neg p q ▸ (h.seize hp.cut hg hv)
lemma Loan.fixed (p:Script I r)(h:folk p) : Loan m (fun _:M=>p) 1 X:=by obtain ⟨a,ha⟩:=h m; exact ⟨a,Sack.coins ha,0,fun i=>by simpa using ha⟩
lemma Loan.stamp (h:Loan m p v X): Loan m (fun i=> stitch (p i)) v X:= h.twirl.land
variable [Fintype J]
lemma Loan.plat (A: Cross L I J)(h:Whole A)(hh:Loan m p v X):Loan m (fun i=> payVolume A (p i)) v X:=by
    obtain ⟨c,hc,k,H⟩:= hh; obtain ⟨s,D,hs,hD⟩:=h; obtain ⟨v,hv,hx⟩:= pokeBill (I:=I) (J:=J) (L:=L) hs (le_max_right D 0) m r; exact ⟨v*c,mul_nonneg hv hc,k,fun i=>(hx A (strip_mono hD le_rfl (le_max_left ..)) _ _ (H i)).tips (le_of_eq (by ring))⟩ -- ..
lemma pay_ft (S:M→Cross L I J)(h:Tip σ S 1 X)(hc:0<σ)(hx:1≤X)(hp:0≤ v)(hh:Loan m p v X):Loan m (fun i=> payVolume (S i) (p i)) v X:=by
   let f (j:Site L)(i:M):= silt (countermove (S i) (lift j) (p i)); have ht:= Loan.count f (fun i=>Loan.land (clay _ h hh hx hc)) hx hp; rw [show (fun i=>payVolume _ (p i))= _ from funext fun j=>(Eq.symm (show (∑ i,f i) j=_ from Finset.sum_apply ..))]; exact ht
lemma pay_ss (S T:M→Cross L I J)(h:Tip σ S 1 X)(he:Tip σ T 1 X)(ha:Tip σ (S-T) v X)(ht:Loan m p 1 X)(hq: Loan m q 1 X)(hm:Loan m (p-q) v X)(hv:0<σ)(hh:1 ≤ X)(hy:∀ i,0<v i): Loan m (fun i=> payVolume (S i) (p i)-payVolume (T i) (q i)) v X:=by
   let f (j:Site L)(i:M):= silt (countermove (S i) (lift j) (p i))- silt (countermove (T i) (lift j) (q i)); have hz(j:Site L): Loan m (f j) v X:= by
       have hS:=clay (lift j) h ht hh hv; have hQ:= clay (lift j) he hq hh hv; have hf:= reachesC (lift j) h he ha ht hq hm hv hh hy; rw [show f j=(fun i=>silt (countermove (S i) (lift j) (p i)-countermove (T i) (lift j) (q i))) from funext fun i=>(silt_sub (sootS (hS.bill i).choose_spec) (sootS (hQ.bill i).choose_spec)).symm]; exact hf.land
   rw [show (fun i=> payVolume _ (p i)-payVolume _ (q i))=∑ i,f i from ?_]; exact Loan.count _ hz hh (fun i=>(hy i).le)
   ext1 i; rw [Finset.sum_apply, show (∑ j,f j i)= _ from Finset.sum_sub_distrib ..]; rfl
lemma pay_tt {S:M→Row I J}(h:Tip σ S 1 X)(hc:0<σ)(hx:1≤ X)(hp:0 ≤ v)(hh:Loan m p v X): Loan m (fun i=> raft (S i) (p i)) v X:=by
    refine pay_ft (fun i=> marry (S i)) ?_ hc hx hp hh; obtain ⟨c,a,B,h⟩:=h; exact ⟨c,a,B,fun i j k=> h i _ _⟩
lemma pay_ttδ {S T:M→Row I J}(h:Tip σ S 1 X)(he:Tip σ T 1 X)(ha:Tip σ (S-T) v X)(ht:Loan m p 1 X)(hq:Loan m q 1 X)(hm: Loan m (p-q) v X)(hv:0<σ)(hh:1 ≤ X)(hy:∀ i,0<v i): Loan m (fun i=>raft (S i) (p i) - raft (T i) (q i)) v X:=by
    refine pay_ss (fun i=>marry (S i)) (fun i=>marry (T i)) ?_ ?_ ?_ ht hq hm hv hh hy
    · obtain ⟨c,a,B,h⟩:=h; exact ⟨c,a,B,fun i j k=>h i _ _⟩
    · obtain ⟨c,a,B,h⟩:=he; exact ⟨c,a,B,fun i j k=>h i _ _⟩
    obtain ⟨c,a,B,h⟩:=ha; exact ⟨c,a,B,fun i j k=> h i j.2 k⟩
end
end Script
end YM.OPE.Flume
