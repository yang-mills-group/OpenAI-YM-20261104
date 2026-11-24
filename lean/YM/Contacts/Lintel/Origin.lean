import YM.Contacts.Lintel.Rotor
namespace YM.Contacts.Lintel
set_option linter.unusedSectionVars false
set_option quotPrecheck false
open Function Set Finset Filter Metric RG Wilson Lattice Precision Exterior MeasureTheory
open Bloch Milling Milling.Steam Pulse Spine MergeProof Milling.Forge Laurent Stationary Matrix Work.F05
open Milling.Garf Form House PertExtension.Series Tree Larch FreeResolvent PhysicalNext.RankCovariance
open PertExtension.Chart Radial
open scoped Topology BigOperators Matrix Classical NNReal ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}{c f m: Side}{α:ℕ→Type}{n k:ℕ}
namespace Plata
open Crag Steam Lumen Resetter Ion Angle Convoy
namespace Rotor
open Barrage Barrage.Reserve Barrage.Slope
variable {K:Field (Fin 2) (Node (Dye G))} {F:PathData G}{P:Clip}{v w u b c A:ℝ} {s:ℝ≥0} {T:Bed}
variable (h:F.Bounds P u v w)(x:G.ColorIndex)
include h
lemma rises (hs:0<s)(ht:Poem K)(hh:Rooted (terrain s _) K b)(hp:∀ v,Mirrored (backpack v) K)(hv:∀ m,∀ y,jet (turnSeries F.loop (m:=m)) 2 y= design (printShadow K m) y): salvia G x K= 0:= by
   let V:= mask (G:=G) K; let L:= filing F; let M:=terraceP; have hV i j : V i j ∘ axes=L i j ∘ axes:= by
      let w j:= turnSeries (m:=M j) F.loop; ext1 p; obtain ⟨y,u,hU,hP⟩:= fleet M stepping (axes p) (axes_real p);
      have H (m:Side): Recorded V (turnSeries (m:=m) F.loop) 0:= Lumen.masked _ hh ht hp (turns_analytic _ h.width h.two) (hv m)
      exact tendsto_nhds_unique (Stationary.harvest (F:=w) (ε:=fun _=>0) (shadow_face _ _ hh hs) (fun i=> by simpa using H (M i)) tendsto_const_nhds p y u hU hP i j) (Stationary.harvest (F:=w) (ε:=fun _=>0) (fun i j=> ((filing_ready F h).1 i j).1) (fun i=> by simpa using (filing_ready F h).2 (M i)) tendsto_const_nhds p y u hU hP i j)
   let i: Ink G 2:= ![x,x]; let j: Run 2:=![coord 1,coord 1]; let p:Stationary.Track:= step (0:Axis); let t:= pressLens V i 1 1; have hh: t=(L i j ∘ axes) ∘ roads:= by change (V i j ∘ axes) ∘ roads=_; rw [hV]
   have hp := ((filing_ready F h).1 i j).1; have he : AnalyticAt ℝ t 0:= by rw [hh]; exact (hp.analytic_real _).comp (roads.analyticAt 0)
   have hz:Rays 4 t:= by rw [hh]; -- merkin accepts real⇒complex? merkin specialized ℝ; intro directly
                          intro p; change (fun v:ℝ=> ((L i j ∘ axes) ∘ roads) (v • p)) =O[cutRay] _; simp only [Function.comp_apply,map_smul]; exact ((filing_ready F h).1 i j).2 (roads p)
   change 2* (speedy t 2 p).re=_; unfold speedy Tensor.coeff; rw [ (rays_jet he _).1 hz _ (by norm_num : 2<4)]; simp [Tensor.diagonal]
variable {Y:bore G}{X:TableFee}
private lemma resolving_charged (hs:0<s)(hu:Roof s Y X)(hv:∀ m, Doric (hair Y m) (intended P F) (paye m A F P))(ht:Blazing Y T) (hk:Next.Free.Whole T.metric) (hf:T.metric.read 0=1)(hm:∀ m,(T.metric.acts m)ᵀ=T.metric.acts m) : salvia G x (Y 2 2)=A:= by
    let Q := Y 0 2; let V:= Y 2 2; let K:= V-A • Q; have hP:= (hu.shelter 0 2); have hT:=hu.shelter 2 2; have hA:= hP.smul A
    have hx: ∀ a:Cover, Mirrored (backpack a) K:= by intro a i; change V _- A*_=_; rw [show V _=_ from ht.frame.here a 2 2 i,show Q _=_ from ht.frame.here a 0 2 i]; rfl
    let hF (m:Side): Shadow (lower m) K (hair Y m 2 2- A • hair Y m 0 2) := by
       have hq i j: Shadow (lower m) (Y i j) (hair Y m i j):= printFeeds (heritage (fun p=> ht.frame.here p i j) m); unfold K; rw [sub_eq_add_neg V,sub_eq_add_neg (hair Y m 2 2)]; exact (hq 2 2).add (by simpa only [neg_one_smul] using (((hq 0 2).scale A).scale (-1))) hT hA.neg
    have hz m x : jet (turnSeries F.loop (m:=m)) 2 x=design (printShadow K m) x:= by
       have hop:= (hv m).after x; have hq:= (hv m).draw 2 le_rfl (by omega) x; let U m:= inputSeries P F (m:=m); let T m:= intended P F (m:=m); let Z:= design (hair Y m 0 2) x; change jet (paye m A F P) 2 x= design (hair Y m 2 2) x at hop; change jet (T m) 2 x=Z at hq; rw [focused (printFeeds (heritage hx m)) (lower_onto _) (hF m), parcel_sub,Convoy.design_scale,← hop]; let Q:=jet (U m) 2 x; have hl:jet (A • U m) 2 x=A * Q := by unfold Radial.jet Q; erw [iteratedFDeriv_const_smul_apply ((stain_knit F P h).analytic.contDiffAt (n:=((↑(2:ℕ)):WithTop ℕ∞)))]; unfold Radial.jet; change _*(A*_)=A*_; ring_nf; rfl -- similar
       rw [show paye m A F P=A • U m + turnSeries F.loop from funext fun x=> Rotor.paye_this A x, serif (show AnalyticAt ℝ (A • U m) 0 from AnalyticAt.const_smul (stain_knit F P h).analytic) _ (turns_analytic _ h.width h.two),hl]; change _= _-A*Z; rw [← hq,(show jet (T m) 2 x=Q from dial_input h ..)]; ring
    have he : salvia G x K= 0:= rises h x hs (show Poem K from (by unfold K; rw [sub_eq_add_neg]; exact (ht.frame.poem 2 2).add (((ht.frame.poem 0 2).scale A).minus))) (hT.sub hA) hx hz; unfold K V Q at he; rw [Oasis.charge_minus x hs hs hT hA, salvia_scale x hP hs,stark_cash hs hf ht hu hk hm] at he; linarith
lemma congruous (hs:0<s)(hu:Roof s Y X)(hv:∀ m, Doric (hair Y m) (intended P F) (paye m A F P))(ht:Blazing Y T) (hk:Next.Free.Whole T.metric) (hf:T.metric.read 0=1)(hm:∀ m,(T.metric.acts m)ᵀ=T.metric.acts m)(hZ: Platinum Y) :salvia G x (Y 2 2)=A ∧∀ m:Side, Orbit F (hair (lowerHouse (sink x Y) Y) m) P := by
   let W:=sink x Y; let Q:= lowerHouse W Y; obtain ha:= resolving_charged h x hs hu hv ht hk hf hm; refine ⟨ha,fun m=> ?_⟩; rw [precadence W hu ht.frame (sink_mast x)]; let R:= hair Y m; let Z:= lowerHouse W R; have hc(i j:ℕ)(v:Link G m): grate Z i j v= grate R i j v-∑ l∈Finset.range i,ticker W l i*grate Z l j v:= recaptured W R (sink_mast _) i j v
   change Doric Z _ _; refine ⟨fun j hj hp v=>?_, fun v=>?_ ⟩; · rw [hc, Finset.range_zero,sum_empty,sub_zero]; exact (hv m).draw _ hj hp v
   have hp : ticker W 1 2=0:= (charged W (sink_mast _) (sunk x Y hZ) 1 (i:=1) (by omega)); have hf:ticker W 0 2=A:= by unfold ticker charge pin W sink; rw [pow_zero,mul_one,PowerSeries.coeff_mk,if_neg (by decide),ha] -- Nat.sub
   let z:= inputSeries P F (m:=m); have he : jet (A • z) 2 v=A*jet z 2 v:= by unfold jet; erw [iteratedFDeriv_const_smul_apply ((stain_knit F P h).analytic.contDiffAt (n:=((↑(2:ℕ)):WithTop ℕ∞)))]; change _*(A*_) = A*_; ring_nf; rfl
   rw [hc, Finset.sum_range_succ,Finset.sum_range_succ,hp, zero_mul,Finset.range_zero,sum_empty,zero_add,add_zero, hf,hc 0]; rw [Finset.range_zero,sum_empty,sub_zero, show grate R 2 2 v = _ from ((hv m).after v).symm,show grate R 0 2 v=_ from ((hv m).draw 2 le_rfl (by omega) v).symm, dial_input h,show paye m A F P=A • z+turnSeries F.loop from rfl,serif (AnalyticAt.const_smul (show AnalyticAt ℝ z 0 from (stain_knit F P h).analytic)) _ (turns_analytic _ h.width h.two), he]; unfold z; ring -- paye equality `rfl` probable
end Rotor
end Plata
end
end YM.Contacts.Lintel
