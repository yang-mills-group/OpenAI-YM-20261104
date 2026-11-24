import YM.Contacts.Lintel.Angle
import YM.Next.STATIONARY.Shape.Scaled
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
set_option linter.unusedSectionVars false
variable {P:Clip}{Z:PathData G}{p:ℝ}{T:MapPrices}{B:Bed}{c v u w d:ℝ}
variable {n:Side}{Y:House (Lines G n 1)}
-- Front-office period assumption for real attempt at every phase
structure Dial (B:Bed)(P:Clip)(Z:PathData G)(n:Side):Prop where
   bounds : ∃ c v u,Z.Bounds P c v u
   sworn : Bid.Sworn B n G
   lin : Attached B Z
   state: ∃ c v, Floor B P n c v
lemma Dial.supports (h : Dial B P Z n): Rays 2 (intended (m:=n) P Z):= by
   obtain ⟨c,v,u,hc⟩:= h.bounds; obtain ⟨s,k,hs⟩:=h.state; have hp:= low_columns hc h.lin hs h.sworn; let f: Link G n→ℝ:=inputSeries P Z; have hx:= (stain_knit Z P hc (m:=n)).analytic; have he:Rays 2 f:=by
      refine (jet_bridge hx).2 (fun x i hi=> ?_); interval_cases i
      · exact (jet_zero ..).trans hp.1
      unfold jet; rw [iteratedFDeriv_one_apply,hp.2.1]; simp
   rw [intent]; exact (he.add ((turns_low _ hc.width hc.three).weaker (by decide :2≤3))).add ((turns_low _ hc.width hc.four).weaker (by decide))
lemma dial_input (h:Z.Bounds P w u v)(n:Side)(x:Link G n): jet (intended P Z) 2 x= jet (inputSeries P Z) 2 x := by
   let a:= (stain_knit Z P h (m:=n)).analytic; let b:= turns_analytic (m:=n) Z.cubic h.width h.three; let c:= turns_analytic (m:=n) Z.quartic h.width h.four; rw [intent,serif (a.add b) _ c,serif a _ b,(jet_bridge b).1 (turns_low _ _ h.three) x 2 (by decide),(jet_bridge c).1 (turns_low _ _ h.four) x 2 (by decide),add_zero,add_zero]; all_goals exact h.width
-- Snapshot on readers. Odd lanes absent/lower not presumed until applying; rank-specific
structure Doric (F:House (Lines G n 1))(A B:Link G n→ℝ): Prop where
    draw j (hi:2≤j)(hp:j≤4):∀ x, jet A j x= grate F 0 j x
    after : ∀ x, jet B 2 x=grate F 2 2 x
abbrev Orbit (Z:PathData G) (T: House (Lines G n 1))(P:Clip):Prop := Doric T (intended P Z) (turnSeries Z.loop)
private def mark (F U:Link G n→ℝ)(i:ℕ) : Link G n→ℝ:= if i=0 then F else if i=2 then U else fun _=>0
local notation "W" => Link G n
private lemma mark_s {F U:W→ℝ}(h:AnalyticAt ℝ F 0)(he:AnalyticAt ℝ U 0) (i:ℕ): AnalyticAt ℝ (mark F U i) 0:= by unfold mark; split_ifs <;> first|assumption| exact analyticAt_const
private lemma materialized (F U:W→ℝ): score F U=stake (mark F U) 5:= by ext x; simp [Ion.stake,sum_range_succ,mark,Crag.score,Ion.conjunct]
section Package
-- for a cradled Y
variable {Y:bore G}{k r:ℕ}
lemma mild_plat (h:Platinum Y)(n:Side) : Platinum (hair Y n):= fun i j hi=> by rw [hair,h i j hi, printLull]
lemma hair_quiet (A:Aegis x Y B)(n:Side)(h:G.Simple)(i r:ℕ)(hr:r < 2): hair Y n i r=0:= by
   interval_cases r; · unfold hair; rw [A.blazing.frame.scalar,printLull]
   obtain ⟨s,-,T,hT⟩:= A.price; rw [hair,rank_one h (should A.blazing) hT,printLull]
lemma material_integrable (hZ: Z.Bounds P w u v)(n:Side): Measurable (Function.uncurry (material (f:=n) P Z)):= by
    let U:= Config G n; have ht (r:ℕ)(F:ℕ→RG.Atom G r) : Measurable (fun x:U=>Precision.uncut F x):= Finset.measurable_fun_sum _ fun i _=> Measurable.tsum (fun j=> ((F j).unmasked_cont i).measurable)
    let L:= mainTerm P Z (n:=n); let Y:= (Precision.loop Z (n:=n)); have hp : Measurable L:= by
       let k(x: Config G n):= quadratic P Z x; have he : Measurable k:= by unfold k quadratic; apply Finset.measurable_fun_sum; intro x _; refine Measurable.add ?_ ((((Z.ell_meas _ P _ _ _ hZ).norm).pow_const (2:ℕ)).div_const _); exact measurable_const.mul (by unfold faceValue; fun_prop)
       exact (Finset.measurable_fun_sum _ (fun (i:Signed) _=> ((he.add (ht _ Z.cubic)).add (ht _ Z.quartic)).comp (continuous_pull i (0:Site n)).measurable)).const_mul _
    have he:Measurable Y:= (Finset.measurable_fun_sum _ fun (i:Signed) _=> (ht _ Z.loop).comp ((continuous_pull i (0:Site n)).measurable)).const_mul _; exact (hp.comp measurable_snd).add ((measurable_fst.pow_const _).mul (he.comp measurable_snd))
lemma packaging (h: Dial B P Z n)(he:G.Simple) {x:G.ColorIndex}(hp:Aegis x Y B)(hy : Orbit Z (hair Y n) P) : Package (n:=n) (material (G:=G) P Z) (hair Y n) 5:= by
   obtain ⟨s,t,q,hK⟩:=h.bounds; let A:W→ℝ:=intended P Z; let L:W→ℝ:=turnSeries Z.loop; have ha : AnalyticAt ℝ A 0:=(strain P Z hK).analytic; have ht:AnalyticAt ℝ L 0:=turns_analytic _ hK.width hK.two; let Y':=hair Y n; have hz : score A L=(fun x:ℝ × Link G n=> material P Z x.1 (input G n x.2)):= by ext x; unfold Crag.score conjunct; rw [pow_zero,one_mul]; rfl
   refine ⟨fun t u s=>?_ , fun t k U=>?_,material_integrable hK n,hz ▸ (score_s ha ht),?_⟩
   · unfold material; exact congr_arg₂ (·+·) (orbit_axis (fun x => quadratic P Z x + Precision.uncut Z.cubic x + Precision.uncut Z.quartic x) u s) (congr_arg (fun x:ℝ=>t^2*x) (orbit_axis (Precision.uncut Z.loop) u s)) -- [show mainTerm P Z (pull s 0 u)=_ from orbit_axis (fun x => quadratic P Z x + Precision.uncut Z.cubic x + Precision.uncut Z.quartic x) u s, show Precision.loop Z (pull s 0 u)=_ from orbit_axis (Precision.uncut Z.loop) u s]
   · unfold material; rw [Work.F05.mainTerm_gauge hK,Work.F05.loop_gauge hK]
   rw [←hz,materialized,swell]; have hs: ∀ i<5,Rays (5-i) ((mark A L - wind Y' 5) i) := by
      intro i hi; apply valued _ (mark_s ha ht _) (wind_ana Y' 5 i _) (fun x j hj=> ?_);
      rw [wind_jet,if_pos (by omega)]; by_cases hr: j < 2
      · suffices hx: Y'.grate i j x=0 by rw [hx,mark]; split; exact ((jet_bridge ha).1 h.supports x j hr); split; exact (jet_bridge ht).1 (turns_low _ hK.width hK.two) x j hr; exact Convoy.jet_empty j x
        unfold grate; split_ifs; rw [show Y' (i+j-2) j=0 from hair_quiet hp n he _ _ hr]; exact parcel_nil _; rfl
      unfold mark; split
      next hh => subst i; exact hy.draw j (by omega) (by omega) x
      split
      next hh=> have h': j=2:= (by omega); subst i j; exact hy.after x
      next ht h'=> rw [Convoy.jet_empty,grate,if_pos (by omega),show Y' (i+j-2) j=0 from mild_plat hp.grade n _ _ (by omega),parcel_nil]
   convert Ion.good_spaces (F:=mark A L-wind Y' 5) (fun i hi=> (mark_s ha ht i).sub (wind_ana ..)) hs using 1; funext z; simp only [Ion.stake,Ion.conjunct,Pi.sub_apply,mul_sub,Finset.sum_sub_distrib]; rfl
end Package
-- recover jets at the canonical graph (truncated to weight and through mandatory period projections)
lemma unveiled {T:House (Lines G n 1)} {F U:Link G n→ℝ} (h:Rays 5 (Crag.margin (swell T 5-score F U))) (hf:AnalyticAt ℝ F 0)(hu:AnalyticAt ℝ U 0): Doric T F U:= by
   let A i:= wind T 5 i - mark F U i; let B (i:ℕ):= A i - (fun x: Link G n=> A i 0); have hl k: AnalyticAt ℝ (A k) 0:= (wind_ana ..).sub (mark_s hf hu _); have ht : Rays 5 (Ion.stake B 5) := by
      rw [show Ion.stake B 5=Crag.margin ((swell T 5) - score F U) from ?_]; exact h; rw [materialized]; funext ⟨t,x⟩; unfold swell Crag.margin Ion.stake B A; simp only [Pi.sub_apply, ← Finset.sum_sub_distrib,conjunct]; apply sum_congr rfl; intro i _; ring
   have hv := contains (n:=5) (k:=5) (F:=B) (fun i hi=> (hl i).sub analyticAt_const) ht
   have hQ i (he:i<5) j (hy:j+i < 5) (hp:j≠0) (x:Link G n): jet (mark F U i) j x=grate T i j x:= by
      let f:=wind T 5 i; let g:=mark F U i; have hx:= (jet_bridge ((hl i).sub (analyticAt_const (v:=A i 0)))).1 (hv i he) x j (by omega); change jet (f - g - (fun _=> A i 0)) j x=_ at hx; rw [Ion.jet_minus _ _ _ _ (hl i) analyticAt_const,Ion.jet_minus f g _ _ (wind_ana ..) (mark_s hf hu ..),show jet f j x=_ from (wind_jet ..).trans (if_pos hy),show jet (fun _=> A i 0) j x=_ from (show jet (fun _=> A i 0) j x=0 from (by unfold jet; rw [iteratedFDeriv_const_of_ne hp]; simp)),sub_zero,sub_eq_zero] at hx; exact hx.symm
   refine ⟨fun j hj hp x=>?_ ,fun x=>?_⟩; simpa only [mark, if_pos rfl, ↓reduceIte] using hQ 0 (by decide) j (by omega) (by omega) x; simpa only [mark,if_neg (show (2:ℕ)≠0 by decide),if_pos rfl, ↓reduceIte] using hQ 2 (by decide) 2 (by decide) (by decide) x
variable {ψ:Side}{S: StepData ψ f}{P':Clip}{Z':PathData G} {g:G.Simple} {U:House (Lines G f 1)}{R:Spark.Astro G S}
local notation "B₁" => (planting S.ratio S.patch.odd_side)
variable {ρ:fieldDir G ψ 1→AxisChart G (planting S.ratio S.patch.odd_side)}{Ω:ChartRatio G}
lemma paid (A H:Bed)(hZ:Z.Bounds P w u v)(Q:Spark.Beam S G R A.metric H.metric d)(hb:S.patch.Branches S.kernel G)(h:LocalRatio Ω) (hp: Critical (B₁) P Z ρ)(hs: PriceGap (B₁) P Z b)(hf:0<b)(he: AnalyticAt ℝ (thermal B₁ (art S) P Z ρ Ω) 0) (hv: ClassicalMatch (B₁) P P' Z Z' ρ) (hh:Package (material (G:=G) P Z) U 5)(hC:Chest U A.metric) (hV: Dial H P' Z' ψ): let T:= Forge.vault S Ω U R A.metric H.metric; Doric T (intended P' Z') (Angle.rentV S P Z ρ Ω) := by
   intro T; let Pit:= classS (S:=S) P Z ρ; let u:= intended P' Z' (m:=ψ); let tax :Link G ψ→ℝ:=rentV S P Z ρ Ω; have hμ:= hv 2 (by decide) (art S); let Y:= arm G ψ 1; have ht : AnalyticAt ℝ Pit 0:= starts _ (hμ.1.analyticAt) Y.toContinuousLinearMap; have hU:AnalyticAt ℝ u 0:= starts _ hμ.2.1.analyticAt Y.toContinuousLinearMap; have h₁ : AnalyticAt ℝ tax 0:= starts _ he Y.toContinuousLinearMap
   have hg i (hi:i≤4) (x): jet Pit i x=jet u i x := by let a:= hv i hi (art S); let f:= fun x=>tested B₁ (art S) P Z x (ρ x); let z:=fun x:fieldDir G ψ 1=> mainTerm P' Z' (represent x); erw [show jet Pit i x=jet f i (Y x) from woven hμ.1.analyticAt (arm G ψ 1).toContinuousLinearMap x i,show jet u i x=jet z i (Y x) from woven hμ.2.1.analyticAt (arm G ψ 1).toContinuousLinearMap x i]; unfold jet; rw [show iteratedFDeriv ℝ i f 0=iteratedFDeriv ℝ i z 0 from a.2.2]; -- end
   have he : Doric T Pit tax:= unveiled (classical_ray (H:=A) (Q:=H) hZ hb h hp hs hf he hh Q ((jet_bridge ht).2 fun x i hi=> by rw [hg i (by omega)]; exact (jet_bridge hU).1 hV.supports x i hi) hC) ht h₁; exact ⟨fun j hj hp x=> (hg j hp x).symm.trans (he.draw _ hj hp _),he.after⟩ -- args
end Plata
end
end YM.Contacts.Lintel
