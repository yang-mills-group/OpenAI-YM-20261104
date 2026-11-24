import YM.GradedFar.Aperture
/-!
# The lower margin at the common position probes

NOT just paying the clock from a different calibration position. Here t' used to
interrogate the fixed finite Fray estimates. Strict derivative uses THAT SAME t' in
both calls (same first Fray column purse).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Tariff.Ballot
open Function Filter Set PowerSeries MeasureTheory
open Extraction Table Spec PhysMS Trace.Pilot OPE OPE.Orbits
open FVA2 XSpace XSpace.Normalize XSpace.Structure1 FVA2.Scale FVA2.Scale.Facets FVA2.Scale.Equator FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh
open MS MS.Native MS.Land MS.Book MS.Book.Program MS.Book.Convolve MS.Fleet MS.Menus
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{Z: WilsonPrescription G}(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
variable {hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H:Main.Match Z hG M σ true)
variable {h:ℕ}
local notation "Sat"=> (Z.store.measure h)
local notation "V*"=> reference G h
local notation "X"=> guide G h
variable (Z)
lemma purse_goes (D:Fray (Z.store.measure h))(p:ℕ): Continuous (fun r:ℝ=> D.purse (goal Z M h p r)):= by
 unfold Fray.purse; refine continuous_pi fun i => continuous_pi fun j=>?_
 let W:Window G h:= ⟨(D.scope i).n,(D.scope i).t,fun l=> Module.finBasis ℝ (Sec G h) (j l)⟩
 change Continuous (fun x=> watch W (goal Z M h p x)); simp_rw [goal,map_sum,map_smul]; fun_prop
variable {Z}
lemma way_bill (D:Fray (Z.store.measure h))(P:Prediction G h)(v: Normalize.Change G h): D.itinerary (D.purse P,X v)= X ((Sat).D (recruit (stand v) P)):= by
 rw [D.way,Fray.box,LinearEquiv.symm_apply_apply]
include H
lemma sensation (D:Fray (Z.store.measure h)) (p:ℕ)(τ:ℝ→ℝ)(T:ℝ→Normalize.Change G h) (ht:Tendsto τ trail (𝓝 0))(hv:Tendsto
    (fun r=> X (T r)) trail (𝓝 0)):
    ∀ᶠ r in trail, ‖X (T r)‖≤ 2*‖ X ((Sat).D (Normalize.recruit (stand (T r)) (goal Z M h p (τ r))))-X ((Sat).D V*)‖:= by
 let A₀:=D.opening; let B(r:ℝ):= D.purse (goal Z M h p (τ r)); let v(r):=X (T r); let x(r:ℝ):= (B r,v r); let y(r:ℝ):=(B r,(0: MoveSpace G h))
 have hor:= (D.fair.hasStrictFDerivAt (x:=A₀) (by simp)).isLittleO
 have z:Tendsto B trail (𝓝 (D.purse V*)):= by rw [← goal_ground Z M H p]; exact ((purse_goes Z M D p).tendsto 0).comp ht
 have he:= (hor.comp_tendsto (show Tendsto (fun r=>(x r,y r)) trail (𝓝 (A₀,A₀)) from (z.prodMk_nhds hv).prodMk_nhds (z.prodMk_nhds tendsto_const_nhds))).bound (show 0<(1/2:ℝ) by norm_num)
 have hW:(Sat).Prepared:= Z.store.prepared h
 filter_upwards [he] with r hr; have hA : x r-y r=(0,v r):= by simp [x,y,Prod.mk_sub_mk]
 have hx : D.itinerary (x r)=X ((Sat).D (Normalize.recruit (stand (T r)) (goal Z M h p (τ r)))) := (way_bill D ..)
 have hy : D.itinerary (y r)= X ((Sat).D V*) := by
   unfold y B; rw [D.way, Fray.box, map_zero, stand0, Screen.recruit_one,goal_metric Z M H] -- Screen
 let f (r):= D.itinerary (x r)-D.itinerary (y r)
 change ‖f r-fderiv ℝ D.itinerary A₀ (x r-y r)‖≤ 1/2 *‖ x r-y r‖ at hr
 have hs:D.delta A₀=1:= D.unpin hW
 have ha (v:MoveSpace G h): fderiv ℝ D.itinerary A₀ (0,v)=v:= congrArg (fun z:MoveSpace G h→L[ℝ] MoveSpace G h=> z v) hs
 rw [hA,ha, Prod.norm_mk, norm_zero,max_eq_right (norm_nonneg _)] at hr
 rw [← hx, ← hy]; change ‖v r‖ ≤ 2 * ‖f r‖
 linarith only [hr,norm_le_norm_sub_add (v r) (f r), norm_sub_rev (f r) (v r)]
end YM.Integration.GradedFar.Tariff.Ballot
