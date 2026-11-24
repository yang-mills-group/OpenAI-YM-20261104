import YM.FormalBulk08.Reef.Safe
import YM.FormalBulk08.Turner.Route
import YM.Work.F05.Reindex

/-! Exact re-fibration at each finite mesh. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Turner
open Series Wick Jets Orb Matrix Filter Set Function PowerSeries
open Stationary hiding Rays
open Lattice RG Precision Reef Work.F05 Tree MeasureTheory Wilson
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{c f:Side}{S:StepData c f}{F T: Forest S.ratio} {R: ChartRatio G}
-- coordinates B(Fat), T(thin); e(old→thin)
def pulse (e:F.Free ≃ T.Free) : Pine G S F≃ Pine G S T:= (pines F).symm.trans ((Equiv.prodCongr e (Equiv.refl _)).trans (pines T))
lemma pulse_step (e:F.Free ≃ T.Free)(i:F.Free)(k:G.ColorIndex): pulse e (pines F (i,k))=pines T (e i,k):= by simp [pulse]
lemma pulse_link (e:F.Free ≃ T.Free) (x:Rays (Pine G S F))(i:F.Free): stand G T (x ∘ (pulse e).symm) (e i) = stand G F x i:= by
   ext1 u; change x _=x _; apply congr_arg x; exact (Equiv.symm_apply_eq ..).mpr (pulse_step _ _ _).symm
lemma pardon (e:F.Free ≃ T.Free) (x:Rays (Pine G S F))(i:F.Free): exposure T 0 (stand G T (x ∘ (pulse e).symm)) (e i)= exposure F 0 (stand G F x) i:= by simp [exposure,pulse_link, Precision.link_one,replica_one]
lemma disparity (e:F.Free ≃ T.Free) (x:Rays (Pine G S F))(P:ChartRatio G) : sap F P x=sap T P (x∘(pulse e).symm):= by unfold sap Work.F05.toll; exact Fintype.prod_equiv e _ _ fun i=>by rw [pulse_link]
-- orbit chart and repoke: *background* held at zero plane for absolute logs.
def track (e:F.Free≃ T.Free)(x:Rays (Pine G S F ⊕ wire G c)): Rays (Pine G S F):= (stand G F).symm (Work.F05.move e 0 (stand G F (x ∘ Sum.inl)))
def thin (e:F.Free≃ T.Free)(x:Rays (Pine G S F ⊕ wire G c)): Rays (Pine G S T):= track e x ∘ (pulse e).symm
lemma relocated (e:F.Free≃ T.Free)(x:Rays (Pine G S F⊕wire G c)): stand G T (thin e x)=Work.F05.switch F T 0 (stand G F (x ∘ Sum.inl)):= by
   rw [Work.F05.move_eq e]; unfold Function.comp; funext i; obtain ⟨i,rfl⟩:=e.surjective i
   rw [index_apply,thin,pulse_link,track];simp;rfl
lemma light_switch (e:F.Free≃ T.Free): ∀ᶠ x:Rays (Pine G S F⊕wire G c) in 𝓝 0, exposure T 0 (stand G T (thin e x))= Profiles.reroute F T G (exposure F 0 (stand G F (x∘Sum.inl))) := by
   have h:Tendsto (fun x:Rays (Pine G S F⊕wire G c)=>((0: Bid.Dir G c),stand G F (x∘Sum.inl))) (𝓝 0) (𝓝 0):=tendsto_const_nhds.prodMk_nhds (show Tendsto _ (𝓝 (0:Rays (Pine G S F⊕wire G c))) (𝓝 (0:AxisChart G F)) from ((map_zero (stand G F)): _=(0:AxisChart G F)) ▸ ((stand G F).continuous.tendsto _).comp (tendsto_pi_nhds.mpr (fun i=> (continuous_apply (Sum.inl i)).tendsto (0:Rays (Pine G S F⊕wire G c)))))
   filter_upwards [h.eventually (exposure_switch F T)] with x hx; rw [relocated]; exact hx
lemma real_lace (e:F.Free≃T.Free): MeasurePreserving (fun a:T.Slice G=>a ∘ e) (T.order G) (F.order G):= by
   let p:=MeasurableEquiv.piCongrLeft (fun _:F.Free=>G.El) e.symm
   have he:p=(p):=rfl
   have hr:(fun a:T.Slice G=>a ∘ e)= fun a=> p a:= by
        ext1 a; funext i; have h:p a (e.symm (e i))=a (e i):= Equiv.piCongrLeft_apply_apply _ _ _ _; rw [e.symm_apply_apply] at h;exact h.symm
   rw [hr]; exact measurePreserving_piCongrLeft (fun (_:F.Free)=> G.probHaar) e.symm
lemma slick (e:F.Free≃T.Free): ContDiffAt ℝ ω (track (G:=G) e) 0:= by
   unfold track; apply (stand G F).symm.contDiff.contDiffAt.comp (g:=fun x=>_) (0:Rays (Pine G S F⊕wire G c))
   let f:=fun x:Rays (Pine G S F⊕wire G c)=> ((0 : Bid.Dir G c),stand G F (x ∘ Sum.inl)); apply (show ContDiffAt ℝ ω (uncurry (Work.F05.move e)) (f 0) from (show f 0=0 from Prod.ext rfl (map_zero _)).symm ▸ (Work.F05.move_jet e)).comp 0 ?_; exact contDiffAt_const.prodMk ((stand G F).contDiff.contDiffAt.comp (f:=fun x:Rays (Pine G S F⊕wire G c)=> x ∘ Sum.inl) _ (contDiffAt_pi.mpr fun _=>contDiffAt_apply ..))
lemma track_zero (e:F.Free≃T.Free):track (G:=G) e 0=0:=by simp [track, show (0:Rays (Pine G S F⊕wire G c)) ∘ Sum.inl= (0:Rays (Pine G S F)) from rfl,Work.F05.move,Work.F05.switch_zero]
lemma brush (e:F.Free≃T.Free)(h:LocalRatio R): ∃ M:Matrix (Pine G S F) (Pine G S F) ℝ, dollars (track (G:=G) e) 0*M=1 ∧ ∀ᶠ z in 𝓝 0,sap F R (z∘ Sum.inl) = sap F R (track e z)*(M.det*(dollars (track e) z).det):=by
    let f:=fun (_:Rays (wire G c))(a:F.Slice G)=> Profiles.reroute F T G a ∘ e
    apply bread F R h (track (G:=G) e) f (fun _=> (real_lace e).comp (Profiles.spending F T G)) (fun _ x y hv=> ?_) _ (slick e |>.of_le le_top) (track_zero e)
    rotate_left
    any_goals
        apply (Profiles.reroute F T G).injective; ext1 i; obtain ⟨i,rfl⟩:=e.surjective i; exact congr_fun hv i
    filter_upwards [light_switch (G:=G) e] with x hx; ext1 i; exact (pardon e (track e x) i).symm.trans (congr_fun hx (e i)) -- definitional
end YM.FormalBulk08.Turner
