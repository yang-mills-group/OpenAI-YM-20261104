import YM.FormalBulk08.Turner.Way

/-! Exact re-fibration at each finite mesh. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Turner
open Series Wick Jets Orb Matrix Filter Set Function PowerSeries
open Stationary hiding Rays
open Lattice RG Precision Reef Work.F05 Tree MeasureTheory Wilson
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{c f:Side}{S:StepData c f}{F T: Forest S.ratio} {R: ChartRatio G}
open YM.AnalyticNext.QuarticMatch.Joint hiding power
open Flat
abbrev Globe (G:Gauge) (S:StepData c f)(F:Forest S.ratio):= Rays (Pine G S F ⊕ wire G c)
def frameD (e:F.Free≃T.Free) (x:Globe G S F): Globe G S T:= Sum.elim (thin e x) (x∘ Sum.inr)
def spins (G:Gauge)(c:Side)(x:Rays (wire G c)):=x
def yarn (_e:F.Free≃T.Free)(x:Globe G S F):= T.foldAt (input G f (winged F x))
lemma green (e:F.Free≃T.Free): ∀ᶠ x:Globe G S F in 𝓝 0,input G f (offer G T (thin e x))= Lattice.gauge (yarn e x) (input G f (winged F x)):= by
   filter_upwards [light_switch (G:=G) e] with x hx; unfold yarn winged at *; rw [sips,hx,sips]; exact Profiles.wears ..
lemma thin_jet (e:F.Free≃T.Free): ContDiffAt ℝ ω (thin (G:=G) e) 0:= contDiffAt_pi.mpr fun _=> contDiffAt_pi.mp (slick e) _
lemma thin_zero (e:F.Free≃T.Free): thin (G:=G) e 0=0:=by unfold thin;rw [track_zero];rfl
lemma frame_zero (e:F.Free≃T.Free): frameD (G:=G) e 0=0:= by unfold frameD; rw [thin_zero]; ext i; cases i<;>rfl
lemma frame_smooth (e:F.Free≃T.Free): ContDiffAt ℝ ω (frameD (G:=G) e) 0:= contDiffAt_pi.mpr fun i=> by cases i with
     | inl i=> exact contDiffAt_pi.mp (thin_jet e) i
     | inr i=> exact contDiffAt_apply ..
lemma scarf (e:F.Free≃T.Free)(x:Globe G S F): yarn e x ∘ S.ratio.embed=1:= by ext1 i; exact T.fold_root ..
lemma weekend (e:F.Free≃T.Free) (P:ChartRatio G) (h:LocalRatio P): abroad (pulse e) (Jets.halo (sap T P) (wire G c))= Jets.halo (sap F P) (wire G c):= by
    let f:= fun x:Rays (Pine G S F)=> x ∘ (pulse (G:=G) e).symm; have he: ContDiffAt ℝ ∞ f 0:= contDiffAt_pi.mpr fun _=>contDiffAt_apply ..
    have hX:sap F P=(sap T P) ∘ f:= funext fun x=> disparity e x P
    rw [hX]; simp_rw [Jets.halo,paste_steps _ f (sap_smooth T P h) he rfl, show roam ℝ _ _=_ from (show roam ℝ (motor f) (paste (sap T P))= tunnelP (pulse e).symm (paste (sap T P)) from fit_translate ..)]; unfold tunnelP; rw [←map_covelog (MvPolynomial.rename (⇑(pulse (G:=G) e).symm)).toRingHom (show coeff 0 (paste (sap T P))=1 from (by rw [paste_first,sap_root _ _ h,map_one]))] -- tunnelP rw issue
    ext1 n; unfold abroad tunnelP; rw [coeff_map, coeff_map,coeff_map,coeff_map]
    change MvPolynomial.rename _ (MvPolynomial.rename _ _) = MvPolynomial.rename _ (MvPolynomial.rename _ _)
    rw [MvPolynomial.rename_rename,MvPolynomial.rename_rename];rfl
lemma upwards (e:F.Free≃T.Free) (u: Pap (Pine G S T ⊕ wire G c)): dish (motor (track e)) (motor (spins G c)) (abroad (pulse e) u)=roam ℝ (motor (frameD e)) u:= by
    let f:= Equiv.sumCongr (pulse (G:=G) e) (Equiv.refl (wire G c)); let p:= Sum.elim (Sum.inl ∘ (pulse (G:=G) e).symm) (Sum.inr (α:=Pine G S F) (β:=wire G c))
    let z:=fun x: Globe G S F=> x ∘ p; have hsp : ContDiffAt ℝ ∞ (spins G c) 0:=contDiffAt_id
    let v:= hitch (track (G:=G) e) (spins G c)
    rw [hull_dish (track e) (spins G c) hsp rfl];change roam ℝ (motor v) _= _; rw [show (_) = roam ℝ (motor z) u from (show abroad (pulse e) u=roam ℝ (motor z) u from (fit_translate ..).symm), roam_compose]
    have hv : frameD (G:=G) e=z∘v:=by ext x i; cases i<;>rfl
    rw [hv, show (fun i=>roam ℝ _ _)=_ from (show (fun i=>roam ℝ (motor v) (motor z i))=motor (z∘v) from funext (motor_compose z v (contDiffAt_pi.mpr fun _=>contDiffAt_apply ..) (hitch_smooth _ _ ((slick e).of_le le_top) hsp) rfl (hitch_zero _ _ (track_zero _) rfl)))]
lemma upwards_sum (e:F.Free≃ T.Free)(u:Pap (Glob G c f)): dish (motor (track e)) (motor (spins G c)) (abroad (pulse e) (roam ℝ (motor (graft T)) u))= roam ℝ (motor (graft T ∘ frameD e)) u:= by rw [upwards,roam_compose,show (fun i=>roam ℝ _ _)=_ from funext (motor_compose (graft T) (frameD (G:=G) e) ((graft_receipt T).of_le le_top) ((frame_smooth e).of_le le_top) (graft_origin T) (frame_zero e))]
set_option maxHeartbeats 600000 in
lemma wing_view (e:F.Free≃T.Free)(p:Pap (wire G f))(hp : Rite p p 1 0) :
   dish (still (Pine G S F) (wire G c)) (motor (spins G c)) (seat F p)=dish (motor (track e)) (motor (spins G c)) (abroad (pulse e) (seat T p)) := by
    let y : Globe G S F→ Rays (Pine G S F):=fun x=> x ∘ Sum.inl
    have hy:ContDiffAt ℝ ω y 0:=contDiffAt_pi.mpr fun _=>contDiffAt_apply ..
    let v:= offer G T ∘ thin (G:=G) e
    have hV (U:Pap (wire G f)):dish (motor (track e)) (motor (spins G c)) (abroad (pulse e) (seat T U))=roam ℝ (motor v) U:= by
       rw [Reef.seat,upwards_sum]; unfold roam; rw [change_after,show (insertAt ℝ _).comp (MvPolynomial.rename Sum.inl).toRingHom=insertAt ℝ (motor v) from (?_)];
       ext
       case hC _ _ _=> simp
       case hX i n m=> simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,RingHom.coe_coe,MvPolynomial.rename_X,insert_X]; rfl
    rw [still_on, hV, drinking F y (spins G c) hy contDiffAt_id rfl rfl]
    apply hp (Pine G S F ⊕ wire G c) (offer G F ∘ y) v (yarn e) (map_zero _) (?_) ((offer G F).contDiff.contDiffAt.comp 0 hy) ((offer G T).contDiff.contDiffAt.comp 0 (thin_jet e)) (drape_lit S T (Army.powL (wing_service F))) (?_) (?_)
    · unfold v; rw [Function.comp_apply,thin_zero,map_zero]
    · refine ⟨1,funext fun i=>?_⟩; unfold yarn winged; rw [show (0:Rays (Pine G S F ⊕ wire G c)) ∘ Sum.inl=(0:Rays (Pine G S F)) from rfl] ; simp [Forest.foldAt]
    simp_rw [pull_id]; exact green e
lemma noise_view (e:F.Free≃T.Free)(k:S.Choices)(hp:S.patch.Branches S.kernel G) : dish (still (Pine G S F) (wire G c)) (motor (spins G c)) (roam ℝ (motor (graft F)) (noisePin S k))=dish (motor (track e)) (motor (spins G c)) (abroad (pulse e) (roam ℝ (motor (graft T)) (noisePin S k))) := by
    let y:Globe G S F→ Rays (Pine G S F):=fun x=> x ∘ Sum.inl; have hy :ContDiffAt ℝ ω y 0:=contDiffAt_pi.mpr fun _=>contDiffAt_apply ..
    let D:=hitch y (spins G c); have hv : D=id := by ext i j; cases j <;> rfl
    rw [still_on,dessert F y (spins G c) hy contDiffAt_id rfl rfl, show hitch y (spins G c)=id from hv, Function.comp_id,upwards_sum]; apply mul_left_cancel₀ (pow_ne_zero 2 X_ne_zero)
    let v:=frameD (G:=G) e; let q:=graft T ∘ v
    have hw : ContDiffAt ℝ ω q 0:= (show ContDiffAt ℝ ω _ (v 0) from ((show v 0=0 from frame_zero e).symm ▸ graft_receipt T)).comp 0 (frame_smooth e); have hq : q 0=0:=by unfold q v; rw [Function.comp_apply,frame_zero,graft_origin]
    have h (P: Globe G S F→Rays (Glob G c f)) : X^ (2:ℕ)*roam ℝ (motor P) (noisePin S k)= roam ℝ (motor P) (paste (clack S k)) := by rw [←salute S hp, roam,map_mul,map_pow,change_X]
    rw [h,h,←paste_steps (clack S k) q ((discord _ hp _).of_le le_top) (hw.of_le le_top) hq,←paste_steps (clack S k) (graft F) ((discord _ hp _).of_le le_top) ((graft_receipt F).of_le le_top) (graft_origin F)]
    apply paste_replace; filter_upwards [green (G:=G) e] with i ht; change groupEnergy _ (S.prediction (input G f _) _) _ = groupEnergy _ (S.prediction (input G f (offer G T (thin e i))) k) _
    rw [ht,predicted hp, scarf]; have he:Lattice.gauge (1:Site c→G.El) (S.prediction (input G f (winged F i)) k)=(S.prediction (input G f (winged F i)) k):= by ext1 i; simp [Lattice.gauge];
    rw [he];rfl
end YM.FormalBulk08.Turner
