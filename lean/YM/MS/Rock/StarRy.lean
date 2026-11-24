import YM.MS.Rock.Caps
/-!
# Evaluating the actual D-supported radial operator at integers

Version after embedding `ray`. Uses precisely volume consistent with splitting. This is part of the
 identity for Ward AND for the pole calculation: n=m=0 reduces to 4D normalization (after beta).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Rock.Path
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux
open Momentum Landau Arts Pilot Spin Arc Wire
open scoped Topology ContDiff
variable {G:Gauge}{I E F H J:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
 {m n k:ℕ}{z:UScale I}{a b : I→ℝ}{r:ℝ}
variable {U:Rip G}{F H:Mob G}{B:ℝ}{s:ℂ}{σ:Bool}
abbrev kPrice (F:Mob G): Prop:= fell 0 (fun _:Unit=> 1) (fun _=>F)
abbrev rPrice (U: Rip G): Prop:= rib 0 (fun _:Unit=>1) (fun _=>U)
lemma const_sc (p:ℝ): scaleC z 1 (fun _=>p):= ⟨max p 1,lt_max_of_lt_right zero_lt_one,0,fun i x _=> by simp⟩
variable [FiniteDimensional ℝ E]
variable (hf:kPrice F)(hu:rPrice U)(h:Sturdy σ F) (hv:Ruddy σ U)
include hf hu
lemma exact_test (W:Touch G m E)(s:ℂ): Ultra (wing s U F W):= by convert! sky (Z:=fun _:Unit=>s) (a:=fun _:Unit=>1) (b:=fun _:Unit=>1) (fun i=>const_sc ..) hf hu (fun _=>zero_le_one) W using 1; ext; simp -- type hp volume etc
lemma carpet_test (W:Touch G m E)(s:ℂ): Ultra (carpet (Px m) (wing s U F W)):= Arc.Q.Gquiet (Px m) (exact_test hf hu W s)
lemma theory (n:ℕ): Pass (U n) (F n) (Px n):= by
   intro l; let V:= sections (ContinuousLinearMap.id ℝ _) (ContinuousLinearMap.id ℝ _) (fun _=>rfl) hf hu (fun _=>zero_le_one) (ray l); have H := V.major (Reserve.cover (μ:= Px n) (Module.finrank ℝ (SectorP n) +1) (by omega)) (); simpa only [ContinuousLinearMap.id_apply, ray_sail] using H.values 1
include h hv
abbrev trueTr (U:Rip G)(F:Mob G)(m:ℕ) (q)(l):= trc (U m) q (F m) l
lemma lowN (l:Legs (Shore G m)) : ocean m U F m l= Arc.pitch m • Ccy (U m) (F m) (Px m) l:= by
    let W:= wing (m:ℂ) U F (ray l); let K:= carpet (Px m) W; have hx (x:SectorP m) : W ((x,0),1)=trueTr U F m x l:= by
        unfold W wing; simp only [Path.path,ray_sail,zero_smul,add_zero]; rw [trucks h hv, Wtr,Pi.add_apply,Pi.smul_apply, sub_self,mul_zero,zero_smul,add_zero]
    have hz := wing_mirror h hv (m:ℂ) (ray l); change coreC ( cloud m) m K 1=_; rw [core_static (carpet_test hf hu _ _) (mirror_r _ hz)]; change pitch m • carpet _ W _=_; unfold carpet; simp_rw [hx]
abbrev Flat (m n:ℕ):= EuclideanSpace ℝ (Apart m n)
omit hf hu h hv in
lemma sq_top (y:Flat m n): Momentum.sq (WithLp.ofLp y)=‖y‖^2:=by rw [inner_norm]; exact (Real.sq_sqrt (sq_nonnegative _)).symm -- nth
omit hf hu in
lemma face (ht:m< n)(x:SectorP m)(y:Flat m n)(l:Legs (Shore G m)): wing (n:ℂ) U F (ray l) ((x,‖y‖),1)=trueTr U F n ((cabs ht.le).symm (x,WithLp.ofLp y)) (Arts.lift ht.le l):= by
   let z:Momentum (Apart m n):= WithLp.ofLp y; let s:=step ht; have hu : Momentum.sq (‖y‖ • spray s)=Momentum.sq z:= by rw [scaling,sq_eq (spray s),zap,if_pos rfl,mul_one,sq_top] -- h parameters? `omit h` not done
   obtain ⟨K,hx,hs⟩:= Spin.fit ht.le (‖y‖ • spray s) z hu; let p:= slideA ht (x,‖y‖); let L:= (cabs ht.le).symm (x,z); have he : K.turn p=L:= by unfold p; rw [Path.path, map_add,hx,show ‖y‖ • spray (hatch ht)=Right ht.le (‖y‖ • spray s) from ?_, hs]; rfl; change _=sendB _ _ ; rw [map_smul,send_spray]; rfl
   unfold wing trueTr; simp only [ray_sail]; rw [tallyN h hv (Nat.succ_le_of_lt ht), slide_ext, lifts_link];
   have hM:=hv.turn n K (Spin.fixedLeft ht.le hx); obtain hV:=congr_fun ((hM.shuttle0 ..).trans (congr_arg (trc (U n) p) (h.turn n K (fixedLeft _ hx)))) (Arts.lift ht.le l); rw [beam_only ht.le K hx, show (flagS K G).volp p=L from he] at hV; exact hV.symm

lemma highN (ht:n=m+k+1)(l:Legs (Shore G m)) : ocean n U F m l=Arc.pitch n • Ccy (U n) (F n) (Px n) (Arts.lift (by omega : m≤n) l):= by
   have hr : m<n:= by omega; 
   haveI: Nonempty (Apart m n):= ⟨step hr⟩; have hT: Module.finrank ℝ (Flat m n)=2*(k+1):=by simp [Flat]; omega
   rw [ocean,spout,swoop,core_nat (carpet_test hf hu _ _) (mirror_r _ (wing_mirror h hv _ _)) (Flat m n) ht hT];
   let T:= fun p=>trc (U n) p (F n) (Arts.lift hr.le l)
   unfold carpet; dsimp only; simp_rw [face h hv hr]; congr 1; change (∫ p: Flat m n, ∫ x:SectorP m, T _ ∂Px m)=∫ q:SectorP n,T q ∂Px n
   let M: SectorP n≃ᵐ (SectorP m × Momentum (Apart m n)):= (cabs hr.le).toHomeomorph.toMeasurableEquiv; have hM : MeasurePreserving M volume (volume.prod volume):= cabs_measure hr.le;
   have ht : Integrable T volume:= theory hf hu n (Arts.lift hr.le l)
   let U:= MeasurableEquiv.toLp 2 (Apart m n→ℝ); let f:SectorP m × Momentum (Apart m n) →ℂ:=T ∘ M.symm
   unfold Px; calc
      _ = (∫ p:Momentum (Apart m n), (∫ x:SectorP m, f (x,p))):= (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Apart m n)).integral_comp' (fun p=> ∫ x:SectorP m,f (x,p))
      _ = ∫ p, f p ∂volume.prod volume := (integral_prod_symm f (hM.symm.integrable_comp_of_integrable ht)).symm
      _ = _ := hM.symm.integral_comp' T
lemma reg_proj (he:m≤n)(l:Legs (Shore G m)) : ocean n U F m l= Arc.pitch n • Ccy (U n) (F n) (Px n) (Arts.lift he l):= by
   obtain hl|hl:= lt_or_eq_of_le he; exact highN hf hu h hv (show n=m+(n-(m+1))+1 by omega) l; subst n; rw [lifts_id]; exact lowN hf hu h hv l
end YM.MS.Rock.Path
