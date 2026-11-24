import YM.WilsonCoeffUV.Kinetic.Bridge
/-!
# Comparison of prescribed Kin alpha with the first Wn thermal

Finite Side interpolation uses costs by orientations **plus** Hess term,
full νΦ normalized. Consumes SeamPhase at previous level *only*, leaves
E input distinct. Doesn't assert alpha from beta-hand calibrations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Power.Roam
open Lattice Laurent Bloch Exterior Wilson Precision RG Function Filter
open Blue MeasureTheory Set Metric Matrix Gauge PowerSeries
open FreeResolvent Tree Stationary Cameo Bank Mosaic
open scoped ContDiff Topology BigOperators Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {c f n : Side}{G:Gauge}(S:StepData c f)(F:Forest S.ratio)
variable {ρ: fieldDir G c 1→ AxisChart G F}
variable {s A B :ℝ}{u:Clip}{R:PathData G}
variable (H Y:FreeResolvent.FaceRow)(Q: Matrix (Body 1 f) (Body 1 c) ℝ) {Ñ: ChartRatio G}
variable {Θ γ Λ α :ℝ}{T:PathData G}{w:Clip}

lemma smoothC (K:R.Bounds u s A B)(h:Critical F u R ρ)(q:FiniteBound F R T u w α Ñ ρ Θ γ Λ) (x: Inputs S Q (H.acts f) (Y.acts c))(b:IsUnit (treeMatrix G S F H).det) (p:S.patch.Branches S.kernel G)(g:LocalRatio Ñ)(e:(H.acts f).transpose= H.acts f) (v:front R u f 0=shine (orbQ (precisionC G f H))):
     0<(treeMatrix G S F H).det :=by
    let U:=treeMatrix G S F H
    let M:=extractV G S F Q
    have hM: M=reveal G S F*((reveal G S F).transpose*M):= sweeps G S F Q Y b x
    have hy:=fueled S F M K h hM p
    have hp: U.transpose=U:= by unfold U treeMatrix; rw [transpose_submatrix,full_symmetric _ e]
    have hx:= centerK U hy hp (dust_seed S F H Y Q g K x e p v).monic
    have hu:= (solid S F h).self_of_nhds; rw [hx] at hu; rw [map_zero,h.1] at hu
    have hh:= mem_of_mem_nhds (q.branch (tac S)); change 0< (hessian F (tac S) u R 0 (ρ 0)).det at hh
    rw [h.1] at hh; change 0<U.det; rwa [hu]

abbrev pointTherm (R:PathData G)(u:Clip)(ρ:fieldDir G c 1→AxisChart G F) (Ñ:ChartRatio G)(b:Link G c):= thermal F (tac S) u R ρ Ñ (arm G c 1 b)
lemma thermC (q:FiniteBound F R T u w α Ñ ρ Θ γ Λ): Green (pointTherm S F R u ρ Ñ):= ContDiffAt.comp (f:=arm G c 1) _ (by rw [map_zero]; exact q.born (tac S)) (arm G c 1).contDiff.contDiffAt
lemma cashM (c:Cost): Mist id (soil (U:=Woods G n) c):=by
   have he (i:Woods G n): Blue.brush i (soil c)=0:= by ext1 k; simp [Blue.brush,blot_apply,soil,coeff_map]
   exact ⟨fun i=>by change Dark _ (Blue.brush i _); rw [he]; exact Equal.refl _ _,fun i j=>by change Dark _ (Blue.brush i (Blue.brush j _)); rw [he,map_zero]; exact Equal.refl _ _⟩

lemma sundial (K:R.Bounds u s A B)(h:Critical F u R ρ)(q:FiniteBound F R T u w α Ñ ρ Θ γ Λ) (x: Inputs S Q (H.acts f) (Y.acts c))(b:IsUnit (treeMatrix G S F H).det) (p:S.patch.Branches S.kernel G)(g:LocalRatio Ñ)(e:(H.acts f).transpose= H.acts f)(v:front R u f 0=shine (orbQ (precisionC G f H))):
    let L:=front R u f; let P:=winter S F H Y Q Ñ L; let Φ:=baseP (pointRotor S F u R ρ)
    Mist id (Blue.flash P-(Blue.flash (sprig Φ 2)+jet (pointTherm S F R u ρ Ñ))) :=by
    intro L P Φ
    let U:=treeMatrix G S F H
    let M:=extractV G S F Q
    let f':=pointRotor S F u R ρ
    let G':= vigor S F Ñ R M ρ
    have hM: M=reveal G S F*((reveal G S F).transpose*M):= sweeps G S F Q Y b x
    have hy:= fueled S F M K h hM p; have hz:=vigors S F M K h g hM p
    have hp: U.transpose=U:= by unfold U treeMatrix; rw [transpose_submatrix, full_symmetric _ e]
    have hu :=smoothC S F H Y Q K h q x b p g e v
    obtain ⟨ht,hh⟩:=vane (dust_seed S F H Y Q g K x e p v) hy hp hu hz.1 hz.2.1 hz.2.2
    let c':= ((1:ℝ)/2*Real.log U.det)
    have he : jet (vineT f' G' - fun _=>c') = jet (pointTherm S F R u ρ Ñ) - realS c':=by
       have hv:Green (vineT f' G'):= vine_green hy.sta hz.1 (by rw [ht]; exact hu)
       rw [jet_sub hv (g:=fun _=> c') contDiffAt_const,jet_const]; exact congr_arg (·-realS c') (jet_congr (thermal_tip S F M K h hM g))
    let B:=orbC (precisionC G c Y); let W:=inside S F H Q Ñ L
    have hw : inside S F H Q Ñ L = Wick _ U⁻¹ (raiseE (shot S F Q Ñ L)):= by simp only [inside,treeInverse,resolve,zero_smul,add_zero]; rfl
    change Mist id (B-logOf (Wick _ U⁻¹ (raiseE (shot S F Q Ñ L)))-(_+jet (vineT f' G'-fun _=>c'))) at hh
    rw [← hw, he] at hh
    have hζ:Mist id (realS (U:=Woods G c) c'):= by apply Eq.subst ?_ (cashM (G:=G) (n:=c) (PowerSeries.C c')); unfold soil; rw [map_C]; rfl
    rw [show Blue.flash P=B- logOf W+soil (plugζ S Ñ) from winter_read S F H Y Q (stance K _) g p e (fun i=>shape_c K i f)]; convert! ((hh.add (cashM (G:=G) (n:=_) (plugζ S Ñ))).add hζ.neg) using 1; abel
lemma baseLink (x: Link G c): baseP (pointRotor S F u R ρ) x=tested F (tac S) u R (arm G c 1 x) (ρ (arm G c 1 x)):=by
    rw [baseP,Function.comp_apply,pointRotor,badge_base,show (sedan S F ρ (piIn x)).1 = ρ (arm G c 1 x) from ?_]
    change vcloth S F G 0+ρ (arm G c 1 x)=_; simp
lemma c_match (K: ClassicalMatch F u w R T ρ) (i:ℕ)(hi:i≤4):
    rye (baseP (pointRotor S F u R ρ)) i= rye (intended w T (m:=c)) i:=by
    let L: Lawn (Woods G c) →L[ℝ] fieldDir G c 1:= (arm G c 1).toContinuousLinearMap
    let x (y:fieldDir G c 1):= tested F (tac S) u R y (ρ y)
    let t (y:fieldDir G c 1):=mainTerm w T (represent y); have h: intended w T (m:=c)=t ∘ L:=rfl
    rcases K i hi (tac S) with ⟨H,Y,p⟩
    funext f; rw [show baseP (pointRotor S F u R ρ)=x ∘ L from funext fun p=> baseLink S F p]; simp_rw [h,rye,wired L (f:=x) (show AnalyticAt ℝ x (L 0) from by rw [map_zero]; exact H.analyticAt),wired L (f:=t) (show AnalyticAt ℝ t (L 0) from by rw [map_zero]; exact Y.analyticAt),map_zero,show iteratedFDeriv ℝ i x 0=iteratedFDeriv ℝ i t 0 from p]

-- η cutoff unknown from P

theorem tapestries (K:R.Bounds u s A B)(h:Critical F u R ρ)(q:FiniteBound F R T u w α Ñ ρ Θ γ Λ)(t:ClassicalMatch F u w R T ρ)
    (x:Inputs S Q (H.acts f) (Y.acts c))(b:IsUnit (treeMatrix G S F H).det)(p:S.patch.Branches S.kernel G)(g:LocalRatio Ñ)(e:(H.acts f).transpose=H.acts f) (hp:(Y.acts c).transpose=Y.acts c)(v:front R u f 0=shine (orbQ (precisionC G f H))):
    let P:=winter S F H Y Q Ñ (front R u f)
    (∀ i≤2,P i (2+i)=rye (intended w T (m:=c)) (2+i))∧ P 2 2= rye (pointTherm S F R u ρ Ñ) 2:=by
    intro P; let Φ := baseP (pointRotor S F u R ρ); let X:=pointTherm S F R u ρ Ñ
    let C:= sprig Φ 2; let D:=sprig X 0
    have hu:∀ i, Pure (P i):= fun i=> winter_pure S F H Y Q g p (fun j=>shape_c K j _) hp _
    have hv i: Pure ((P - (C+D)) i):= (hu i).sub ((sprig_pure _ (immersed (riderC S F h)) 2 i).add (sprig_pure _ (thermC S F q) 0 i))
    have he:shellK 2 P:=winter_band S F H Y Q g (stance K f)
    have hX:shellK 2 C:=sprig_count _ _; have hz:shellK 2 D:=fun i j h=>shine_dark (by omega)
    have hb: Mist id (Blue.flash (P-(C+D))):=by
        have hh : Blue.flash D=jet X:=by unfold D; rw [sprig_flash]; simp; rfl
        rw [flash_sub (finite_shell he) (finite_shell (shell_sum hX hz)),flash_add (finite_shell hX) (finite_shell hz),hh]; exact sundial S F H Y Q K h q x b p g e v
    have hr i k (p:i≤2)(q:2≤ k): P i k=(C+D) i k:=sub_eq_zero.mp (opaqueGain _ hb (shell_sub he (shell_sum hX hz)) hv i k p q)
    constructor
    · intro i p
      rw [hr i (2+i) p (by omega),Pi.add_apply,Pi.add_apply]; unfold C D Φ; rw [sprig,shine_lit]; unfold sprig
      rw [shine_dark (by omega),add_zero,c_match S F t _ (by omega)]
    rw [hr 2 2 le_rfl le_rfl,Pi.add_apply,Pi.add_apply]; unfold C D sprig; rw [shine_dark (by omega),zero_add,zero_add (2:ℕ),shine_lit]
end YM.WilsonCoeffUV.Power.Roam
