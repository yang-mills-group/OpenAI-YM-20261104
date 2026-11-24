import YM.Contacts.Procession.Clouds
/-! # One-mark projection at cover potential rank/timing. Keep coordinate economy phase-independent on shelves in this epoch. -/
noncomputable section
namespace YM.Contacts.Procession.Cartons
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix
open MeasureTheory Labels Source Drops Analysis Finset Bloch Laurent Push.AbsoluteSums Extra.Iteration MergeProof Next.Free Work.F08 Pulse Spine Origin
open Milling Milling.Steam Milling.Forge Milling.Garf Tensor MultiNext.SignedSource Pattern Shuttle Tide
open scoped Classical Topology BigOperators NNReal ENNReal Matrix ContDiff Matrix.Norms.Frobenius
open Morning Mediator Next.Foundations
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 90000
set_option autoImplicit false
variable {G:Gauge}{X Y: Type}{m:Side}{F:Cohort G}{d k h u n:ℕ}(B: Labels.Frame G d)
-- read on entire Mark.App.No power prices assumed.
private def admit (A: Directions G m): Link G m:= (arm G m 1).symm fun i=> A (i.1,axisEquiv.symm i.2)
private lemma admitD (v:ℕ) : ContDiff ℝ ω (admit (G:=G) (m:=m)):= by unfold admit; apply (arm G m 1).symm.contDiff.comp; fun_prop
lemma read_snap_rank (f:Config G m→ℝ)(hf:GaugeInvariant f)(hp:AnalyticAt ℝ (f ∘ input G m) 0)(H:Hol G) : ∃ p:B.Coeff, JetTest H 0 (B.coords.symm p) ((↑) ∘ f) := by -- `((↑) ∘ f)` syntax coercion
    let g:Config G m→ℂ:=fun x=> (f x:ℂ); have hz:(g ∘ increment 1)= Complex.ofRealCLM ∘ (f ∘ input G m) ∘ admit := by
       funext a; apply congr_arg (fun u:Config G m=> (f u:ℂ)); ext1 ⟨x,i⟩; rw [increment,Pi.one_apply,mul_one,encode_link]; unfold admit; rw [(arm G m 1).apply_symm_apply]; change _= G.lieExp (a (x,axisEquiv.symm (coord i))); rw [show axisEquiv.symm (coord i)=i from (axisEquiv.symm_apply_apply i)]
    have hx: ContDiffAt ℝ d (g ∘ increment 1) 0:= by rw [hz]; exact Complex.ofRealCLM.contDiff.contDiffAt.comp _ (ContDiffAt.comp _ (show ContDiffAt ℝ d (f ∘ input G m) (admit (0:Directions G m)) from (by rw [show admit (0:Directions G m)=0 from (by apply (arm G m 1).injective; unfold admit; rw [(arm G m 1).apply_symm_apply,map_zero]; rfl)]; exact (hp.contDiffAt (n:=ω)).of_le le_top)) ((admitD 0).contDiffAt.of_le le_top))
    obtain ⟨p,hp,hf'⟩:=read_projection H 0 d g (fun u U=> congr_arg ( (↑):ℝ→ℂ) (hf u U)) hx; exact ⟨B.coords p,by rw [B.coords.symm_apply_apply]; exact hp⟩
-- finite Demand Households
abbrev Channel (G:Gauge)(d:ℕ):= Push.Local.Probe G d
structure Decoder (B:Labels.Frame G d) where
    port: Finset (Channel G d)
    writes :(↥port→ℂ)→L[ℂ] B.Coeff
    linear (x:B.Coeff) : writes (fun i=>Push.Local.runProbe B i.val x)=x
def decoder : Decoder B:= by
    let K:= (Push.Local.probe_budget B).choose; let V:= (ContinuousLinearMap.pi (fun z:K=>Push.Local.runProbe B z.val)); have hx: LinearMap.ker V.toLinearMap = ⊥:= eq_bot_iff.mpr (by
        intro x hx; obtain ⟨C,h,hC⟩:= (Push.Local.probe_budget B).choose_spec; have ht:∀ i ∈K, Push.Local.runProbe B i x=0:= fun i hi=> congr_fun (show V x=0 from hx) (show ↥K from ⟨i,hi⟩); exact (show x=0 from norm_le_zero_iff.mp ((Push.Local.norm_le_size B x).trans ((hC x 0 le_rfl (fun i hi=>by rw [ht i hi,norm_zero])).trans_eq (mul_zero _)))))
    let H:= V.toLinearMap.exists_leftInverse_of_injective hx; refine ⟨K,H.choose.toContinuousLinearMap,fun x=>?_ ⟩; exact DFunLike.congr_fun H.choose_spec x
abbrev glide (J: Jet G)(d:ℕ)(t:ℝ) := trunk d (scaleJet J t)
lemma glide_ever (d:ℕ)(J:Jet G): ContDiff ℝ ω (glide J d):= by
    refine contDiff_pi.mpr fun i=> ?_; have he {F:Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (j:ℕ)(c:F): ContDiff ℝ ω (fun t:ℝ=> t^j • c):=(contDiff_id.pow _).smul contDiff_const; exact he (i.val+2) _
@[simp] lemma glide_zero (J:Jet G): glide J d 0=0:= funext fun i=>by simp [glide,trunk,scaleJet]
abbrev Rod (F:Cohort G)(d u n:ℕ) (J:Channel G d): ℝ:= iteratedDeriv J.2.val (panel F d u n ∘ glide J.1 d) 0
-- compare on sampling orbit, H test matches.Bidy
lemma ahead (f:Config G m→ℝ)(hh:GaugeInvariant f)(H:Hol G)(J:Jet G)(d:ℕ): (f ∘ H.testLinks d (0:Site m) J)=ᶠ[𝓝 0] ((f ∘ input G m) ∘ north (h:=d) H m) ∘ plank G d ∘ glide J d := by
    let x:ℝ→ Draft G d:= plank G d ∘ glide J d; have hx : x 0=0:= (by unfold x; simp); have hu:Tendsto x (𝓝 0) (𝓝 0):= hx ▸ ((plank G d).continuous.comp (glide_ever d J).continuous).tendsto 0
    refine ((native (d:=d) (m:=m) H hh).comp_tendsto hu).symm.mono fun i hi=> ?_; change _ = ((f ∘ input G m) ∘ north H m) (x i); rw [show _=_ from (show ((f ∘ input G m) ∘ north H m) (x i) = f (frameAt H m (x i)) from hi.symm)]; apply (Eq.trans (congr_arg f (test_scaled (d:=d) H 0 J i))); apply congr_arg f; funext j; unfold Hol.testLinks; rw [sub_zero]; rfl
lemma juice {P:ℕ→Side}(h:Tendsto (fun j=>(P j).val) atTop atTop)(H:Hol G){f:∀ n, Link G (P n) →ℝ}(hf:∀ n', Tide.Ticket (f n') F n)(ht:Tide.Felt F)(J:Jet G)(hk:k ≤n)(hp:k*(d+1)≤u):
      Tendsto (fun i=>iteratedDeriv k (((f i) ∘ north (h:=d) H (P i)) ∘ plank G d ∘ glide J d) 0) atTop (𝓝 (iteratedDeriv k (panel F d u n ∘ glide J d) 0)) := by
    let X:ℝ→Draft G d:= plank G d ∘ glide J d; have hx:X 0=0:= by unfold X; simp;
    let f' i:= (f i) ∘ north (h:=d) H (P i); let g:= room F d u n;
    have hF i: ContDiffAt ℝ ω (f' i) (X 0):= (by rw [hx]; refine ContDiffAt.comp _ ?_ (north_diff _ H d); rw [north_zero]; exact (hf i).clear.contDiffAt)
    have hH:ContDiffAt ℝ ω g (X 0):= by rw [hx]; exact ((rows_diff F u n).contDiffAt.comp _ (germ_rain ..));
    have hX:ContDiffAt ℝ ω X 0:= (ContinuousLinearMap.contDiff (plank G d)).contDiffAt.comp _ (glide_ever d J).contDiffAt; let A:Fin k→ℝ:= fun _=>1
    change Tendsto (fun i=> (iteratedFDeriv ℝ k (f' i ∘ X) 0) A) atTop (𝓝 (iteratedFDeriv ℝ k (g∘ X) 0 A)); have he:(k:WithTop ℕ∞)≤ω:=le_top; simp_rw [iteratedFDeriv_comp (hF _) hX he,iteratedFDeriv_comp hH hX he, FormalMultilinearSeries.taylorComp,_root_.sum_apply]; apply tendsto_finsetSum _ fun i _=> ?_; simp_rw [hx]; let v(j:Fin i.length):= iteratedFDeriv ℝ (i.partSize j) X 0 (A ∘ i.emb j); exact settlement H h ht v ((Nat.mul_le_mul_right _ i.length_le).trans hp) (i.length_le.trans hk) hf
-- fetch all
structure Shape (B:Labels.Frame G d)(Q:Snap G d→ℝ)(q:B.Coeff):Prop where
    read (J:Channel G d): Push.Local.runProbe B J q = ((iteratedDeriv J.2.val (Q∘ glide J.1 d) 0:ℝ):ℂ)
-- using real iterated deriv not complex→
def exhibit (Q:Snap G d→ℝ): B.Coeff:= (decoder B).writes (fun i=> ((iteratedDeriv i.val.2.val (Q∘ glide i.val.1 d) 0:ℝ):ℂ))
lemma Shape.won {Q:Snap G d→ℝ}{q:B.Coeff} (h:Shape B Q q): exhibit B Q=q:=by unfold exhibit; simp_rw [← h.read]; exact (decoder B).linear _ -- variable binder B explicit
lemma gauges (h:Tide.Tags F)(hq:d≤n)(hp:d*(d+1) ≤ u): Shape B (panel F d u n) (exhibit B (panel F d u n)):= by
   obtain ⟨H⟩:= Hol.exists_ode G; let A:= Barrage.Slope.terraceP; choose f Hf Hg HF using fun i=> h.oath (A i) n; choose q hQ using fun i:ℕ=> read_snap_rank B (f i) (Hg i) (HF i).clear H
   let X (i:Channel G d):ℂ:= Rod F d u n i
   have hm(i: Channel G d) : Tendsto (fun j=>Push.Local.runProbe B i (q j)) atTop (𝓝 (X i)):= by
       cases i with| mk J k=>
       have ht:= Nat.le_of_lt_succ k.isLt; let l:=k.val; let g (i:ℕ):= ((f i ∘ input G (A i)) ∘ north (h:=d) H (A i)) ∘ plank G d ∘ glide J d; refine (((Complex.ofRealCLM.continuous).tendsto (Rod F d u n (J,k))).comp (juice (k:=k.val) Barrage.Slope.stepping H HF h.toFelt J (ht.trans hq) ((Nat.mul_le_mul_right _ ht).trans hp))).congr (fun i=> ?_)
       erw [Push.Local.runProbe_eq]; rw [← (hQ i J).2.2 _ ht]; let u:= ahead (f i) (Hg i) H J d; have hx:(fun t=> ((f i (H.testLinks d 0 J t)):ℂ))=ᶠ[𝓝 0] Complex.ofRealCLM ∘ g i:= u.mono (fun i hi=> congr_arg Complex.ofRealCLM hi); have ht: ContDiffAt ℝ ω (g i) 0:= by
           let Y:= north (h:=d) H (A i); let U:ℝ→ Link G (A i):= Y ∘ plank G d ∘ glide J d; have hv : U 0=0:= by unfold U Y; simp only [Function.comp_apply,glide_zero,map_zero,north_zero]
           change ContDiffAt ℝ ω ((f i ∘ input G (A i)) ∘ U) 0; refine ContDiffAt.comp _ (by rw [hv]; exact (HF i).clear.contDiffAt) ?_; unfold U; refine ContDiffAt.comp _ ?_ ?_; swap; · exact ((plank G d).contDiff.comp (glide_ever d J)).contDiffAt
           simp only [Function.comp_apply,glide_zero,map_zero]; exact north_diff ..
       exact (DFunLike.congr_fun (Complex.ofRealCLM.iteratedFDeriv_comp_left ht (i:=k.val) le_top) (fun _=>1)).symm.trans (DFunLike.congr_fun (hx.iteratedFDeriv ℝ k.val|>.eq_of_nhds).symm (fun _=>1))
   have hx:Tendsto q atTop (𝓝 (exhibit B (panel F d u n))):= (((decoder B).writes.continuous|>.tendsto (fun i=> X i.val)).comp (tendsto_pi_nhds.mpr fun i=> hm i.val)).congr (fun i=> (decoder B).linear (q i))
   exact ⟨fun i=> tendsto_nhds_unique ((Push.Local.runProbe B i|>.continuous).continuousAt.tendsto.comp hx) (hm i)⟩
end YM.Contacts.Procession.Cartons
