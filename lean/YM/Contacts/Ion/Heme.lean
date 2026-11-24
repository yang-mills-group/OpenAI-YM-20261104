import YM.Contacts.Ion.Borea
namespace YM.Contacts.Lyre
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Kale Garf PertExtension.Series Radial Larch Ion Convoy Lumen Resetter Shuttle.Tide
open Procession Procession.Welcome Procession.Catch Procession.Sun Procession.Lotus Procession.Hinges Procession.Xenon
open Shuttle.Pigment Prairie Harrier Sequent
open scoped Classical Topology BigOperators NNReal Matrix ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}{b c d g:ℝ}{X Y ι κ α β: Type}{m:Side}{n k i r l j M D:ℕ}{ζ σ:ℝ≥0}
open UVNext PricedKernels Next.Free Lattice Tree FreeResolvent
open PertExtension.Orb MeasureTheory
namespace Align
open Spark
-- No minimal size nor even period assumption for spin commutation; full chart. Measured hot is exactly its mirror (observed in orbit block before gauge).
variable {f:Side}(S:StepData m f)(h:Even f.val)
local notation "Λ"=> (SplitSpace (G:=G) S)
local notation "Θ" => (Forestry S)
local notation "Κ"=> (Precision.AxisChart G Θ)
local notation "L" => shineDance S
local notation "E"=> tribe S Θ
local notation "Ξ" => orderTurn Align.inverse
local notation "Σv"=> stash S Θ
open PertExtension.Chart Spark
lemma from_spot (hm:Even f.val){U V: Config G f}(hU:Halo U)(hV:Halo V)(hp:∀ i:orb f,U i.val=V i.val): U=V:= by
    funext i; obtain ⟨j,hj⟩:= (bar_slide hm).2 i; rw [←hj,double]; split; rw [hU,hV,hp]; exact hp _
local notation "σX"=> ContinuousLinearMap.comp (Σv) (L)
include h
lemma verdant (x:Λ): Halo (input G f (σX x)):= (unwrinkle _).mpr ( (flip_links Align.inverse _).trans (congr_arg _ (sight S h x)))
lemma prism_view (x:Λ): input G f (σX x)= banquet S (expLinks _ _ x):= by
   apply from_spot h (verdant S h x) (lift_flip h _); intro i; simp only [ContinuousLinearMap.comp_apply,stash_drape,lift_at]; by_cases hi:i.val∈(Θ).trunks
   · let t:Bark S:=⟨i,hi⟩; rw [show (Align.path S).symm (_,expLinks _ _ x) i= _ from slip_in S (G:=G) 1 (expLinks _ _ x) t]; exact (Θ).on_tree _ ⟨i.val,hi⟩
   let t: Rem S:=⟨i,hi⟩; change (Θ).drape (expLinks _ _ (L x)) (attic S t).val=_; rw [Forest.off_tree,show _=expLinks _ _ x t from slip_out S (G:=G) 1 (expLinks _ _ x) t]; unfold expLinks; rw [spot]
local notation "U" => Rem S
abbrev octave (p:U × Bool): (Θ).Free:= if p.2 then via S (attic S p.1) else attic S p.1
omit h in
lemma octave_val (v:U × Bool): (octave S v).val= Align.double (v.1.val,v.2):=by rcases v with ⟨i,h|h⟩<;> rfl
lemma nocturne : Bijective (octave S):= by
   constructor
   · rintro ⟨a,p⟩ ⟨b,q⟩ hh; have hx:= (bar_slide h).1 ((octave_val S (a,p)).symm.trans ((congr_arg Subtype.val hh).trans (octave_val S (b,q)))); exact Prod.ext (Subtype.ext (congr_arg Prod.fst hx)) (congr_arg (fun x:orb f × Bool=>x.2) hx)
   intro i; rcases bloom S i with hv|hv; exact ⟨(own S i,false),hv.symm⟩; exact ⟨(own S i,true),hv.symm⟩
lemma two_cash {P:ChartRatio G}(hx:LocalRatio P): ∀ᶠ y:Λ in 𝓝 0,∀ b:Link G m, Real.exp (gold P (weave S (b,σX y))/2)=jacobian P y/jacobian («U»:=Rem S) P 0:= by
   let F:= PertExtension.Chart.fee P; have hf:0<F 0:=fpos0 hx; let K:= Equiv.ofBijective (octave S) (nocturne S h); have hp (i:U) : ∀ᶠ y:Λ in 𝓝 0, y i∈ Metric.ball 0 P.radius ∧ 0<F (y i):= by
       have ht:∀ᶠ y:G.Color in 𝓝 0, y∈ Metric.ball 0 P.radius ∧ 0<F y:= (show ∀ᶠ y:G.Color in 𝓝 0, y∈ Metric.ball 0 P.radius from Metric.ball_mem_nhds _ hx.patch).and ((Ratio.fee_smooth hx).continuousAt.eventually (lt_mem_nhds hf)); exact (continuousAt_apply i (0:Λ)).eventually ht
   filter_upwards [eventually_all.mpr hp] with y hy b; change Real.exp (gold P (weave S (b,Σv (L y)))/2)=_; rw [scroll_gold, ←Equiv.sum_comp K, Fintype.sum_prod_type, Finset.sum_div, Real.exp_sum, jacobian, jacobian, ← Finset.prod_div_distrib]; apply Finset.prod_congr rfl; intro i _; rw [Fintype.sum_bool]; change Real.exp ((Real.log (F (L y (via S (attic S i)))/F 0)+Real.log (F (L y (attic S i))/F 0))/2)= _; rw [spot_neg S h,spot]; rw [show F (-y i)=F (y i) from (collected hx _ (hy i).1).symm]; change _= F (y i)/F 0; rw [show (Real.log _+Real.log _)/2=Real.log (F (y i)/F 0) from by ring, Real.exp_log (div_pos (hy i).2 hf)]
-- normalized single-epoch component at half invocation
local notation "Mx"=> Link G m
local notation "Φ" => Config G m
lemma vacant_wind (hw:S.patch.Branches S.kernel G) (H:Even m.val)(y:Mx)(hy:Ξ y=y)(x:Λ)(d:ℝ): noise S d (banquet S (expLinks _ _ x)) (input G m y)=Real.exp (-d*hot S (weave S (y,σX x))/2):= by
   let v:=expLinks _ _ x; let Y:= input G m y; let q:Entry G m:= fun i=>Y i.val; let Z:= banquet S v; let p:= (Align.path S).symm (1,v); have he : Y=liftLinks q:= from_spot H ((unwrinkle _).mpr ((flip_links Align.inverse y).trans (congr_arg (input G m) hy))) (lift_flip H q) (fun i=> (lift_at q i).symm)
   rw [hot_spec,Spark.grow,blooms, prism_view S h,noiseTaylor]; change noise S d (liftLinks p) Y = Real.exp (-d* (S.kernel.penalty * ∑ i,dawn S Z Y i)/2); rw [he,show noise S d (liftLinks p) (liftLinks q)= Real.exp (-d*S.kernel.penalty*orbitC S p q) from deliver ..,show (∑ i,dawn S Z (liftLinks q) i)=_ from estimate S hw p q H h]; congr 1; ring
end Align
end
end YM.Contacts.Lyre
