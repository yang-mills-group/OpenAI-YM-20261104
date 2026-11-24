import YM.SignedWilsonExpansion.Kane.Finale
set_option autoImplicit false
set_option maxHeartbeats 480000
noncomputable section
namespace YM.SignedWilsonExpansion.Kane
open Function Filter Set Table Spec Climb Trace Trace.Pilot PhysMS PhysMS.Frame
open Extraction Order Spin Next.UVStress OPE OPE.Orbits Levy
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1 FVA2 Dframe FVA2.Scale.Level Future
open Belfry Belle Dancer Belfry.Crisis Belfry.Classroom Belfry.ScaleFits Commission
open scoped BigOperators Topology ContDiff Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)(W:ℝ→tower S)(L:Leading F W)
variable {b d e j n:ℕ}{ι:Type}{l:Filter ι}{g r ε:ι→ℝ}
namespace Tilted
open FVA2.Scale Belfry.Crisis Asymptotics Path
open MS MS.Land MS.Fleet MS.Native FVA2.Scale
/-!
### Smoothness & uniform fees for poses at the home radius. before negotiating thermal tick.
-/
open Dancer.Drawing Dancer.SeatsW
variable {Ξ:Type}{σ:Type}
namespace Iris
section payments
variable {P:Filter σ}{n:ℕ}{U:Set (Points n)}{Q₁ Q₂:σ→Points n→ℂ}{c:σ→ℂ}
structure Calm (P:Filter σ)(Q:σ→ Points n→ℂ)(U:Set (Points n)):Prop where
   smooth : ∀ᶠ i in P,∀ x∈U,ContDiffAt ℝ ∞ (Q i) x
   cost (m:ℕ) : ∃ C:ℝ, 0≤ C ∧ ∀ᶠ i in P,∀ x∈ U,‖iteratedFDeriv ℝ m (Q i) x‖≤ C
private lemma n_le (k:ℕ) : (k:WithTop ℕ∞)≤ ∞:=WithTop.coe_le_coe.mpr le_top
lemma tally {f:σ→ℂ}(p:f=O[P] (1:σ→ℝ)):∃ C:ℝ,0≤ C ∧ ∀ᶠ i in P,‖f i‖≤C:=by
    obtain ⟨k,h⟩:= isBigO_iff.mp p; exact ⟨|k|, abs_nonneg _, h.mono fun i hi=> (show ‖f i‖≤ k by simpa using hi).trans ( le_abs_self .. ) ⟩
lemma add (h:Calm P Q₁ U)(p: Calm P Q₂ U): Calm P (Q₁+Q₂) U:=by
   refine ⟨ ( h.smooth.and p.smooth ).mono fun i hi x hx=> ( hi.1 x hx ).add ( hi.2 x hx ),fun m=>?_⟩; obtain ⟨a,ha,h'⟩:= h.cost m; obtain ⟨b,hb,p'⟩:= p.cost m; refine ⟨ a+b, add_nonneg ha hb,?_ ⟩; filter_upwards [ h',p',h.smooth,p.smooth ] with i hi hv hX hY x hx; rw [Pi.add_apply,iteratedFDeriv_add_apply (( hX x hx ).of_le (n_le _)) (( hY x hx ).of_le (n_le _))]; exact ( norm_add_le .. ).trans (add_le_add ( hi x hx ) ( hv x hx ))
lemma scale (h: Calm P Q₁ U)(p:c=O[P] (1:σ→ℝ)): Calm P (fun i=> c i • Q₁ i) U:=by
   refine ⟨ h.smooth.mono fun i hi x hx=> (hi x hx).const_smul (c i),fun m=>?_⟩; obtain ⟨a,ha,h'⟩:= h.cost m; obtain ⟨b,hb,p'⟩:= tally p; refine ⟨ b*a, mul_nonneg hb ha,?_⟩; filter_upwards [ p',h',h.smooth ] with i hi hv hz x hx; rw [iteratedFDeriv_const_smul_apply ((hz x hx).of_le (n_le _)), norm_smul]; exact mul_le_mul hi (hv x hx) (norm_nonneg _) hb
lemma sub (h: Calm P Q₁ U)(p: Calm P Q₂ U): Calm P (Q₁-Q₂) U:=by
   have hp:= scale p ( isBigO_const_const (-1:ℂ) one_ne_zero P ); have he: (fun i:σ=> (-1:ℂ) • Q₂ i)= - Q₂:= funext fun i=> neg_one_smul _ _; rw [he] at hp; rw [sub_eq_add_neg]; exact add h hp
lemma comp {f:Points n→ℂ}(hk:IsCompact U)(h:∀ x∈U,ContDiffAt ℝ ∞ f x): Calm P (fun _=>f) U:=by
   refine ⟨ Eventually.of_forall fun _=>h,fun m=>?_⟩; have he: ContinuousOn (iteratedFDeriv ℝ m f) U:= fun x hx=> ((h x hx).continuousAt_iteratedFDeriv (n_le m)).continuousWithinAt; obtain ⟨C,hC⟩:= (hk.image_of_continuousOn he.norm).bddAbove; exact ⟨|C|,abs_nonneg C,Eventually.of_forall fun i x hx=> (hC (mem_image_of_mem _ hx)).trans ( le_abs_self C ) ⟩
lemma sum {u:Type*}(f:u→σ→Points n→ℂ){s: Finset u}(p:∀ x∈s, Calm P (f x) U): Calm P (∑ i∈ s,f i) U:=by
   induction s using Finset.induction_on with
   | empty=> simp only [ Finset.sum_empty ]; refine ⟨ Eventually.of_forall fun _ _ _=> contDiffAt_const, fun m=> ⟨0,le_rfl,Eventually.of_forall ( fun i x _=>by change ‖iteratedFDeriv ℝ m (0:Points n→ℂ) x‖ ≤ 0; simp ) ⟩⟩
   | insert x s h ih=> rw [Finset.sum_insert h]; exact add ( p x ( Finset.mem_insert_self .. ) ) (ih fun i h=> p i ( Finset.mem_insert_of_mem h ) )
end payments
variable {P:Normalize.Store G}(U:Initialize G)(K:Rose.Pick P){T:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}{S':Prescription (Press.portDeck G)}(Q:Speed.Quoted U K T S') (s:G.Simple)
variable {A : Set (Points n)}{f':ι→Tags G d n}{l:Filter ι} (h:Roi A) {F W} {θ r:ι→ℝ}
local notation "Z"=> FVA2.Scale.Measure.start U K d
include Q s h
open private modelAt sold from YM.SignedWilsonExpansion.Dancer.CashDesk -- `full name`?
lemma quote (h1:∀ i,Salary ℂ l 1 (fun j=> f' j i)) (j:ℕ): Calm l (fun i x=>Jury.fxt Z x j (f' i)) A:=by
    let Y:= Module.finBasis ℂ (Sec G d); let ℨ:= Fin n→ Fin ( Module.finrank ℂ (Sec G d) ); let Z'(x:ℨ)(i:ι):= ∏ k:Fin n, Y.coord (x k) (f' i k)
    let E(x:ℨ)(i:ι)(v:Points n):= Jury.fxt Z v j ( Y ∘ x ); let u:= ∑ x:ℨ, (fun i:ι=> Z' x i • E x i ); have he: (fun i:ι=> (fun x=> Jury.fxt Z x j ( f' i )))=u:= by
       ext i v; unfold u; simp only [Finset.sum_apply]; convert modelAt ( Jury.fxt Z v j ) (f' i) (fun i=> Y) using 2; congr 1; exact Subsingleton.elim _ _
       rfl
    rw [he]; exact sum _ ( fun x _=> scale ( Iris.comp h.1 fun v hv=>smoothP U K s Q (Y ∘ x) j (⟨v,h.2 hv⟩:Stage n) ) ( sold Finset.univ _ (fun i h=> h1 i ( Y.coord (x i) )) ) )
lemma paid (h1:∀ i,Salary ℂ l 1 (fun j=> f' j i))(u:Tendsto θ l (𝓝 0))(b:ℕ): Calm l (fun i x=> Path.mote Z b x (θ i) ( f' i )) A:=by
    let t(i):= (θ i:ℂ); have ht:t=O[l](1:ι→ℝ):= by exact IsBigO.of_norm_left ( show (fun i=> ‖t i‖)=O[l](1:ι→ℝ) from by simp_rw[t,Complex.norm_real]; exact ( Wipe.stop u ).norm_left )
    let R(m:ℕ)(i:ι)(x:Points n):= Jury.fxt Z x m ( f' i ); let E(m:ℕ)(i:ι): Points n→ℂ :=(t i)^m • ( R m i ); have hp:(fun i x=>Path.mote Z b x (θ i) ( f' i ))=∑ i∈ Finset.range (b+1), E i :=by ext i v; simp only [Finset.sum_apply]; rfl
    rw [hp]; refine sum _ (fun i _=> scale ( quote U K Q s h h1 i ) (?_)); simpa only[Pi.one_apply,one_pow] using! ht.pow i
omit s Q
include L
lemma blink (u:Tendsto r l trail) (f':Tags G d n) : Calm l (fun i x=> levelOf F W r i d n x f') A:=by
   let y(i:Fin n):= ( fields C.labels d ).symm ( f' i ); let F':= (fun i:Fin n=> d); let X(i:ι)(x:Points n):= levelOf F W r i d n x f'; refine ⟨ (u.eventually self_mem_nhdsWithin).mono fun i hi x hx=> ( Plot_neat _ hi f' ).contDiffAt ((conf_open n).mem_nhds (h.2 hx)), fun m=>?_ ⟩; obtain ⟨c,hc,hX⟩:= ( Iris.comp (P:=l) h.1 ( f:=WickGoal (C:=C) (d:=F') y) fun i hi=> WickGoal_tied y ( h.2 hi ) ).cost m; refine ⟨1+c,add_nonneg zero_le_one hc,?_⟩; filter_upwards [u.eventually ( Metric.tendstoUniformlyOn_iff.mp ( L.lead n F' y m A h.1 h.2 ) _ (show (0:ℝ)<1 from by norm_num) ),hX] with i hi hv x hx; specialize hi x hx; rw [dist_comm,dist_eq_norm] at hi; exact ( norm_le_norm_sub_add (iteratedFDeriv ℝ m (X i) x) (iteratedFDeriv ℝ m (WickGoal y) x) ).trans (add_le_add hi.le (hv x hx))
end Iris
end Tilted
end YM.SignedWilsonExpansion.Kane
