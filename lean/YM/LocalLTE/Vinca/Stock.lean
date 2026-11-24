import YM.MergeProof.Fleece
import YM.MergeProof.Sonata
/-!
# Conservation in Stamp supplies. Endpoints with actual atoms.

A Tune guaranteed by the EXISTING mergeproof producer would not suffice
for the following census. It's not free to use another set of lookalike
marginals to get predictions; even costs can blow up on equality of functions.
Retain the exact deterministic resolver obtained via Career.dilations.
(We use the same `Y` for affordability; prove larger η on the chosen
calendar. Small eligibility limitations inherited from reference calibration.)
These jobs are at singletons; don't identify with separate nonsingleton
representations at rotated origins.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Vinca
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus MergeProof
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}(B:SectionData F) (H : History G) (N p i : ℕ) (Y : Hol G)
local notation "Rout" => H.rep N p i
local notation "Old" => H.rep N p (i+1)
local notation "WorkSite" => H.S.side i p
local notation "StartSite" => H.S.side (i+1) p
local notation "g₀" => Config G StartSite → ℂ
local notation "Lℓ" => H.S.block i
-- Explicit deterministic ticket.
-- Remove unused if not needed.W
structure Ink (α : Config G StartSite→ℂ)(β:Res G StartSite) (δ:ℂ) (Q:GaugeDoor Old Rout) (A:Wing→Prop)(f:g₀)(lead:F.Coeff)(c t u:ℝ) (W: Coefficient F WorkSite):Prop where
    cost:Gig B H N p i Y f W lead c t
    line:Tale A 0 0 (((H.S.block i).val:ℂ)^d) α β (profile (Rout).activities W.forced) δ u t Q
-- extends Availability.Co.Per.
variable {B H N p i Y} {x:Config G (H.S.side (i+1) p)→ℂ} {β:Res G (H.S.side (i+1) p)} {δ:ℂ} {Q:GaugeDoor (H.rep N p (i+1)) (H.rep N p i)} {A:Wing→ Prop} {f: Config G (H.S.side (i+1) p)→ℂ}{lead:F.Coeff}{a b c u t v:ℝ}{W:Coefficient F (H.S.side i p)}
lemma Ink.weaken (h:Ink B H N p i Y x β δ Q A f lead a b c W)(hq:a≤u)(hv:b≤t)(hp:c≤v):Ink B H N p i Y x β δ Q A f lead u t v W:=⟨h.cost.weaken hq hv,h.line.climb le_rfl hp hv⟩
lemma Ink.offered (h:Ink B H N p i Y x β δ Q A f lead a b c W):Coupon B H N p i Y x β δ Q A f lead a b c:=⟨W,h.cost,h.line⟩
variable (B H N p i Y)
lemma zSlot (X:Wing→Prop)(q:GaugeDoor Old Rout)(_h:H.Selected) {t u:ℝ}(ht:0≤t)(hu:0≤u) : Ink B H N p i Y 0 0 0 q X 0 0 t t u (Extra.Histories.primary (0:Site WorkSite) 0):=by
   let P:Coefficient F WorkSite:= Extra.Histories.primary 0 0; have hp: P.Format 0 Y Rout:= primary_format _
   have he: P.density 0 B Rout=0:=by
      funext V; rw [show P.density 0 B Rout V= _ from primary_density B (Rout) 0 V];change _*part B 0 Rout V 0=0;rw [map_zero,mul_zero]
   have hκ: P.remBound 0 Rout (kappa H i) 0:= primary_rem _ (Real.sqrt_pos.mpr (forcedPos _ _))
   obtain ⟨a,b,hb,h₁⟩:= rem_tabs.mp hκ
   have h2:a=0∧ b=0:= by have hz:=hb.first; have hr:=hb.second; constructor<;>linarith
   obtain ⟨rfl,rfl⟩:=h2
   refine ⟨⟨hp,?_,by simpa only [P, Extra.Histories.primary,sub_zero,Frame.coeffSize,Pi.zero_apply,norm_zero,sum_const_zero,mul_zero] using ht, 0,0,hb,by rw [mul_zero,add_zero]; exact ht⟩,?_⟩
   · have hx:= (H.levels.transition_mass i p (Old).beta)
     rw [he,Extra.Histories.blast]; funext x; simp [StepData.push]
   rw [show profile (Rout).activities P.forced = 0 by funext i j; simp [profile,P,cram,Extra.Histories.primary]]; exact taped hu ht

-- Unit
lemma currencyQ (A:Wing→Prop)(q:GaugeDoor Old Rout)(h:H.Selected)(hm:i<N) (c w t:ℝ)(hp:0≤t)(T:Heading F):let P:= Extra.Histories.primary 0 F.e0
    Ink B H N p i Y (P.exponentialEntry 0 B Old) 0 1 q A (P.density 0 B Old) (T.leads Lℓ F.e0)
      (w*F.coeffSize (F.core F.e0)) (c*F.coeffSize (vowel F Lℓ (F.core F.e0))) t (Extra.Histories.primary (0:Site WorkSite) ((((H.S.block i).val:ℂ)^d) • F.e0)):=by
   intro P; let Q:= H.S.block i; let x:ℂ:=(Q.val:ℂ)^d
   have hx : T.leads Q F.e0=x • F.e0 := by
    change T.map (vowel F Q F.e0) = _
    rw [show vowel F Q F.e0 = x • F.e0 by
      funext i
      by_cases hi : i=0
      · rw [hi]; simp [x,vowel,F.zero_degree]
      simp [vowel,Frame.e0,Pi.single_eq_of_ne hi],map_smul,T.unit]
   rw [Size.unit_core, show vowel F Q 0=0 from funext fun i=>by simp [vowel], show F.coeffSize 0=0 from by simp [Frame.coeffSize],mul_zero,mul_zero]
   let R:= Extra.Histories.primary (0:Site WorkSite) (x • F.e0)
   have hu:P.exponentialEntry 0 B Old= fun _=>1:=by
      funext U
      have he j:P.maskedTerm Old j U=0:= congr_fun (map_zero (Push.Local.maskLinear _ _)) U
      change F.e0 0+maskLinear _ _ (presented B 0 _ (F.core F.e0)) U+∑' j,P.maskedTerm Old j U=1; rw [Size.unit_core]; simp only [map_zero,Pi.zero_apply,add_zero,Frame.e0,Pi.single_eq_same,he,tsum_zero]
   have hκ:R.remBound 0 Rout (kappa H i) 0:= primary_rem _ (Real.sqrt_pos.mpr (forcedPos _ _)); obtain ⟨a,b,hb,hA⟩:= rem_tabs.mp hκ
   have ha:a=0∧b=0:=by have h:=hb.first; have h':=hb.second; constructor<;> linarith
   obtain ⟨rfl,rfl⟩:= ha
   refine ⟨⟨primary_format _,?_ ,?_, 0,0,hb,by simp⟩,?_⟩
   · have hz : blast H N p i d (P.density 0 B (H.rep N p (i+1)))=x • liftVac H N p i:=by unfold P;rw [unit_density]; exact blast_vac H N p i d h hm
     change R.density 0 B Rout= _; unfold R; rw [hz,show Extra.Histories.primary (0:Site WorkSite) (x • F.e0) = Extra.Histories.stretch x (Extra.Histories.primary 0 F.e0) by simp [Extra.Histories.stretch,Extra.Histories.primary]]
     funext V; rw [stretch_density,_root_.YM.Extra.Histories.unit_density];rfl
   · change Motion.orbitCost F * F.coeffSize (R.x-_)≤_; rw [show T.leads (Lℓ) F.e0=x • F.e0 from hx]; simp [R,Extra.Histories.primary,Frame.coeffSize]
   rw [hu, show profile (Rout).activities R.forced=0 by funext i j; simp [R,Extra.Histories.primary,profile,cram]]; exact taped hp le_rfl
variable {ι:Type}[Nonempty ι][Countable ι]
lemma full {X:Wing→Prop} (q:GaugeDoor Old Rout)(hq: SoundDoor (H.levels.clock.op i p) q)
    (h:H.Selected)(hm:i≤N){g:ι→ g₀}{w':ι→ Res G StartSite}{t:ι→ℂ}{φ:g₀}{ψ: Res G StartSite}{σ:ℂ}{f:ι→ g₀}{U:ι→ F.Coeff}{u a z:ι→ℝ}(P:ι→ Coefficient F WorkSite)
    (hp:∀ j,Ink B H N p i Y (g j) (w' j) (t j) q X (f j) (U j) (u j) (a j) (z j) (P j))(hg:∀ V, HasSum (fun i=>g i V) (φ V))(hx:∀ i V, HasSum (fun j=> w' j i V) (ψ i V))(ht:HasSum t σ)
    (hf:Dominated f)(hk:∀i,Measurable (f i)) (hv:Summable fun i=> F.coeffSize (U i))(hu:Summable u)(ha:Summable a)(hζ:Summable z):
    Ink B H N p i Y φ ψ σ q X (fun V=> ∑' i,f i V) (∑' i,U i) (∑' i,u i) (∑' i,a i) (∑' i,z i) (Extra.Histories.merge (code _) P):=by
   have hκ:0<kappa H i:= Real.sqrt_pos.2 (forcedPos ..)
   refine ⟨Gig.all_in B H N p i Y h hm (fun i=>(hp i).cost) hf hk hv hu ha, Tale.upon hq (fun i=>(hp i).line) hg hx (fun i V=> profile_merge (code _) P hκ (fun i=> (hp i).cost.bound) ha i V) ht ⟨fun i=>?_,hζ,le_rfl⟩ ⟨fun i=> rem_nonneg ((hp i).cost.bound),ha,le_rfl⟩⟩
   obtain ⟨j,h,P,p,Φ,W⟩:= (hp i).line; exact sumBudget_credit W.purchase
section Ground
variable (F) {s:Side}
structure Gateway (Z:Hol G) (R:Rep G s)(c:Side) where
   core: F.Index → Coefficient F c
   reader (f:Config G s →ℂ)(b:Support s)(u:ℝ) (h:RegFit R 0 d Z b f)(hp:R.p.supBounds 0 b f u): Coefficient F c
   flag (f:Config G s→ℂ)(j:ℕ)(x:ℝ)(ht: SlotFit R 0 j f)(he:∀ U,‖f U‖≤x): Coefficient F c
variable {F}
variable (Q:GaugeDoor (H.rep N p (i+1)) (H.rep N p i))
structure Key (W:Gateway F Y Old WorkSite)(c w t:ℝ)(T:Heading F)(A:Wing→Prop):Prop where
   main (j:F.Index): j≠0 → let v:=Size.axis F j; let Z:=Extra.Histories.primary (0:Site StartSite) v
    Ink B H N p i Y (Z.exponentialEntry 0 B Old) 0 0 Q A (Z.density 0 B Old) (T.leads Lℓ v) (w*F.coeffSize (F.core v)) (c*F.coeffSize (Bid.vowel F Lℓ (F.core v))) t (W.core j)
   regular (f:g₀)(b:Support StartSite)(x:ℝ): let u:=(Old).p.mass b x; ∀ (h:RegFit Old 0 d Y b f)(hp:(Old).p.supBounds 0 b f x), Ink B H N p i Y (masked (Old).p.threshold b f) 0 0 Q A (salary Old b f) 0 (w*u) (w*u) (2*u) (W.reader f b x h hp)
   forced (f:g₀)(j:ℕ)(x:ℝ): let u:=(Old).p.mass ((Old).activities.forced j).support x; f≠0 → A (.gasKey j)→ ∀(ht: SlotFit Old 0 j f)(h:∀ U,‖f U‖≤x), Ink B H N p i Y 0 (exactGas (Old).activities j f) 0 Q A (Extra.Histories.fare Old j f) 0 (w*(u / Real.sqrt (H.levels.clock.forcedAllowance (i+1)))) (w*(u / Real.sqrt (H.levels.clock.forcedAllowance (i+1)))) (2*u) (W.flag f j x ht h)
   map_norm v : F.coeffSize (T.map v) ≤ c * F.coeffSize v ∧ F.coeffSize (T.map.symm v) ≤ c * F.coeffSize v
variable {B H N p i Y Q} {W:Gateway F Y (H.rep N p (i+1)) (H.S.side i p)}{a t w:ℝ}{T: Heading F}{P:Wing→Prop}
lemma Key.old (h:Key B H N p i Y Q W a t w T P): Stampede B H N p i Y Q a t w T P:=⟨fun _ hi=>(h.main _ hi).offered,fun _ _ _ he hx=>(h.regular _ _ _ he hx).offered,fun _ _ _ ht hv hx _ hA=>(h.forced _ _ _ ht hv hx hA).offered,h.map_norm⟩
end Ground
end YM.LocalLTE.Vinca
