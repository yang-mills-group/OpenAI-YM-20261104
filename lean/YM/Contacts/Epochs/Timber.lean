import YM.Contacts.Allium.BeaconHill
import YM.Contacts.Epochs.Portal

/-! # Planning interweave. Post actuator commitments shelf frame actual.
 Need before-L just one real floor & shelves.Spans step cuffs.
 -/
noncomputable section
set_option autoImplicit false
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Contacts.Allium Contacts.Allium.Grant Contacts.Revest Contacts.Bounty
set_option quotPrecheck false
open Pressure Testing Terrain ConnectedActivityE6 Blaze Push.Uniform Push.SectorMeasure PhysicalNext.JointLoad.Heir
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge} {k x i j m:ℕ} {F:ℝ} {v: Patch} {β: ℝ} {s:Sheet G}{K:MapPrices}{R:Targets s (ThroughLaunch.bearing s K)}{E:Expenses R}
namespace Concert
abbrev chant (x:ℕ):ℝ:= (x+3:ℕ)
abbrev fabric (k:ℕ) :ℕ:= 40*(k+6)
lemma coal (k:ℕ): Choiced (fabric k) (chant k) ∧ 3 ≤ fabric k ∧ chant k+2 < (fabric k:ℝ)*(3/8:ℝ)-(3:ℕ) := by
   have h:3≤ fabric k:=by unfold fabric; omega
   unfold Choiced Contacts.Loom.Capture.race Contacts.Loom.Capture.stashp hearty; refine ⟨⟨by omega,?_ ,?_,?_ ⟩,h,?_⟩; all_goals simp only [chant,fabric]; push_cast; linarith only [Nat.cast_nonneg (α:=ℝ) k]
open Trophy.Lore
-- Pre contract Fee(T as Post) certificate
variable (z:Return.Wages){u:ℕ→ℕ}{Y:Rolls (ThroughLaunch.raise s u)}
     {w:Return.Wages}{f:ℕ→ℝ}(W: Register Y E w f) (B:ℕ→ℕ→Cafe){F:ℕ→ℕ→Postage}(S:Time.Scouts (F:=F)) (E₀:ℕ→ℕ→Exchange)
     (q:UVNext.CouplingReset.ResetPrices)(η:ℕ→ℝ)(P : PostCost Y){θ:Protection Y} (p:ℕ→ℕ→JointLoad.Heir.Record) (C: Programs s)
local notation "O" => (ThroughLaunch.bearing s K)
local notation "X" => R j i
local notation "X'" => E j i
local notation "U" => s.profile i
local notation "U'" => s.profile j
local notation "L" => Y.L j
local notation "J" => W.o j i
local notation "n" => (max (U).order (fabric k))
local notation "d" => (dim ((R j i).halo) (fabric k))
set_option quotPrecheck false -- move before
-- new.J rooms with spacecraft.Post cost at fixed κ, y.Number.m at WAIT. Need Patch P with L but arbor uses T.L, certificates store equal + transfers proof. Can't force L before patch? destruct with subst wrappers.
abbrev before (s:Sheet G)(K:MapPrices)(R:Targets s K)(z:Return.Wages)(j i k:ℕ)(U₀:Side): Prop := Trophy.Lore.Priced G (s.profile i) U₀ (z j i) ∧ Terrain.jetty (R j i) (fabric k) ≤ U₀.val
variable (V:G.ColorIndex)
abbrev Fly (j i k:ℕ)(r x:ℝ)(b:Patch) :Prop:= ∃ (d₁ d₂ d₃:ℕ)(J':Push.Uniform.Before G (s.profile j).width (s.profile j).paths b.J (Testing.query s (ThroughLaunch.bearing s K) j i).bind (max (s.profile i).order (fabric k) +3)), Tenor V b (R j i) (W.o j i) (chart G) (s.profile i) (s.profile j) (fabric k) (max (s.profile i).order (fabric k)) (dim (R j i|>.halo) (fabric k)) J' j d₁ d₂ r x (chant k) ∧ Arboric (G:=G) b (s.profile i) (s.profile j) d₁ j d₂ d₃ (dim (R j i|>.halo) (fabric k)) (fabric k) (max (s.profile i).order (fabric k)) x (chant k) -- naming ambiguity local U notation uses ambient variables! i,j in declaration shadow stale. Avoid. X Color nonempty for any G? ColorIndex finite maybe Empty when not simple.G need pass explicit.
def paceK (x:ℝ)(k j i :ℕ): Prop:= ∀ (v:Patch), v.L=Y.L j→v.J=j→v.Branches s.kernel G→ let T:= s.profile i; Palace (o:=W.o j i) (μ:=W.μ j i) (Y.L j) (Testing.query s (ThroughLaunch.bearing s K) j i) (R j i) Chi.canonical (fabric k) (p j i) T.order T.order T.power (C j i) (E j i) ((Y.L j).val:ℝ)⁻¹ v (mile j i) (Solo.raise (Roof.rays s) j i) (W.c j i) (z j i) (chant k+2) x ∧ Fly W V j i k (W.μ j i) x v
structure Fort (x:ℝ)(k:ℕ) (j i:ℕ) :Prop where
    base : Trophy.Lore.Phase G (Y.L j) (s.profile i) (z j i) (chant k) (alphaBound Y j) x (R j i|>.halo) (fabric k)
    buy : Outlay.Bargain G (s.profile i) (F j i) (S j i) x (betaF G x (Y.L j)) (alphaBound Y j)
    pure : let P:=s.profile i; let H:=R j i; AxPure (o:=W.o j i) (μ:=W.μ j i) (Y.L j) (Testing.query s (ThroughLaunch.bearing s K) j i) H Chi.canonical (fabric k) P.order P.power (E j i) 1 (W.c j i) (chant k+2) x
    pace : paceK z W p C V x k j i
variable (hg:G.Simple) (hp:EpochSeal s (ThroughLaunch.bearing s K) R E)(hk:StepStages j i)
lemma patch_equality (P Q:Patch)(h:P.L=Q.L)(ht:P.J=Q.J): P=Q:= by cases P; cases Q; simp_all
include hp hk hg
lemma wages (hZ:(p j i).ε≤1/4) (hf: before s O R z j i k (Y.L j)): ∀ᶠ x in atTop, Fort z W S p C V x k j i:= by
   obtain ⟨hc,ho,hw⟩:= coal k; have hU : 0 ≤ alphaBound Y j:= add_nonneg (s.profile j).drift_ge (abs_nonneg _); let x:= fabric k; let P':= Testing.query s O j i; have h' := (hp.hForm j i).2.2.2.1; let Ξ:= chant k;
   have hx: (E j i).wanting < -(3/8:ℝ):= h'.trans_lt (by norm_num); have hS:= W.consumes j i hk; have hK:= hS.2.1; let A:=(G.slopeConstant * Real.log (↑(Y.L j):ℝ)); have hV := Outlay.enact G (S j i) (s.profile i) A (alphaBound Y j) (YM.Work.E04.shift_nonneg G (Y.L j)) hU; have hQ:= bigTown (μ:=W.μ j i) L P' X (o:=W.o j i) Chi.canonical x (U).order (U).power (X') 1 (W.c j i) (chant k+2) ho hf.2 hK hS.1 one_pos hx hw;
   have h₁:∀ᶠ x' in atTop, paceK z W p C V x' k j i:= by
       unfold paceK; by_cases h : ∃ p: Patch,p.L=L ∧ p.J=j ∧ p.Branches s.kernel G; swap; · exact Eventually.of_forall fun v P hp hP hU=> (h ⟨P,hp,hP,hU⟩).elim
       obtain ⟨p₀,hL,hr,h⟩:= h; obtain ⟨U1⟩:= Push.Uniform.pre_order G (U').width (U').paths p₀.J s.kernel («n»:=n+3) (by have h:=ho; omega)
       obtain ⟨r,m,hm⟩:= sponsors V p₀ X (W.o j i) (chart G) U U' x n j (chart_ok G) hg hc (le_max_right _ _) hK d U1 -- check arg order
       obtain ⟨i',hi⟩:= clears p₀ U U' x n j hg hc m r d -- check
       have hV:= Solo.raise (Roof.rays s) j i; filter_upwards [hi,hm,stately L P' X (μ:=W.μ j i) (o:=W.o j i) Chi.canonical x (p j i) (U).order (U).order (U).power (C j i) X' (↑(Y.L j):ℝ)⁻¹ hg hZ (le_trans (by decide) (U).order_ge) le_rfl ho hK hS.1 hx (by positivity) (chant k+2) hw hf.2 p₀ h (mile j i) (Solo.raise (Roof.rays s) j i) (W.c j i) (z j i) (by unfold Solo.raise rays; linarith [(s.profile i).price_pos])] with x hi hh hk v ht ht' he;
       rw [patch_equality v p₀ (ht.trans hL.symm) (ht'.trans hr.symm)]; exact ⟨hk,m,r,i',U1,hh,hi⟩
   filter_upwards [Trophy.Lore.art G L U (alphaBound Y j) (z j i) (chant k) ((R j i).halo) x hU hc.2.1,hV,hQ,h₁] with t hc hp hv hx; exact ⟨hc,hp,hv,hx⟩
end Concert
end YM.PhysicalNext.Repeat.Legato
