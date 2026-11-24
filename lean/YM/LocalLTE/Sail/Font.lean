import YM.LocalLTE.Sail.Cantabile
import YM.LocalLTE.Sail.Allocation
/-!
# Quadrant prices with customary probe normalization

From actual normalized TransferData.entries with powers of the mesh in the
operator. Allows rescaling at microscopic stage (not unbounded regulator-independent raw amplitude).
A request quotes weight-1 errors on THESE same scaled probes. No assumption
that the calibration basis is produced from idealized labels.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Sail
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open YM.Push.Local
open Lattice Next.Foundations YM.MergeProof Planned.GuardedAtom Motion Guard
open MeasureTheory
open PhysicalNext.Repeat PhysicalNext.JointLoad
open LocalLTE.Ticket LocalLTE.River
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge} (P:History G) (N p:ℕ)
variable {d:ℕ}
local notation "B"=> (localSection G d)
variable {Fv:Type*}[Finite Fv]
variable (v:((Labels.frames G).level d).Coeff)
    (M:Motion) (o:∀ i,Site (P.S.side i p))
variable (A:Extra.Histories.Music ((Labels.frames G).level d) P N p)
-- through cone-any. moves fixed through composition.T.Not silently replacing m kiosk outputs by cheaper norm layouts.Unit.Beacon.C
variable {W:Bid.Worth} {m i r0 :ℕ} (π:((P.rep N p m).activities).Moves M.1 (o m))
noncomputable def sampleNorm (d m:ℕ):ℂ:= ((P.S.a N:ℂ)^d)*alto P m d
local notation "σ" j=> sampleNorm P N d j
noncomputable abbrev glyphSeed (m:ℕ): Config G (P.S.side m p)→ℂ := radiant (σ m) M (o m) (((A.tone m).plays v).exponentialEntry 0 B (P.rep N p m))
noncomputable abbrev glyphK (m:ℕ): Box (P.S.side m p)→ Config G (P.S.side m p)→ℂ:= sunny (P.rep N p m) ((A.tone m).plays v).forced M (o m) (σ m)
noncomputable abbrev stampField (T: Coefficient ((Labels.frames G).level d) (P.S.side m p)) := stretch (σ m) (Planned.GuardedAtom.audition («z»:=M) π T)
noncomputable abbrev imprint := stampField P N p M o π ((A.tone m).plays v) -- variable order check
noncomputable def primProbe : Config G (P.S.side N p)→ℂ:= ((P.S.a N:ℂ)^d) • stepUp M (o N) (initial (localSection G d) P N p v 0)
local notation "pF"=> imprint P N p v M o A π
lemma sample_top : sampleNorm P N d N=1:=by unfold sampleNorm alto; exact mul_inv_cancel₀ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (P.S.a_pos N).ne'))
lemma sample_step : sampleNorm P N d (m+1) = ((P.S.block m|>.val):ℂ)^d * sampleNorm P N d m:=by unfold sampleNorm; rw [alto_at,mul_left_comm]
-- use Parse unicode.
set_option quotPrecheck false
local notation "Z₁"=> (P.rep N p m)
local notation "w₁"=> glyphK P N p v M o A
local notation "S"=> glyphSeed P N p v M o A
local notation "z"=> σ m
local notation "v₁"=> ((A.tone m).plays v)
open Accent
lemma sunny_color : w₁ m=profile (P.rep N p m).activities (pF).forced :=by
   let L:= Planned.GuardedAtom.audition («z»:=M) π v₁
   change (σ m) • floatUp M _ _= profile (Z₁).activities ((σ m) • L.forced)
   rw [profile_scale]; unfold L; rw [foyer]
private lemma exponentialT (T: Coefficient ((Labels.frames G).level d) (P.S.side m p)) (o:Site (P.S.side m p)) (c:ℂ) (U):
    (stretch c T).exponentialEntry o B (P.rep N p m) U=c * T.exponentialEntry o B (P.rep N p m) U:=by
   let Q := stretch c T; have hb (j) : Q.maskedTerm (Z₁) j U=c*T.maskedTerm (Z₁) j U:=masked_scale ..
   change Extra.Histories.part B o (Z₁) U (c•T.x)+ ∑' i,Q.maskedTerm _ i U=c* (Extra.Histories.part B o _ U T.x+_); simp only [map_smul, hb,smul_eq_mul,tsum_mul_left,mul_add]
lemma sunny_ray : S m= (pF).exponentialEntry (o m) B (P.rep N p m):=by
   let a':= audition («z»:=M) π v₁; have h:a'.exponentialEntry (o m) B (P.rep N p m)=stepUp M (o m) (((A.tone m).plays v).exponentialEntry 0 (localSection G d) (P.rep N p m)):=by
       have h:= bow (o:=0) M v₁ _ (sound G d) π; rw [show affine M.1 (o m) 0=o m by simp [affine]] at h; exact h
   change z • stepUp M (o m) _= (Extra.Histories.stretch z a').exponentialEntry (o m) B (P.rep N p m)
   rw [← h]; funext U; exact (exponentialT P N p a' (o m) z U).symm
variable (h:Heard (localSection G d) P N p (hol G) m (A.tone m))(hs:P.Selected)(ht:m≤N)
include hs h ht
omit hs ht in
lemma stamp_signal : coin Z₁ (S m) (pF).forced= radiant z M (o m) (((A.tone m).plays v).density 0 B Z₁) ∧ Dominated (pF).forced∧ (pF).Format (o m) (hol G) Z₁:=by
   obtain ⟨hf,hL⟩:=h.earns v; obtain ⟨a,b,hx,-⟩:= rem_tabs.mp hL;
   obtain ⟨hv,hc,hD⟩:= audition_turn M _ π ((by decide: 2≤ 4).trans (Next.Foundations.actual_side_ge P.S m p)) (sound G d) hf hx
   rw [show affine M.1 (o m) 0=o m from by simp [affine]] at hv hc hD
   refine ⟨?_, rainbow (rem_dominated (hc.bound le_rfl)) _,stretch_format _ hv⟩
   rw [Sail.sunny_ray P N p v M o A π, coin_primary]
   funext U; refine (stretch_density ..).trans ?_; exact congr_arg (z*·) (congr_fun hD U) -- elaboration.P.Port
omit h ht hs
local notation "Z'"=> P.rep N p N
variable (π': (P.rep N p N).activities.Moves M.1 (o N))(hv:OnTop (localSection G d) P N p (hol G) (A.tone N))
include hv hs
lemma prim_ray : ∀ U,((Z').eval U:ℂ)*primProbe P N p v M o U= Accent.coin Z' (glyphSeed P N p v M o A N) (imprint P N p v M o A π').forced U:=by
   intro U; rw [(stamp_signal P N p v M o A π' hv.heard).1]; have he:= mural P (hol G) B N p A v M (o N) hv hs U -- arg order.P.
   let u₀:= (stepUp M (o N) (initial (localSection G d) P N p v 0)); let x:= ((P.S.a N:ℂ)^d)
   let F':= (stepUp M (o N) (((A.tone N).plays v).density 0 (localSection G d) Z')); change _*u₀ U= (alto P N d)*F' U at he
   change (↑((Z').eval U):ℂ)*(x*u₀ U)=(x*alto P N d)* F' U
   rw [mul_left_comm,he,mul_assoc]
omit hv
variable (p₀ : (P.rep N p (m+1)).activities.Moves M.1 (o (m+1)))
-- `embed` hypothesis. any translations of this type. Not all floor/parent.Per primary factory Gram.
include hs h
lemma fromStep (hm:m<N)
    (hh: Heard (localSection G d) P N p (hol G) (m+1) (A.tone (m+1)))(hv: Responds (localSection G d) P N p W m (A.tone (m+1)) (A.tone m)) (hp:o (m+1)= (P.levels.clock.op m p).ratio.embed (o m)) : coin (Z₁) (S m) (pF).forced=(P.levels.clock.op m p).push (P.rep N p (m+1)).beta (coin (P.rep N p (m+1)) (glyphSeed P N p v M o A (m+1)) (imprint P N p v M o A p₀).forced):=by
   have hz:=sample_step P (N:=N) (m:=m) (d:=d); obtain ⟨hf,hF⟩:= hh.earns v
   let V':= (A.tone (m+1)).plays v
   rw [(Sail.stamp_signal P N p v M o A π h).1, (Sail.stamp_signal P N p v M o A p₀ hh).1, hp]; exact starship P M (o m) _ _ d (hv.values v) (play_integrable P N hs hm hf hF) _ hz -- order
end YM.LocalLTE.Sail
