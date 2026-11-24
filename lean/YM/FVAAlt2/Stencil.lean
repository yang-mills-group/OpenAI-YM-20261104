import YM.FVAAlt2.Shift

/-! An origin-aware physical stamp on both sides of the fixed-regulator bridge.
It's a stencil binding *before* doing any integration or measuring-frame matching.
Stamp validation for specific producers can therefore discharge the remaining premises
without assuming anything about any either-scheme output identities.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2
open MS MS.Koszul MS.Native MS.Native.Wilsonian MS.Native.Studio MS.Book MS.Cylinder MS.Cylinder.Taylor MS.Cylinder.Lab MS.Puff MS.Puff.Actors MS.Swirl MS.Puff.Mom Swirl.Near MS.Fleet
open MS.Orbit MS.Orbit.LogReal MS.Orbit.Cog Convolve Program
open Function Finset Filter Topology MeasureTheory Lattice SchemeRG11.Sway SchemeRG11.Sway.Lam Pert.Orb
open scoped PowerSeries ContDiff
variable {G:Gauge}{n:Side}{d:ℕ}{ι κ:Type}[Fintype ι][DecidableEq ι][Fintype κ][DecidableEq κ]
variable (A:Module.Basis ι ℝ (Land G n))(b:Module.Basis κ ℝ (ScalarGhost G n))
variable (x:Site n)
local notation "E" => Com (isOdd (ι:=ι) (κ:=κ)) --
local notation "ℂx" => PowerSeries ℂ
local notation "N" => Wilson.Config G n
local notation "F'" => Dot G Cover
local notation "V"=>Land G n
set_option linter.unusedSectionVars false

def turnAddress (x:Site n)(k:Edge (Site n)):= (x+k.1,k.2)
def moveLetter (x:Site n)(O:Wilson.Config G n→ℝ)(X:N):= O (X ∘ turnAddress x)
lemma shift_gauge {f : N→ℝ}(he: Chart.OpenGauge (Chart.drive n) f): Chart.OpenGauge (Chart.drive n) (moveLetter x f):= by
 intro g U; unfold moveLetter; rw [show Chart.siteGauge _ g U ∘ turnAddress x = Chart.siteGauge _ (fun z=>g (x+z)) (U ∘ turnAddress x) from ?_,he]; funext ⟨v,i⟩; change _= _ * g (x+(v+step i)); simp [Function.comp,Chart.siteGauge,Chart.endRail,Chart.drive,turnAddress,add_assoc]
lemma shift_city (f:N→ℝ):moveLetter x f ∘ Chart.nation=(f∘Chart.nation)∘ (Sew.pull (turnAddress x) (G:=G)):= rfl
lemma shift_symbol (W: Dot G Cover)(f:N→ℝ)(hg:germ (f∘ Chart.nation))(hp: enters n W=reads (f∘Chart.nation)): posMark n x W= reads (moveLetter x f ∘ Chart.nation):= by
 change (Lab.Shift x (shown n W)).val= _
 have he(sh:Chart.City G (Site n)→ℝ): sh ∘ Sew.pull (P:=Site n) id=sh:=rfl
 rw [show shown n W=Sew.art id (f∘Chart.nation) from Subtype.ext (hp.trans (by rw [Sew.pooled id hg, he])), shift_city, ← Sew.pooled (turnAddress x) hg]; exact congr_arg Subtype.val (Sew.map_sec id _ _) -- params

/-- Atom binding requires an actual real physical insertion, includes charge
and engineering multiplier choices (constant per location here).
The mark reference and the object O in the top integral are provided *independently*.
`stamp` includes all-order equality of **input** Taylor tables at this position;
later constructors for the physical dictionary must actually discharge it.
`From` is only needed for the negative shift `d`; it lives on the cover stencil.
No derivative comparison on nonzero fields. -/
structure AtomCert (x:Site n)(U:Dot G Cover)(d:ℕ)(O:Wilson.Config G n→ℝ):Prop where
  invariant : Chart.OpenGauge (Chart.drive n) O
  smooth : germ (O ∘ Chart.nation)
  low : From U.val d
  stamp : posMark n x U=reads (O∘ Chart.nation)
  sym : Symm Draft.DotFlip U.val
namespace AtomCert

-- `Aura` already gives this COMBINED promise. We expose f rather than hiding it in an exists.
lemma on_aura (W: Dot G Cover)(A:Studio.Aura W d)(f:N→ℝ)(hv: Chart.OpenGauge (Chart.drive n) f)(hg:germ (f ∘ Chart.nation))(he: enters n W=reads (f∘Chart.nation)): AtomCert x W d (moveLetter x f):= ⟨shift_gauge x hv,(by rw [shift_city]; exact ContDiffAt.comp 0 hg (Sew.pull (G:=G) (turnAddress x)).contDiff.contDiffAt), A.low,shift_symbol x W f hg he,A.phase.symm⟩ -- comp f0 not mapped
lemma supplied (W: Dot G Cover)(h: Studio.Aura W d): ∃ f, ∀ x:Site n, AtomCert x W d (moveLetter x f):= by obtain ⟨f,he,hg,hf⟩:=h.pay n; exact ⟨f,fun x=>on_aura x W h f he hg hf⟩

-- mark-placement includes finite pull into moment
variable {x}
lemma gaugeW (f:Wilson.Config G n→ℝ)(h:Chart.OpenGauge (Chart.drive n) f) : Lattice.GaugeInvariant f := by intro u v; rw [show Lattice.gauge u v=Chart.siteGauge (Chart.drive n) (fun x=>(u x)⁻¹) v by ext1; simp [Lattice.gauge,Chart.siteGauge,Chart.endRail,Chart.drive], h]

variable {F:Dot G Cover}{O:Wilson.Config G n→ℝ}
abbrev mark0 (O:Wilson.Config G n→ℝ)(v:Potential G n):= O (positiveLinks v)
lemma watching (h:AtomCert x F d O): Watching O:=by
 refine ⟨fun u _ v=> gaugeW O h.invariant u v,?_⟩
 let L:Potential G n→L[ℝ] Chart.City G (Site n):=(LinkP G n).subtypeL
 exact (ContDiffAt.comp (g:=O ∘ Chart.nation) (f:=L) 0 (by rw [map_zero]; exact h.smooth) ((ContinuousLinearMap.contDiff («E»:=Potential G n) (F:=Chart.City G (Site n)) (𝕜:=ℝ) L).contDiffAt)).of_le le_top
lemma pinMask (t:ℤ)(F: F'): posMark n x (model t F) = mask t (posMark n x F):= by unfold posMark Lab.Shift shown transport; rw [LinearMap.comp_apply,LinearMap.comp_apply, mod_ferry,mod_ferry]; rfl
lemma below (h:AtomCert x F d O)(i:ℕ)(hi:i<d): mask i (posMark n x F)=0:=by
  have hm : model (i:ℤ) F=0:= by
    apply Subtype.ext; funext l; by_cases hl:l.length=i; exact (enough l (by rw [hl] )).trans (h.low l (by omega)); exact strange _ (by omega)
  rw [← pinMask,hm,map_zero]

-- recover Bose table on this shifted atom
lemma into4 {J:List ι}(f:Raw ι ℂ): pull (Bos.projVec ι κ) f (J.map avec)=f J:=by
 induction J generalizing f with| nil=>rfl| cons a l ih=>
    rw [List.map_cons,pull_cons,sum_eq_single a]; · rw [ih]; simp [Bos.projVec,avec]
    · intro i _ hi; simp [Bos.projVec,avec,Ne.symm hi]
    simp
abbrev μy (O: Wilson.Config G n→ℝ):Land G n→ℝ:= (O ∘ positiveLinks) ∘ g0 G n
lemma stood4(h:AtomCert x F d O): germ (μy O):= ContDiffAt.comp (g:=O ∘ Chart.nation) (f:=spread G n) 0 (by rw [map_zero]; exact h.smooth) (ContinuousLinearMap.contDiff («E»:=Land G n) (F:=Chart.City G (Site n)) (𝕜:=ℝ) (spread G n)).contDiffAt
local notation "S₀"=> isOdd (ι:=ι) (κ:=κ)
lemma enter4 (h:AtomCert x F d O): pull (embeddingM A b) (posMark n x F)=ink (dirA4 A) (μy O):= by rw [h.stamp]; exact embedding_ink A b h.smooth
lemma pinMarkMask (h:AtomCert x F d O)(i:ℕ):
    pull (embeddingM A b) (posMark n x (model i F))=(Bos.up (Bos.bob A _ h.stood4 i)).val:= by rw [pinMask, pull_mask, enter4 _ _ h,bob_inside]
-- below uses lookup on transducer, local rank claims hold on all independent fields
include b in
lemma clears_shift (h:AtomCert x F d O)(i:ℕ)(hi:i<d): Bos.bob A _ h.stood4 i=0:=by
 let P:=embeddingM A b
 have h0: (Bos.up (κ:=κ) (Bos.bob A _ h.stood4 i)).val=0:= by rw [← pinMarkMask _ b h i,pinMask,h.below i hi,map_zero]
 rw [Bos.up_v] at h0; apply Subtype.ext; funext l; exact (into4 (κ:=κ) _).symm.trans (congrFun h0 _)

def atomSeries(h:AtomCert x F d O):PowerSeries (Bos ι):=PowerSeries.mk (fun i=> Bos.bob A _ h.stood4 (i+d))
lemma ptS(h:AtomCert x F d O): promote (pull (embeddingM A b)) (promote (posMark n x) (Book.levels d F))= Com.forget S₀ (Bos.upS (h.atomSeries A)):= by
 funext k; rw [Com.forget_at,Bos.upS,PowerSeries.coeff_map,atomSeries,PowerSeries.coeff_mk]; have hh:=pinMarkMask A b h (k+d); rw [Nat.cast_add] at hh; exact hh -- cast concerns
include b in
lemma advance (h:AtomCert x F d O): PowerSeries.X^d * h.atomSeries A= Bos.seriesInk A _ h.stood4:=by
 ext1 k; rw [PowerSeries.coeff_X_pow_mul',Bos.seriesInk,PowerSeries.coeff_mk]; split; · rename_i e; rw [atomSeries,PowerSeries.coeff_mk,Nat.sub_add_cancel e]
 next e=> exact (clears_shift A b h k (lt_of_not_ge e)).symm
end AtomCert
end YM.FVAAlt2
