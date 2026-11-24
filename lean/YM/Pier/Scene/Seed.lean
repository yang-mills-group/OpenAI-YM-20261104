import YM.Pier.Scene.Pilot
/-! Joint readout endpoint, all small lengths and all constructor periods.
Do not assume even that these layouts are the calibrated scheme layouts in the
FULL matching target (later choose readings under this cost), nor that an
integral budget for *moment* estimates absolute values inside the integral.

`fine` combines these checks on one B, accepts actual constructed Starter. -/
set_option autoImplicit false
noncomputable section
namespace YM.Pier.Scene
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Marker Source Overlay
open FullVolume.Sever MergeProof MergeProof.Accent Extra.Histories Extra.Trajectories Extra.Multi Next.Rank Edition Spindle SharpGram Trace RG12 Next.UVStress
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Bandage
open RG17 RG17.Panoramic OPE OPE.Orbits SharpGram Spec
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
set_option quotPrecheck false
variable {G:Gauge}(R:Run G)(h:G.Simple){f:Extraction.Order} {S:Table R.family.book}{F:Spec.Final R.family f S}
local notation "C"=> R.family
local notation "A"=> R.family.path
local notation "Gx"=> Pert.Asymptotics.regulatorRun R.family
local notation "ι"=> R.family.path.levels
local notation "H"=> R.family.path.levels.clock.hatBeta

/-- All fields coexist on the one explicit reader order. This price export is
 for the actual *mesoscopic approximation by physical regular columns* before
 comparison to the independent coefficients. Receipts include the mandatory
 volume laws, flags/masks and marks. No change of arity in assuming the price.
 It's available to every finite horizon with the printed funding level choices
 (inner k*), after the reader construction. -/
structure ScenePlan (F : Final R.family f S) (L:Layout F) : Prop where
    layout : Located L
    handles : Handles L
    shift : L.shift=(fun _ _=> LinearEquiv.refl ..)
    compares : Comparably R L.level
    basis (p' d:ℕ) : ∀ᶠ r:ℝ in home, ∀ v: Free C d, ‖v‖≤ H (L.level r)^p' → ∃ w : R.family.label d,
      mass R.family d (L.shift d r w) ≤ H (L.level r)^(1+Lenses.price d+p') ∧ master L d r w= L.frame d r v ∧
      Tendsto (fun i=>atRef L d r i w) L.lens (𝓝 (locatedRef L d r w))
    allFlags {n:ℕ} (Γ:Census (Fin n)) (d:Fin n→ℕ)(o t e p':ℕ)(ht:1≤t) :
      ∀ᶠ r:ℝ in home, let m:= L.level r; let k:=berth R (o+25) m
      (m < k) ∧ Comparably R L.level ∧ EnvelopeRange R m k t o r ∧
       ((4*n:ℝ)* R.family.S.a k ≤ r/H m^o ∧ (4*n:ℝ)* R.family.S.a k ≤ r/(t:ℝ)/4) ∧
       ∀ X:Points n, AtShore t X→ ∀ p:ℕ,
        (∃ x:Fin n→Site (R.family.side k p), Neighbor R X r ((4*n:ℝ)*R.family.S.a k) x) ∧
        ∀ N:ℕ,k<N→∀ v:(j:Fin n)→ R.family.label (d j),
          (∀ j,mass R.family (d j) (L.shift _ r (v j)) ≤ (H m)^p')→
        ∀ x:Fin n→ Site (R.family.side k p), Neighbor R X r (r/(t:ℝ)/4) x →
        ∀ s:Γ.Mode, Integrable (gapTag R N s x (shutter R L d r N p v)) (Therm.scene A N p k) ∧
          ‖∫ Y,gapTag R N s x (shutter R L d r N p v) Y∂(Therm.scene A N p k)‖ ≤
             (8:ℝ)^e * Gx N p m^(2*e)

-- combine on one compatible fuse. Iteration and local envelopes retained
-- in Starter R. Further demands may use this same T even after selecting
-- the layout. On further refinements other constructions MAY be considered,
-- not asserting independence. No lower distance margin is baked into the choice of layout.
-- Lengths.Price is geometric only.
structure Supplies (R : Run G) (h:G.Simple)(T:Campaign R) (W : Campaign.Pillars R T) : Prop extends Starter R h T W where
  arrives (f : Extraction.Order) :
     ∃ (g : Extraction.Order) (S : Table R.family.book)
       (F : Spec.Final R.family (f.refine g) S) (E : YM.EveryPhase.Almanac F) (P:OPE.Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
          (X:Climb.Scaling S) (B:ℕ→ℝ) (L:Layout F),
         (Extraction.Order.mk Extraction.Sequence.full (f.refine g).per).Ordered R.family S ∧
         FullVolume.PositionsUV R.family Extraction.Sequence.full ∧ YM.EveryPhase.Completed F E ∧
         OPE.Services R.family (f.refine g) S ∧ OPE.Orbits.Foundation F P ∧ Pert.FirstExtension F X ∧
         (∀ m:ℕ,(f.refine g).limits (fun _=>True) (fun N p=>R.family.path.β N p m) (B m)) ∧
         PertExtension.Running.isLimit R.family (f.refine g) B ∧ ScenePlan R F L ∧
         ∃ u:Ultrafilter (ℕ×ℕ), (u:Filter _) ≤ (f.refine g).fuse ∧ ∃ s:Extraction.Sequence, ∃ b:Lenses.Mantle F (u:Filter _),
           Pegs b L ∧ StrictAnti (b.radius ∘ ⇑s) ∧ ∀ i:ℕ, L.level (b.radius (s i))= s i
namespace Starter
variable {T0:Campaign R}{W':Campaign.Pillars R T0}
lemma fine (U : Starter R h T0 W') : Supplies R h T0 W' := by
   refine ⟨U,fun f => ?_⟩
   obtain ⟨g,S,F,hr,hZ,E,P,X,B,hE,J,hF,hX,hB,hL,hQ⟩:= U.limits f
   let K:=Ultrafilter.of ((f.refine g).fuse)
   have hk:(K:Filter _) ≤ (f.refine g).fuse:= Ultrafilter.of_le _
   obtain ⟨w⟩:= hQ K hk
   obtain ⟨L,hC,hP,hv,hW,hM,s,hs,hv'⟩:= installable R U w J P hk
   exact ⟨g,S,F,E,P,X,B,L,hr,hZ,hE,J,hF,hX,hB,hL,
     ⟨hv,hW,hC,hM, shapesPay R L J hv hP,fun _ d=>wholeFrame R L J U hv hM d⟩,
     K,hk,s,w,hP,hs,hv'⟩
end Starter

theorem joint (G:Gauge)(h:G.Simple)(b:ℝ)(hb:0<b) :
    ∃ (R:Run G)(T:Campaign R)(W:Campaign.Pillars R T), R.family.path.levels.clock.kernel.penalty=b ∧
        Supplies R h T W := by
   obtain ⟨R,T,W,hb,hP⟩:= stocked G h b hb
   exact ⟨R,T,W,hb,Starter.fine R h hP⟩
end YM.Pier.Scene
