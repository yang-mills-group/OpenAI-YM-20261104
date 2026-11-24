import YM.Pier.Base.Launch
/-! Single-clock seed for the forced-input and Strobe producer chain. These partial
results fall short of the sharp/perturbative/trace extensions.
Follows Joint/Feather final construction *on this common R*; obtains the witnesses,
not asserting about a `choose` after another branch. Standard Pillars format permits
further horizon extraction within its own scheme; not requiring or proving agreement
between different extraction orders in `LimitRoom`. -/

set_option autoImplicit false
noncomputable section
namespace YM.Pier
open Function Filter Set Lattice RG
open YM.PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Legato.Campaign Legato.Bandage
open FullVolume FullVolume.Final Extraction RG17
open scoped Topology BigOperators Classical

variable {G:Gauge}

def OnePath (R : Run G) (f : Extraction.Order) : Prop :=
  ∃ (S : Table R.family.book)
          (F : Spec.Final R.family f S),
          (Extraction.Order.mk Extraction.Sequence.full f.per).Ordered R.family S ∧
          PositionsUV R.family Extraction.Sequence.full ∧
          ∃ (L : YM.EveryPhase.Almanac F) (P:OPE.Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
              (X:Climb.Scaling S) (B:ℕ→ℝ), YM.EveryPhase.Completed F L ∧
              OPE.Services R.family f S ∧ OPE.Orbits.Foundation F P ∧ Pert.FirstExtension F X ∧
              (∀ m:ℕ,f.limits (fun _=>True) (fun N p=>R.family.path.β N p m) (B m)) ∧
              PertExtension.Running.isLimit R.family f B ∧
              ∀ U:Ultrafilter (ℕ×ℕ), (U:Filter _) ≤ f.fuse → Nonempty (SharpGram.Lenses.Mantle F (U:Filter _))

def LimitRoom (R : Run G) (f : Extraction.Order) : Prop :=
        ∃ g : Extraction.Order, OnePath R (f.refine g)

open Mooring MergeProof.Matric

/- Long-distance distortions not claimed. -/
def Corridors (R : Run G)(h : G.Simple){T:Campaign R}(W : Pillars R T) : Prop :=
  ∀ d k:ℕ, ∀ᶠ m:ℕ in atTop, ∀ N p e:ℕ, m ≤ e → e ≤ N →
       let x:=2^(k+1) * Pert.Asymptotics.regulatorRun R.family N p m^(2*(k+1))
       Gram.Within (books R W N p d m) (corridor R W h N p d e m) x ∧
        (m < e → ∃ hy:R.t d ≤ m,
         let P0:=stepTo R W h N p d m hy
         let a:=ruby d R.alloy.B.a m
         Gram.Costed (P0.leanings (books R W N p d (m+1))).toLinearMap
           (P0.leanings (soft (corridor R W h N p d e (m+1)))).toLinearMap (2*a*x) ∧
          2*a*x*(R.alloy.B.a.params (m+1)).columns ≤ x/2)

structure Starter (R : Run G) (h:G.Simple)(T:Campaign R) (W : Pillars R T) : Prop where
    uv : Jewel R T W
    pillar : SharpGram.Dense.Coverage R.family R.makes
    flick : Flick R.family.path.levels
    thresholds : Citizen R.family R.w (mutt R.family.path.levels R.Q) R.doors
    reserve {m N p d : ℕ} : R.family.ref d ≤ m → m < N →
      ∀ x : (R.family.labels.level d).Coeff,
        let V := (R.family.factory d N p).entries m x
        Room V 0 (R.family.path.rep N p m)
          (Real.sqrt (R.family.path.levels.clock.forcedAllowance m)) 1
          ((R.family.path.levels.params m).columns *
             (R.family.labels.level d).coeffSize ((R.family.labels.level d).core V.x))
    corridor : Corridors R h W
    limits : ∀ f : Extraction.Order, LimitRoom R f

set_option maxHeartbeats 900000 in
 theorem earn (h:G.Simple) (S0 : Levels G→Prop) (hS : OnPier S0) (b:ℝ)(hb:0<b) :
    ∃ (R:Run G)(T:Campaign R)(W:Pillars R T), R.family.path.levels.clock.kernel.penalty=b ∧
      S0 R.family.path.levels ∧ Starter R h T W := by
   obtain ⟨R,T,W,hT,hY,hP,hEx,hV,hG,hCov,hFlick,hCit,v,Θ,hW⟩:= Campaign.buildsPier S0 hS h b hb
   have J:= jewelOf17 T W h hT hY v Θ hW
   have he:= Campaign.opePackage17 W h hV hG hW
   refine ⟨R,T,W,hP,hEx,J,hCov,hFlick,hCit,(fun hm he x=> fitsPier W h hm he x),decksBooked R W h,fun f=>?_⟩
   obtain ⟨g,B,hB⟩ := PertExtension.Running.extraction R.family J.actual f
   obtain ⟨w,S,F,X,hS,hX⟩:= R.extractible17 h he (f.refine g)
   obtain ⟨L,hL⟩:= EveryPhase.all_characters F
   let t:=F.phase.transport
   obtain ⟨p,hp⟩:= OPE.Prescription.chosen F.room.kernel.laws.toSymmetric t.injection
   let r:OPE.Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin := ⟨p,hp,F.room.kernel,t.injection,t.rights,t.spots⟩
   have hb m:=Extraction.Order.retained (g:=w) (hB m)
   refine ⟨g.refine w, ?_⟩
   rw [show f.refine (g.refine w)=(f.refine g).refine w from rfl]
   exact ⟨S,F,from_spec ((f.refine g).refine w) ⟨F⟩ J.fullMesh,J.fullMesh,L,r,X,B,
     hL,hS,OPE.Orbits.produce F r hS,hX,hb,(fun m=> Order.along (hb m)),fun U hl=> SharpGram.Lenses.attains_mantle17 F hS U hl hCov⟩

 theorem stocked (G:Gauge) (h:G.Simple) (b:ℝ)(hb:0<b) :
    ∃ (R:Run G)(T:Campaign R)(W:Pillars R T), R.family.path.levels.clock.kernel.penalty=b ∧ Starter R h T W := by
   obtain ⟨R,T,W,hP,-,A⟩ := earn h _ (clearPier G) b hb
   exact ⟨R,T,W,hP,A⟩
end YM.Pier
