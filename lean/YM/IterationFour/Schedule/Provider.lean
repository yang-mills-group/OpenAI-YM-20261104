import YM.UVExtension.Reports.Ultraviolet
import YM.EveryPhase.Extension

/-!
# Choosing pre/post block extras on the DESIGNATED UV-provider route

Auxiliary rider on `Levels` only, not a predicate with a comparison hidden in
it; if it can be realized with the stated order of choices, can ask for it in
a selection from `UVExtension.Reports.ultraviolet`. Same commitment from
`uv_wishes`, don't change coupling or Vol trajectories afterwards. Follows the
proof of `uv_flowered` through that checkout to retain this additional receipt.

Explicit adapter back to `Final` and the common every-phase provider, not a
claim that two arbitrary already selected configurations coincide. No removal
of the phase/formal hypotheses of downstream endpoints.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.IterationFour
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Bandage
open InteractingRank Next.Rank Next.Rank.Tapes RankCovariance PhysicalNext.InteractingRank.Soft
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open Next.Extract Dash
open YM.MergeProof MergeProof.Accent UVExtension UVExtension.Harvest

def Rider (W : Levels G → Prop) := ∀ s : Sheet G, ∃ D : Rolls s, ∀ θ : Protection D,
    ∃ T : Delays θ, ∀ U : Delays θ, DelayLe T U →
      ∀ b : Bar U, ∀ J : Wait b, ∃ Y : Wait b, WaitLe J Y ∧
        ∃ a : Levels G, Paid Y a ∧ AsDivisors a.S ∧ W a

lemma inside (hG:G.Simple) {b:ℝ} (h:0<b) {goal : Levels G→Prop} (hg:Rider goal) :
    ∃ C:Family G, C.path.levels.clock.kernel.penalty=b ∧ Spec.Calibrated C ∧ C.Makes ∧ Extraction.Wcmain C ∧
     UVExtension.Oasis.Floral (hG:=hG) C ∧ goal C.path.levels ∧
     ∃ (f : Extraction.Order) (T : Table C.book), Nonempty (Spec.Final C f T) := by
  obtain ⟨k,hb,hp⟩:= YM.Axial.viable G b h
  let v: Orders:= ⟨4,fun i=>6+i,fun i=>2+i,fun i=>100+i⟩
  have hE (i:ℕ): 100 ≤ v.supportExp i:= by change (100:ℝ) ≤ 100+i; simp
  have he : Draft v:= by
    refine ⟨le_rfl,fun i j hij=> Nat.add_le_add_left hij 6,fun i j hij=> Nat.add_le_add_left hij 2,fun i j hij=>?_,fun i=> lt_of_lt_of_le (by norm_num) (hE i),fun i=>by change _ ≤6+i; omega,fun i=>by change _≤2+i; omega⟩
    change (100:ℝ)+i≤100+j; gcongr
  obtain ⟨s,T,Y,K,hX,H,l,hL,hK⟩:= uv_wishes hG hp he (fun _=>1) (fun _ _ _=>le_rfl) (fun _=>le_rfl) hE
  let M:=UVExtension.Case.provider s T l
  obtain ⟨P,hR⟩:= hg M.p
  obtain ⟨_,H₀⟩:= hK l le_rfl
  let Q (_ _ :ℕ): JointLoad.Clockwork.Menu:= ⟨Push.SectorMeasure.Chi.canonical,1,0,0,0,0,0,0,one_pos,le_rfl⟩
  let J₀ (_ _ :ℕ):JointLoad.Folio.Aux:=⟨40,1,1,le_rfl⟩
  let E : Next.Scheduling.Exchange:=⟨0,0,1,1,1,0,0,by norm_num⟩
  obtain ⟨w,h⟩:= H₀ P
  obtain ⟨F,hF⟩:= h w le_rfl (fun _ _=> ⟨1,1,1,1,le_rfl,zero_lt_one,zero_lt_one⟩) (fun _ _=> E)
  obtain ⟨θ,-,hH⟩:= hF _ (fun _=>one_pos)
  -- Spend the rider before paying `D` and with the retained `P`
  obtain ⟨U,hU⟩:= hR θ
  obtain ⟨V,h₁,hK⟩:= hH Q J₀ U
  obtain ⟨D,-⟩:= Bar.exists_above V 2; let I:Wait D:= ⟨fun _=>0,fun _ _=>0,fun _=>by simp,0⟩
  obtain ⟨Y,-,H₂⟩:= hK V (DelayLe.refl _) D I
  obtain ⟨Ω,hY,a,ha,hp,hgoal⟩:= hU V h₁ D Y
  obtain ⟨X,B,hB,R,W,c,T,t,S,Hx,Hk,hT,hq,hu,hD,h_lease,h_rate,⟨hh',hH,h_Φ,h_sh⟩,hE⟩:= H₂ Ω hY.ready hY.window hY.length a ha hp
  let V:= Mast.centerB S Hx; let W:=Mast.cellar S c Hx t Hk; let S':= Mast.Cellar.gate (Mast.roseA S) W
  let Z:= Family.mk (Issue.trail V) (hol G) (Labels.frames G) (localSection G) t S'
  obtain ⟨hc,hF,hQ,hU,hW,B₀,-,-,K₀,F₀,L,-,H⟩:=hT.reception
  have hv:Ribbons.Created Z:= ⟨_,t,S',rfl⟩
  have hπ:Acme.Aroma Z:= ⟨Ribbons.laurelE Z hG hU hu hq hv hF,hq, Ribbons.fugacious Z hG hu⟩
  refine ⟨Z,(congr_arg KernelChoices.penalty (B.valid.kernel.trans hX)).trans hb,hc,hF,hW,Oasis.survives W Hx hD hQ hh' hH (hB.symm ▸ h_Φ) h_sh h_lease h_rate hT hu,(show goal B.a from hB.symm ▸ hgoal),?_⟩
  obtain ⟨g,A,L,R,z,T,E,-,hA,s,-⟩:=H Extraction.Order.full -- inspect order
  let f := Extraction.Order.full.refine g
  obtain ⟨M,I,hI,p⟩:= Acme.emanate (W:=E) hπ hG (grilled Z hF hU hq s.copies) (hE f) s hA.clean.ready hA.clean.tilt
  exact ⟨f,T,Acme.glistens hc hA.clean.ready hA.clean.tilt p⟩

/-- Check exact UV and every-phase receipts on a strengthened schedule. -/
theorem acceptedWith (hG : G.Simple) {penalty : ℝ} (hp : 0<penalty)
    {goal : Levels G→Prop} (h : Rider goal) :
    ∃ (C : Family G) (f : Extraction.Order) (T : Table C.book)
        (F : Spec.Final C f T) (L : EveryPhase.Almanac F),
      C.Makes ∧ Spec.Calibrated C ∧ C.path.levels.clock.kernel.penalty=penalty ∧
      UVExtension.Oasis.Floral (hG:=hG) C ∧ goal C.path.levels ∧
      (Extraction.Order.mk Extraction.Sequence.full f.per).Ordered C T ∧
      (∀ d k:ℕ,∀ᶠ n in atTop,
          ∀ (r:ℕ) (v:Fin r→ C.book.Token), (∀ i,(v i).1≤d) →
            ∃ g,Poppy.Margins C r n k v g) ∧ EveryPhase.Completed F L := by
  obtain ⟨C,hk,hc,hM,hW,hV,hq,f,T,⟨F⟩⟩:= inside hG hp h
  obtain ⟨L,hL⟩:= EveryPhase.all_characters F
  exact ⟨C,f,T,F,L,hM,hc,hk,hV,hq,Reports.useFull hV ⟨F⟩,Poppy.bravo (Oasis.appears hV),hL⟩
end YM.PhysicalNext.Repeat.Legato.IterationFour
