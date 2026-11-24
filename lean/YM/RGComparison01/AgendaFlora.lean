import YM.RGComparison01.AgendaWishes
import YM.UVExtension.Oasis.Fruition

/-!
# Simultaneous obligations on *the* same Factor as in Flora.

Not `Floral` with a demand met at, say, a *different underlying*
 presentation. Port the assembly into the SAME cutoff/period and expose.

 Extend `Floral` nonintrusively with the extra pricing via `RichFloral`.
 For any payable Agenda. Agenda lifts from `survives`, `uv_flowered`,
 `fruition`. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Oasis
open Function Filter Set Lattice Wilson RG PhysicalNext PhysicalNext.Repeat
open Progress.DirectedRecipe MeasureTheory Push Push.AbsoluteSums
open RG.Supply Precision Shoot Org Input Steady
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext Mallow
open WilsonStartup Time Next.Foundations UVNext.CouplingReset Legato
open Roost Spire Orchard Camp Dales Lamppost Oriel Rafter Copse Linden Metric
open SectorNext.Vacuum Hearth Pier MergeProof.Ribbons
open Source Labels Gale Mast MergeProof Cells GridApprox Accent Extra.Histories
open Swell Stock Harvest Extraction Fallow Poppy Beach Upland
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {hG:G.Simple}{X: Metals G} {D:Rolls X.p} {A : Alloy X D} {Q:Factor A} {S: Uses Q hG} {C:ℕ→ℝ}{w:Bid.Worth}{R: Bandage Q C w} {t:ℕ→ℕ}(L:Cellar S t R)
local notation "φ"=> A.B.a
set_option quotPrecheck false
open Cellar
local notation "V0"=> Cellar.yard (roseA S) L
def RichFloral (Ω : RGComparison01.Agenda G) (C : Family G) : Prop :=
    ∃ (M : Metals G) (P : Rolls M.p) (A : Alloy M P)
      (R : Roost.Factor A) (S : Uses R hG) (T : Bolt A)
      (t : ℕ → ℕ) (K : ℕ → ℝ) (w : Bid.Worth)
      (Q : Bandage R K w) (L : Cellar S t Q),
        Ω.atFactor R ∧ Arc R S T ∧ C = Cellar.yard (roseA S) L ∧ Oasis.Spring S ∧
        (∃ (hA : Arc R S T), let p := Mast.roseA S; Chateau Q (fun _ => 1) (centerB S hA) t
          (Cellar.gate p L) (Orchard.roof S p)) ∧
        Harvest.Barn S Q (fun _ => 1) L ∧
        Velour (Cellar.yard (Mast.roseA S) L) (Bandage.renal A.B.a)
          (Bandage.mutt A.B.a (fun _ => 1)) (Orchard.roof S (Mast.roseA S)) ∧
        (∃ a:ℝ,0 < a ∧ Metric.ball (0:ℂ) a ⊆ Broad A.B.a ∧
            ∀ d N p,t d ≤ N → Nonempty (Gale.Circuit S d N p Q L a)) ∧
        ∀ d m:ℕ, ∀ᶠ p:ℕ in atTop, ∃ r:ℝ, Nutrition L d (m+1) p r ∧
            ∀ (n:ℕ) (u:Fin n → (Hearth.roster L).Token), (∀ i,(u i).1 ≤ d) →
              ∃ b:ℝ, ∃ _hb:0 < b, ∃ hp:Metric.ball (0:ℂ) b ⊆ Broad A.B.a, ∃ W f,
                Beach.Shoal L p n u b hp W f m ∧ Beach.Realizes L p n u W b

lemma RichFloral.forget {Ω : RGComparison01.Agenda G} {P : Family G} (h : RichFloral (hG:=hG) Ω P) : Floral (hG:=hG) P := by
  obtain ⟨M,D,A,B,V,T,x,w,Y,U,K,-,H⟩ := h
  exact ⟨M,D,A,B,V,T,x,w,Y,U,K,H⟩
variable {Lu:Org.Bolt A}(h:Arc Q S Lu)
variable (hp: Harvest.Barn S R (fun _=>1) L) (he:Mix.paidL (Cellar.yard (roseA S) L)) (v:ℝ)(hv:0 < v)(hV:ball (0:ℂ) v ⊆ Broad A.B.a) (hQ:∀ d N p,t d ≤ N→ Nonempty (Gale.Circuit S d N p R L v))(hS :Cloud.Leases C Q.shape A.delay) (hR:∀ i j,(Q.target i j).rate ≤ -(7/16:ℝ))
variable (hs: Chateau R (fun _=>1) (centerB S h) t (Cellar.gate (Mast.roseA S) L) (Orchard.roof S (Mast.roseA S)))
    (hg:Velour (Cellar.yard (Mast.roseA S) L) (Bandage.renal A.B.a) (Bandage.mutt A.B.a (fun _=>1)) (Orchard.roof S (Mast.roseA S)))
include h hp he hv hV hQ hS hR hs hg
lemma rich_survives {Ω : RGComparison01.Agenda G} (hΩ : Ω.atFactor Q) : RichFloral (hG:=hG) Ω (Cellar.yard (Mast.roseA S) L):=by
   refine ⟨X,D,A,Q,S,_,t,C,w,R,L,hΩ,h,rfl,spring h,⟨h,hs⟩,hp,hg,⟨v,hv,hV,hQ⟩,fun d m=> ?_⟩
   filter_upwards [nourishing h hp d (m+1)] with p ⟨r,hr⟩
   refine ⟨r,hr,fun n u hu=>?_⟩
   obtain ⟨a₁,hv0,hA,V,y,hr'⟩:= sparksP L p n m d hv hV (fun _=>1) hp he u (fun d N=> hQ d N p) hS hR hr hu h
   obtain ⟨b,hb,hB,W,hK,hc⟩:= Beach.keep_prefix L p n hv0 hA u hv hV (fun d N=>hQ d N p) hr'
   exact ⟨b,hb,hB,W,y,hK,hc⟩

end YM.UVExtension.Oasis
namespace YM.PhysicalNext.Repeat.Legato
open RGComparison01
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
open YM.MergeProof MergeProof.Accent
-- Unconditional existence through the actual Wcmain, ranks and Seed.
variable (hG:G.Simple)
open UVExtension UVExtension.Harvest
/-! price from same schedule, Barn pins together all projections and histories,
    Transfers peak & radiances, see e.g. Poppy.Fountain. Real offset laws
    on `.yard` are the marked families actually tested. At the center exact
    CLOSED acquisitions via UV-stress.Weak L output. -/
include hG
theorem rich_flowered {Ω : Agenda G} (hΩ : Ω.Payable) {b:ℝ} (h:0<b) : ∃ C:Family G, C.path.levels.clock.kernel.penalty=b ∧ Spec.Calibrated C ∧ C.Makes ∧ Extraction.Wcmain C ∧
    UVExtension.Oasis.RichFloral (hG:=hG) Ω C ∧ Acme.Aroma C ∧ (∀ F:Extraction.Order, Cells.CellHyp C F → Grill C F∧MergeProof.East.CompleteWeak C F)∧∀ f:Extraction.Order, ∃ (g:Extraction.Order) (A:Table C.book) (L:ℕ→Table C.book) (R:Bin A) (T:Table C.book) (E:DiffPlan T), Next.Extract.Base C (f.refine g) A L R T E ∧ ∃ s:Spec.Seed C (f.refine g) T,Maxwell.Ranks T s.kernel.spin := by
  obtain ⟨k,hb,hp⟩:= YM.Axial.viable G b h
  let v: Orders:= ⟨4,fun i=>6+i,fun i=>2+i,fun i=>100+i⟩
  have hE (i:ℕ): 100 ≤ v.supportExp i:= by change (100:ℝ) ≤ 100+i; simp
  have he : Draft v:= by
    refine ⟨le_rfl,fun i j hij=> Nat.add_le_add_left hij 6,fun i j hij=> Nat.add_le_add_left hij 2,fun i j hij=>?_,fun i=> lt_of_lt_of_le (by norm_num) (hE i),fun i=>by change _ ≤6+i; omega,fun i=>by change _≤2+i; omega⟩
    change (100:ℝ)+i≤100+j; gcongr
  obtain ⟨s,T,Y,K,hX,H,l,hL,hK⟩:= agendaWishes hG hp he (fun _=>1) (fun _ _ _=>le_rfl) (fun _=>le_rfl) hΩ hE
  let M:=UVExtension.Case.provider s T l
  obtain ⟨⟨P⟩,H⟩:= hK l le_rfl
  let Q (i j:ℕ): JointLoad.Clockwork.Menu:= ⟨Push.SectorMeasure.Chi.canonical,1,0,0,0,0,0,0,one_pos,le_rfl⟩
  let J₀ (i j:ℕ):JointLoad.Folio.Aux:=⟨40,1,1,le_rfl⟩
  let E : Next.Scheduling.Exchange:=⟨0,0,1,1,1,0,0,by norm_num⟩
  obtain ⟨w,h⟩:= H P
  obtain ⟨F,hF⟩:= h w le_rfl (fun _ _=> ⟨1,1,1,1,le_rfl,zero_lt_one,zero_lt_one⟩) (fun _ _=> E)
  obtain ⟨θ,-,hH⟩:= hF _ (fun _=>one_pos)
  let U: Delays θ:=⟨fun _=>0,fun _ _=>0,fun _=>1,fun _=>1⟩; obtain ⟨V,h₁,hK⟩:= hH Q J₀ U
  obtain ⟨D,-⟩:= Bar.exists_above V 2; let I:Wait D:= ⟨fun _=>0,fun _ _=>0,fun _=>by simp,0⟩
  obtain ⟨Y,-,H⟩:= hK V (DelayLe.refl _) D I
  obtain ⟨a,ha,hp⟩:= Wait.engine Y hG; obtain ⟨X,B,hB,R,hθΩ,W,c,T,t,S,Hx,Hk,hT,hq,hu,hD,h_lease,h_rate,⟨hh',hH,h_Φ,h_sh⟩,hE⟩:= H Y le_rfl le_rfl le_rfl a ha hp
  let V:= Mast.centerB S Hx; let W:=Mast.cellar S c Hx t Hk; let S':= Mast.Cellar.gate (Mast.roseA S) W
  let Z:= Family.mk (Issue.trail V) (hol G) (Labels.frames G) (localSection G) t S'
  obtain ⟨hc,hF,hQ,hU,hW,B₀,-,-,K₀,F₀,L,-,H⟩:=hT.reception
  have hv:Ribbons.Created Z:= ⟨_,t,S',rfl⟩
  have hπ:Acme.Aroma Z:= ⟨Ribbons.laurelE Z hG hU hu hq hv hF,hq, Ribbons.fugacious Z hG hu⟩
  exact ⟨_,(congr_arg KernelChoices.penalty (B.valid.kernel.trans hX)).trans hb,hc,hF,hW,Oasis.rich_survives W Hx hD hQ hh' hH (hB.symm ▸ h_Φ) h_sh h_lease h_rate hT hu hθΩ, hπ,fun f hf=>⟨grilled Z hF hU hq hf,hE f⟩,fun f=>by obtain ⟨g,A,L,R,z,T,E,h,hp⟩:= H f; exact ⟨g,A,L,R,T,E,hp⟩⟩
end YM.PhysicalNext.Repeat.Legato
namespace YM.UVExtension.Oasis
open RGComparison01
open Function Set Filter MeasureTheory RG Wilson Lattice
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Extraction Climb Spec Table Ward
open Analysis Org Cells
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}

-- Also preserve the vacuum and exterior consumer through arbitrary
-- further extractions (vol/diagonal -- not the claim of mesh convergence
-- which is full and separate).
open Next.UVStress
lemma fruitionRich {Ω : Agenda G} (hΩ : Ω.Payable) (h:G.Simple)(b:ℝ)(hb:0<b): ∃ C:Family G,C.Makes∧ Spec.Calibrated C ∧ RichFloral (hG:=h) Ω C ∧ C.path.levels.clock.kernel.penalty=b ∧ Extraction.Wcmain C ∧
   (∀ d k:ℕ,∀ᶠ n in atTop,∀ r:ℕ,∀ v:Fin r→ C.book.Token,(∀ i,(v i).1 ≤ d) → ∃ f,Poppy.Margins C r n k v f) ∧
   ∀ (f:Extraction.Order),∃ (g:Extraction.Order) (T:YM.Table C.book), (∃ s:Seed C (f.refine g) T, Maxwell.Ranks T s.kernel.spin)∧ (∃ (M:MaxwellData C)(I:IR (C:=C) T)(V:DiffPlan T), I.J≠0∧UV C (f.refine g) T V M I)∧ Nonempty (Final C (f.refine g) T):=by
    obtain ⟨C,hB,hC,hM,hW,hE,H,hQ,hF⟩:= YM.PhysicalNext.Repeat.Legato.rich_flowered h hΩ hb
    refine ⟨C,hM,hC,hE,hB,hW,Poppy.bravo (appears hE.forget),fun f=>?_⟩
    obtain ⟨g,A,L,R,T,E,hA,s,hN⟩:= hF f
    obtain ⟨hs,hG⟩:= hQ (f.refine g) s.copies
    obtain ⟨M,I,hI,p⟩:=YM.MergeProof.Acme.emanate (W:=E) H h hs hG s hA.clean.ready hA.clean.tilt
    exact ⟨g,T,⟨s,hN⟩,⟨M,I,E,hI,p⟩,YM.MergeProof.Acme.glistens hC hA.clean.ready hA.clean.tilt p⟩


end YM.UVExtension.Oasis
