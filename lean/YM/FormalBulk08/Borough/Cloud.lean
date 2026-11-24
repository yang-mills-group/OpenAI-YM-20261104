import YM.FormalBulk08.Borough.Stats
import YM.UVExtension.Reports.Ultraviolet

/-! Same installer scope as stock Upland, with optional extra phase before
launch. Explicit admissible schedules, existence OVER the proposed actual
provider type, keeping their stronger Floral witness too. This makes no
inferences about previously chosen Final and doesn't compare actual trajectories
for other witnesses. Select at construction time once with extra financial gates. -/
set_option autoImplicit false
noncomputable section
-- some namespaces of Recipe expect reusing its root
namespace YM.PhysicalNext.Repeat.Legato
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
variable (hG:G.Simple)
open UVExtension UVExtension.Harvest FormalBulk08.Borough

-- Keep shared variables incl stencils and Hol; `Fields` equality proof relevant. Include Dir export.
structure Provenance (G:Gauge) (C:Family G) (ρ:ChartRatio G) :Prop where
    stencil : C.params=(hol G)
    tie : C.labels =Labels.frames G
    sold : HEq C.localSection (localSection G)
    vacuum : ∃ (J: Horizon C.path.levels) (A:Kin J ρ) (P:Sheet G) (R:Rolls P)(Q:PostCost R), A.Planned Q ∧ (∀ N n m,m≤ N→(C.path.rep N n m).path=A.path N m) ∧∀ N n m,m<N → |C.path.β N n m-C.path.β N n (m+1)-A.alpha N m|≤ 1
variable {K:KernelChoices}{v:Orders}(hp :∀ p : Patch,p.Branches K G)(hv:ThroughLaunch.Draft v)(he:∀ i,100 ≤ v.supportExp i)
-- Can pay more at these stages: Floors l≥χ, entrance gates Any x & Delays E...
include hG hp hv he
lemma uv_canopies {O:FormalBulk08.Spigot.Herald} (X₀:FormalBulk08.Borough.Window G K) (χ:ℕ→ℕ)(P : Levels G → Prop) (hP:∀ (s:Sheet G),s.kernel=K→∀ (D:Rolls s)(T:Protection D)(V: Delays T),∃ Y: Delays T,DelayLe V Y∧∀ Z: Delays T,DelayLe Y Z→∀ (A:Bar Z) (I:Wait A)(L:Levels G), Paid I L→ P L): ∃ C:Family G, C.path.levels.clock.kernel=K ∧ Spec.Calibrated C ∧ C.Makes ∧ Extraction.Wcmain C ∧ UVExtension.Oasis.Floral (hG:=hG) C ∧ Acme.Aroma C ∧ (∀ F:Extraction.Order, Cells.CellHyp C F → Grill C F∧MergeProof.East.CompleteWeak C F) ∧ (∀ f:Extraction.Order, ∃ (g:Extraction.Order) (A:Table C.book) (L:ℕ→Table C.book) (R:Bin A) (T:Table C.book) (E:DiffPlan T), Next.Extract.Base C (f.refine g) A L R T E ∧ ∃ s:Spec.Seed C (f.refine g) T,Maxwell.Ranks T s.kernel.spin) ∧ Provenance G C (chart G) ∧ FormalBulk08.Borough.Evergreens K O (Labels.frames G).level (hol G) (chart G) X₀ C.path.levels ∧ C.path.levels.clock.J 0=v.first ∧ (χ≤ fun i=>(C.path.levels.clock.factor i).val)∧P C.path.levels := by
  obtain ⟨s,T,Y,K',hX,G',l,hL,hK⟩:= uv_wishes hG hp hv (fun _=>1) (fun _ _ _=>le_rfl) (fun _=>le_rfl) he
  obtain ⟨J,hJ,hj⟩:= funded_before K X₀ (chart G) (Labels.frames G).level (hol G) (χ ⊔ l)
  have hl := sup_le_iff.mp hJ; let M:= UVExtension.Case.provider s T J
  obtain ⟨⟨P⟩,H⟩:= hK J hl.2
  let Q (i j:ℕ): JointLoad.Clockwork.Menu:= ⟨Push.SectorMeasure.Chi.canonical,1,0,0,0,0,0,0,one_pos,le_rfl⟩
  let J₀ (i j:ℕ):JointLoad.Folio.Aux:=⟨40,1,1,le_rfl⟩
  let E : Next.Scheduling.Exchange:=⟨0,0,1,1,1,0,0,by norm_num⟩
  obtain ⟨w,h⟩:= H P
  obtain ⟨F,hF⟩:= h w le_rfl (fun _ _=> ⟨1,1,1,1,le_rfl,zero_lt_one,zero_lt_one⟩) (fun _ _=> E)
  obtain ⟨θ,-,hH⟩:= hF _ (fun _=>one_pos)
  let U: Delays θ:=⟨fun _=>0,fun _ _=>0,fun _=>1,fun _=>1⟩; obtain ⟨V,h₁,hK⟩:= hH Q J₀ U
  obtain ⟨X',hu,-,H'⟩:= counter_day K O (Labels.frames G).level (hol G) (chart G) X₀ V
  obtain ⟨Z',hZ,hR⟩:= hP M.p hX P θ X'
  obtain ⟨D,-⟩:= Bar.exists_above Z' 2; let I:Wait D:= ⟨fun _=>0,fun _ _=>0,fun _=>by simp,0⟩
  obtain ⟨Y,-,H⟩:= hK Z' (hu.trans hZ) D I
  obtain ⟨a,ha,hp⟩:= Wait.engine Y hG; obtain ⟨X,B,hB,R,W,c,T',t,S,Hx,Hk,hT,hq,hu',hD,h_lease,h_rate,⟨hh',hH,h_Φ,h_sh⟩,hE⟩:= H Y le_rfl le_rfl le_rfl a ha hp
  let V:= Mast.centerB S Hx; let W:=Mast.cellar S c Hx t Hk; let S':= Mast.Cellar.gate (Mast.roseA S) W
  let Z:= Family.mk (Issue.trail V) (hol G) (Labels.frames G) (localSection G) t S'
  obtain ⟨hc,hF,hQ,hU,hW,B₀,-,-,K₀,F₀,L,-,H⟩:=hT.reception
  have hv:Ribbons.Created Z:= ⟨_,t,S',rfl⟩
  have hπ:Acme.Aroma Z:= ⟨Ribbons.laurelE Z hG hU hu' hq hv hF,hq,Ribbons.fugacious Z hG hu'⟩
  have hw (i): J i≤ (P.L i).val := (P.large i).need
  refine ⟨Z,B.valid.kernel.trans hX,hc,hF,hW,Oasis.survives W Hx hD hQ hh' hH (hB.symm ▸ h_Φ) h_sh h_lease h_rate hT hu', hπ,fun f hf=>⟨grilled Z hF hU hq hf,hE f⟩,(fun f=>by obtain ⟨g,A,L,R,z,T,E,h,hp⟩:= H f; exact ⟨g,A,L,R,T,E,hp⟩),⟨rfl,rfl,HEq.rfl,?_⟩, FormalBulk08.Borough.launch hj hw (H' _ hZ) B.valid,B.valid.firstZero.trans G'.first,?_,hR _ (.refl _) D Y B.a B.valid⟩
  · refine ⟨B.M,B.kin,M.p,P,F,B.support,fun N p m hm=>?_,fun N p m hm=>(V.moves N m p hm).δ⟩
    have hh :=((V.sticks N p).prices m (Nat.zero_le _) hm).1.path
    change (V.history N p m).path=B.kin.path N m; exact hh.trans (by change B.bake.path N m=B.kin.path N m;rw [B.bases])
  intro i; change _≤ (B.a.clock.factor i).val; rw [B.valid.lengths]; exact (hl.1 i).trans (hw i)
lemma uv_shaded {O:FormalBulk08.Spigot.Herald} (X₀:FormalBulk08.Borough.Window G K) (χ:ℕ→ℕ): ∃ C:Family G, C.path.levels.clock.kernel=K ∧ Spec.Calibrated C ∧ C.Makes ∧ Extraction.Wcmain C ∧ UVExtension.Oasis.Floral (hG:=hG) C ∧ Acme.Aroma C ∧ (∀ F:Extraction.Order, Cells.CellHyp C F → Grill C F∧MergeProof.East.CompleteWeak C F) ∧ (∀ f:Extraction.Order, ∃ (g:Extraction.Order) (A:Table C.book) (L:ℕ→Table C.book) (R:Bin A) (T:Table C.book) (E:DiffPlan T), Next.Extract.Base C (f.refine g) A L R T E ∧ ∃ s:Spec.Seed C (f.refine g) T,Maxwell.Ranks T s.kernel.spin) ∧ Provenance G C (chart G) ∧ FormalBulk08.Borough.Evergreens K O (Labels.frames G).level (hol G) (chart G) X₀ C.path.levels ∧ C.path.levels.clock.J 0=v.first ∧ χ≤ fun i=>(C.path.levels.clock.factor i).val := by
  have hp' (s:Sheet G) (p:s.kernel=K)(D:Rolls s)(T:Protection D)(V:Delays T) : ∃ Y:Delays T,DelayLe V Y ∧ ∀ Z:Delays T,DelayLe Y Z→∀ (A:Bar Z)(I:Wait A)(L:Levels G),Paid I L→True:= ⟨V,.refl _,fun _ _ _ _ _ _=> trivial⟩
  obtain ⟨C,a,b,c,d,f,H,U,T,hA,hG',hT,h',_⟩:= uv_canopies (O:=O) hG hp hv he X₀ χ (fun _=>True) hp'
  exact ⟨C,a,b,c,d,f,H,U,T,hA,hG',hT,h'⟩
end YM.PhysicalNext.Repeat.Legato
