import YM.WilsonCoeffUV.Kinetic.Alpha
import YM.WilsonCoeffUV.Product.Report.Family
import YM.UVExtension.Reports.Ultraviolet
/-!
# Request formal-coefficient gates before invoking UV historical pipeline

For use at global witness selection time (16/the coordinator) only. Is not an
axiom on some already picked unrelated Family/Holo/RG. This adapter supplies,
simultaneously on one and the same witness, the *unchanged* UV conclusion,
same primary stencil/horizon vocabulary, ordinary numerical purchases for these
formal UV theorems, K & first-loop plans for grade alignment. Doesn't
supply the missing actual density bounds or identify canonical transfers with
`factory`; multiple comparisons and all physical tasks still require stronger
instantiation. After applying this adapter and selecting the Final use accepted
phase preservation ON THAT Final. Not further changing sequence convention.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM
open RG Lattice Next.Foundations RG.Supply Input Wilson Precision
open Function Filter
open Topology
namespace WilsonCoeffLease
variable {G:Gauge}
-- never import partner speculative assumptions
/-- Costs can be intersected with others using maxima. `T0` post protection
    choice, e.g. post/shell demands & broad optimizer before all Wait gates. -/
def Funds0 (G:Gauge): Type:= ∀ s:Sheet G,∀ P:Rolls s,∀ h:Protection P, Delays h
def Prepaid0 (_G:Gauge):Type:= KernelChoices→ℕ→ℕ

/-- Pin EXACT History. The lift/path calibration check `SeamPhase` derived later.
No infer arbitrary rotated physical perturbation scheme here. Also the parameters
from λ exponent of checkpoint path can still depend on inputs HG. -/
structure Leased (C:Family G)(K:KernelChoices)(W:Prepaid0 G)(T:Funds0 G) where
   page:Sheet G
   phases: Rolls page
   cert : Protection phases
   delays : Delays cert
   bed : Bar delays
   wait : Supply.Wait bed
   proof : Paid wait C.path.levels
   beforeL : W K≤ page.floorL
   postL : Push.PriceCompiler.DelayLe (T page phases cert) delays
   same : page.kernel=K
   opts (i:ℕ): ∃ j:ℕ,(phases.L i).val=3^j
   plans : PostCost phases
   pathH : Horizon C.path.levels
   kinase : Kin pathH (Next.Foundations.chart G)
   earns : kinase.Planned plans
   joint N p m: m≤N → (C.path.rep N p m).path=kinase.path N m
   book : C.labels=Labels.frames G
   paths : C.params=hol G
   acts i : HEq (C.localSection i) (localSection G i)

lemma triL (s:Sheet G)(g:G.Simple):∃ P: Rolls s,∀ i:ℕ, ∃ j:ℕ,(P.L i).val=3^j:=by
    choose C H using fun i => Supply.Rolls.eventually_large s g i; let M:=fun i=>(Finset.range (i+1)).sup C; have hm:Monotone M:=fun i j hij=>Finset.sup_mono (Finset.range_mono (by omega)); let L (i:ℕ) : Side:= ⟨3^(M i+1),by positivity⟩
    have hs i: Large s i (L i):=by
       apply H
       · have he : C i≤M i := Finset.le_sup (Finset.mem_range.mpr (by omega)); exact le_trans he (by change _≤3^(M i+1); exact (Nat.le_succ _).trans (Nat.lt_pow_self (n:=M i+1) (by omega)).le)
       exact (Odd.pow (n:=M i+1) (show Odd (3:ℕ) by decide))
    refine ⟨⟨L,hs,fun i j p=> pow_le_pow_right₀ (by omega) (Nat.add_le_add_right (hm p) _)⟩,fun i=> ⟨_,rfl⟩⟩
end WilsonCoeffLease

-- UV composition adapter, following accepted `uv_flowered` & `fruition`
namespace PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Bandage
open InteractingRank Next.Rank Next.Rank.Tapes RankCovariance PhysicalNext.InteractingRank.Soft
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open Next.Extract Dash YM.MergeProof MergeProof.Accent
open UVExtension UVExtension.Harvest WilsonCoeffLease Extraction Extraction.Order

-- Fine strokes at call: No further selection of unrelated Final.
theorem leasedWilson (hG:G.Simple)(k:KernelChoices)(hp:∀ P:Patch,P.Branches k G)(pL: Prepaid0 G)
    (T0:Funds0 G) : ∃ (C:Family G)(f:Extraction.Order)(T:YM.Table C.book), Nonempty (Spec.Final C f T)
    ∧ C.Makes∧ Spec.Calibrated C ∧ C.path.levels.clock.kernel=k ∧ Oasis.Floral (hG:=hG) C ∧ (Extraction.Order.mk Extraction.Sequence.full f.per).Ordered C T
    ∧ (∀ d k:ℕ, ∀ᶠ n in atTop, ∀ (r:ℕ)(v:Fin r→C.book.Token), (∀ i,(v i).1≤d)→∃ g,Poppy.Margins C r n k v g)
    ∧ Nonempty (WilsonCoeffLease.Leased C k pL T0):=by
  let v: Orders:= ⟨4,fun i=>6+i,fun i=>2+i,fun i=>100+i⟩
  have hE (i:ℕ): 100 ≤ v.supportExp i:= by change (100:ℝ) ≤ 100+i; simp
  have he : Draft v:= by
    refine ⟨le_rfl,fun i j hij=> Nat.add_le_add_left hij 6,fun i j hij=> Nat.add_le_add_left hij 2,fun i j hij=>?_,fun i=> lt_of_lt_of_le (by norm_num) (hE i),fun i=>by change _ ≤6+i; omega,fun i=>by change _≤2+i; omega⟩
    change (100:ℝ)+i≤100+j; gcongr
  obtain ⟨s,T,Y,K,hX,H,l,hL,hK⟩:= uv_wishes hG hp he (fun _=>1) (fun _ _ _=>le_rfl) (fun _=>le_rfl) hE
  let l':= l ⊔ pL k; let M:= UVExtension.Case.provider s T l'
  obtain ⟨_n,H⟩:= hK l' le_sup_left; obtain ⟨P,hP⟩:= triL M.p hG
  let Q (i j:ℕ): JointLoad.Clockwork.Menu:= ⟨Push.SectorMeasure.Chi.canonical,1,0,0,0,0,0,0,one_pos,le_rfl⟩
  let J₀ (i j:ℕ):JointLoad.Folio.Aux:= ⟨40,1,1,le_rfl⟩
  let E : Next.Scheduling.Exchange:=⟨0,0,1,1,1,0,0,by norm_num⟩
  obtain ⟨w,h⟩:= H P
  obtain ⟨F,hF⟩:= h w le_rfl (fun _ _=> ⟨1,1,1,1,le_rfl,zero_lt_one,zero_lt_one⟩) (fun _ _=> E)
  obtain ⟨θ,-,hH⟩:= hF _ (fun _=>one_pos)
  obtain ⟨V,h₁,hK⟩:= hH Q J₀ (T0 M.p P θ)
  obtain ⟨D,-⟩:= Bar.exists_above V 2; let I:Wait D:= ⟨fun _=>0,fun _ _=>0,fun _=>by simp,0⟩
  obtain ⟨Y,-,H⟩:= hK V (DelayLe.refl _) D I
  obtain ⟨a,ha,hp⟩:= Wait.engine Y hG; obtain ⟨X,B,hB,R,W,c,T,t,S,Hx,Hk,hT,hq,hu,hD,h_lease,h_rate,⟨hh',hH,h_Φ,h_sh⟩,hE⟩:= H Y le_rfl le_rfl le_rfl a ha hp
  let V':= Mast.centerB S Hx; let W:=Mast.cellar S c Hx t Hk; let S':=Mast.Cellar.gate (Mast.roseA S) W
  let Z:= Family.mk (Issue.trail V') (hol G) (Labels.frames G) (localSection G) t S'
  obtain ⟨hc,hF,hQ,hU,hW,B₀,-,-,K₀,F₀,L,-,H⟩:=hT.reception
  have hv:Ribbons.Created Z:= ⟨_,t,S',rfl⟩; have hπ:Acme.Aroma Z:= ⟨Ribbons.laurelE Z hG hU hu hq hv hF,hq,Ribbons.fugacious Z hG hu⟩
  have hr: Oasis.Floral (hG:=hG) Z:= Oasis.survives W Hx hD hQ hh' hH (hB.symm ▸ h_Φ) h_sh h_lease h_rate hT hu
  let f':=Extraction.Order.full; have hf : ∀ f:Extraction.Order, ∃ (g:Extraction.Order) (A:YM.Table Z.book) (L:ℕ→YM.Table Z.book) (R:Bin A) (T:YM.Table Z.book) (E:DiffPlan T), Next.Extract.Base Z (f.refine g) A L R T E ∧ ∃ s:Spec.Seed Z (f.refine g) T,Maxwell.Ranks T s.kernel.spin := fun f=>by obtain ⟨g,A,L,R,z,T,E,h,hp⟩:= H f; exact ⟨g,A,L,R,T,E,hp⟩
  obtain ⟨g,A,L,R₀,T,E,hA,st,hN⟩:= hf f'; let gr:Grill Z (f'.refine g):= grilled Z hF hU hq st.copies; let r':= hE (f'.refine g)
  obtain ⟨M',II,hI,tP⟩:= Acme.emanate (W:=E) hπ hG gr r' st hA.clean.ready hA.clean.tilt
  have hJ:= Acme.glistens hc hA.clean.ready hA.clean.tilt tP
  have H':M.p.kernel=k:= hX
  refine ⟨Z,_,T,hJ,hF,hc,B.valid.kernel.trans H',hr, Reports.useFull hr hJ, Poppy.bravo (Oasis.appears hr),?_⟩
  have o:= Oasis.spring Hx
  exact ⟨⟨M.p,P,θ,V,D,Y,B.valid,(show pL k≤l' from le_sup_right),h₁,H',hP,F,B.M,B.kin,B.support,fun N p m hm=> (o.actual m p N hm 0 (by rw [abs_zero]; exact o.open_at)).1,rfl,rfl,fun _=> HEq.rfl⟩⟩
end PhysicalNext.Repeat.Legato
end YM
