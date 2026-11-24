import YM.Contacts.Solstice.Result
import YM.Contacts.Pulse.Epoch
/-! Adapted from Noel Columns. No costs for working epochs left unpaid here. -/
set_option autoImplicit false
noncomputable section
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
-- joint contact and PT builds kept with checkout on ACTUAL canonical kinetic data.
open Pulse.Spine
structure Passage (G:Gauge) where
  M: Metals G
  L: Rolls M.p
  A: Alloy M L
  X: Factor A
  T: Bolt A
  c: ℕ→ℝ
  K: Bid.Worth
  b: Bandage X c K
  t: ℕ→ℕ
  S: ∀ d N p,TransferData ((Labels.frames G).level d) (Issue.trail T) N p
  D: ∀ N p m:ℕ,m<N→GaugeDoor ((Issue.trail T).rep N p (m+1)) ((Issue.trail T).rep N p m)
  sanity: Chateau b (fun _ => 1) T t S D
  peace: Truce M.K A.B.a
abbrev Passage.Z (u:Passage G):= Family.mk (Issue.trail u.T) (hol G) (Labels.frames G) (localSection G) u.t u.S
/- Later can post additional demands anticipator and arrival around pre/post widths without another EXISTS of contact family.
`w` floors per MapPrices & stage, `pay` after thru shelves; e.g. use b.stall functions. -/
structure BidTri (G:Gauge) where
  w: MapPrices → ℕ→ℕ
  pay: Metals G→(ℕ→Side)→ℕ→ℝ

def admits (w:BidTri G)(p:Passage G): Prop:= ∀ i, let j:= p.A.B.a.clock.J (i+1)
    w.w p.M.K j ≤ (p.A.B.a.S.block i).val ∧ w.pay p.M p.L.L j ≤ p.A.B.a.clock.hatBeta i
-- Unconditional existence through the actual Wcmain, ranks and Seed.
variable (hG:G.Simple)
include hG
theorem tri_noel (p:BidTri G) {b:ℝ} (h:0<b) : ∃ (u:Passage G) (C:Family G), admits p u ∧ u.Z=C ∧ C.path.levels.clock.kernel.penalty=b ∧ Spec.Calibrated C ∧ C.Makes ∧ Extraction.Wcmain C ∧
    (∃ W r D, OPE.Package C W r D) ∧ Acme.Aroma C ∧ (∀ F:Extraction.Order, Cells.CellHyp C F → Grill C F∧MergeProof.East.CompleteWeak C F)∧∀ f:Extraction.Order, ∃ (g:Extraction.Order) (A:Table C.book) (L:ℕ→Table C.book) (R:Bin A) (T:Table C.book) (E:DiffPlan T), Next.Extract.Base C (f.refine g) A L R T E ∧ ∃ s:Spec.Seed C (f.refine g) T,Maxwell.Ranks T s.kernel.spin := by
  obtain ⟨k,hb,hp⟩:= YM.Axial.viable G b h
  let v: Orders:= ⟨4,fun i=>6+i,fun i=>2+i,fun i=>100+i⟩
  have hE (i:ℕ): 100 ≤ v.supportExp i:= by change (100:ℝ) ≤ 100+i; simp
  have he : Draft v:= by
    refine ⟨le_rfl,fun i j hij=> Nat.add_le_add_left hij 6,fun i j hij=> Nat.add_le_add_left hij 2,fun i j hij=>?_,fun i=> lt_of_lt_of_le (by norm_num) (hE i),fun i=>by change _ ≤6+i; omega,fun i=>by change _≤2+i; omega⟩
    change (100:ℝ)+i≤100+j; gcongr
  obtain ⟨s,T,Y,K,hX,H,l,hL,hK⟩:= himalayas_columns hG hp he (fun _=>1) (fun _ _ _=>le_rfl) (fun _=>le_rfl) hE
  obtain ⟨f,hf⟩:= chosen_flags G (ThroughLaunch.bearing s T)
  let r:= (l ⊔ f) ⊔ p.w (ThroughLaunch.bearing s T)
  let M:=ThroughLaunch.currency s T r
  obtain ⟨⟨P⟩,H⟩:= hK r (le_sup_left.trans le_sup_left)
  let Q (i j:ℕ): JointLoad.Clockwork.Menu:= ⟨Push.SectorMeasure.Chi.canonical,1,0,0,0,0,0,0,one_pos,le_rfl⟩
  let J₀ (i j:ℕ):JointLoad.Folio.Aux:=⟨40,1,1,le_rfl⟩
  let E : Next.Scheduling.Exchange:=⟨0,0,1,1,1,0,0,by norm_num⟩
  obtain ⟨w,h⟩:= H P
  obtain ⟨F,hF⟩:= h w le_rfl (fun _ _=> ⟨1,1,1,1,le_rfl,zero_lt_one,zero_lt_one⟩) (fun _ _=> E)
  obtain ⟨θ,-,hH⟩:= hF _ (fun _=>one_pos)
  let U: Delays θ:=⟨p.pay M P.L,fun _ _=>0,fun _=>1,fun _=>1⟩; obtain ⟨U', hu0, hu'⟩ := OPE.halo_delay U
  obtain ⟨V,h₁,hK⟩:= hH Q J₀ U'
  obtain ⟨D,-⟩:= Bar.exists_above V 2; let I:Wait D:= ⟨fun _=>0,fun _ _=>0,fun _=>by simp,0⟩
  obtain ⟨Y,-,H⟩:= hK V (DelayLe.refl _) D I
  obtain ⟨a,ha,hp⟩:= Wait.engine Y hG; obtain ⟨X,B,hB,R,W,c,T,t,S,D',hT,hq,h_col,h_fr,hu⟩:= H Y le_rfl le_rfl le_rfl a ha hp
  let Z:= Family.mk (Issue.trail T) (hol G) (Labels.frames G) (localSection G) t S
  change Velour Z (renal B.a) _ D' ∧ VelourArity Z _ _ D' ∧ (∀ f:Extraction.Order,MergeProof.East.CompleteWeak Z f) at hu
  obtain ⟨hc,hF,hQ,hU,hW,B₀,-,-,K₀,F₀,L,-,H⟩:=hT.reception
  have hv:Ribbons.Created Z:= ⟨_,t,S,rfl⟩
  have hπ:Acme.Aroma Z:= ⟨Ribbons.laurelE Z hG hU hu.1 hq hv hF,hq, Ribbons.fugacious Z hG hu.1⟩ -- fix argument order
  let u: Passage G:= ⟨M,P, ⟨F,θ,V,D,Y,X,B⟩, R,T,_,_,c,t,S,D',hT,hf _ fun i=> by
    have h:= B.valid.lengths; have he:= B.a.fits.sameFactor i
    change _ ≤ (B.a.S.block i).val; rw [← he,h]; exact ((show f≤r from le_sup_right.trans le_sup_left) _).trans (P.large _).need⟩
  refine ⟨u,Z, fun i=> ⟨?_, (?_ : p.pay M P.L _ ≤ _)⟩, rfl,(congr_arg KernelChoices.penalty (B.valid.kernel.trans hX)).trans hb,hc,hF,hW, ?_, hπ,fun f hf=>⟨grilled Z hF hU hq hf,hu.2.2 f⟩,fun f=>by obtain ⟨g,A,L,R,z,T,E,h,hp⟩:= H f; exact ⟨g,A,L,R,T,E,hp⟩⟩
  · have h:= B.valid.lengths; have he:= B.a.fits.sameFactor i
    change _ ≤ (B.a.S.block i).val; rw [← he,h]; exact ((show p.w M.K ≤ r from le_sup_right) _).trans (P.large _).need
  · exact ((hu0.trans h₁).beta _).trans (B.valid.pays i)
  · refine ⟨_, _, _, ⟨hU, hu.1, fun d N p hn m hm h => h_col d N p hn m hm h, h_fr, ?_, ?_, hv, hq⟩, hu.2.1⟩
    · apply hu' V h₁ Y B.a B.valid
    · assumption
end YM.PhysicalNext.Repeat.Legato
namespace YM.Pulse
open PhysicalNext.Repeat.Legato OPE Spec MergeProof Org
open Contacts.Solstice Contacts Spine
open scoped Classical Topology BigOperators
-- An actual down-payment on the keconomic approximation. Free extra delay and before-L floor & bar coupling.
-- Later apertures obtainable too directly in the proof of tri_noel.
theorem through_truce (G:Gauge)(hG:G.Simple){b:ℝ}(h:0<b)(p:BidTri G)(F:Extraction.Order): ∃ (u:Passage G), admits p u ∧ u.Z.path.levels.clock.kernel.penalty=b ∧ ∃ (f:Extraction.Order)(A:Table u.Z.book) (Z:Final u.Z (F.refine f) A) (M:Devices Z.sector.derivatives), MultipleLight Z M ∧ Nonempty (Transport.SystemBasis M) ∧ Nonempty (Thresholds M):= by
  obtain ⟨u,_,hu,rfl,hB,hC,hV,hW,hS,H,hQ,hF⟩:=tri_noel hG p h
  obtain ⟨g,A,L,R,T,E,hA,s,hN⟩:= hF F
  obtain ⟨hs,hG'⟩:= hQ (F.refine g) s.copies
  obtain ⟨M,I,hI,p⟩:=Acme.emanate (W:=E) H hG hs hG' s hA.clean.ready hA.clean.tilt
  obtain ⟨Z⟩:= Acme.glistens hC hA.clean.ready hA.clean.tilt p
  obtain ⟨P,hP⟩:= Prescription.chosen Z.room.kernel.laws.toSymmetric Z.phase.transport.injection
  let X : Devices Z.sector.derivatives := ⟨P,hP,Z.sector.turns,Z.room.kernel,Z.phase.transport.injection,Z.phase.transport.rights,Z.phase.transport.spots,Z.phase.transport.motion,fun d=> Classical.choice (MultipleContact.detector_exists d _)⟩
  exact ⟨u,hu,hB,g,T,Z,X,provided Z X rfl ⟨hs,hG,hS,A,L,R,E,hA⟩,Transport.real_basis X, ⟨(installs X (f:=fun i=>1) (fun _=>zero_lt_one)).choose⟩⟩
end YM.Pulse
