import YM.Juniper.Provider.Nursery
import YM.Pert.Dense.End
import YM.OPE.Levy.Endpoint
import YangMills.WilsonProof.NativeSupport.checks.ComparisonCommonWitness
/-!
# Common UV/WilsonX infrastructure/every-phase endpoint, realizing actual additional estimates on the UV branch

Adaptation of YM/OPE/Levy/Theory.lean (weak scaling and OPE in one frame on
Services + stronger supplied calendar hypothesis), YM/Pert/Dense/End.lean.
No claim of the all-orders comparison here. Order-zero Pert.Position.Crest and
OPE.Levy.Ticket cost/ranks/gauge conventions/support all as in those definitions;
not inferring a precision improvement. Do not apply inverse estimates on other
frames without proving compatibility. The stronger reader report & actual Gram
budgets intended for matching will use this same C/f/T/F and physical fields.
Note `pack.system` on the Nursery: singleton and multiple insertion transfers
use the actual `.roof` doors. Norm transitions of new analytic/smooth may
require new proofs. `Services` from Realty forgets down to existence of doors.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Juniper
open RG Lattice Function Filter Set Extraction Maxwell Analysis MeasureTheory
open Climb Org Next.UVStress Spec Table Ward Cells
open PhysicalNext PhysicalNext.Repeat
open Pert OPE Orbits
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G : Gauge} {C : Family G} {hG : G.Simple} {S : Table C.book}
variable {f : Extraction.Order}

-- Needed also to export to the Levy/threshold suppliers that depend on their actual Base.
open MergeProof.Acme
lemma first {E₀ : DiffPlan S} {M : MaxwellData C} {I : IR (C:=C) S} {X : Scaling S} {c : ℝ} {U : ∀ d, Spin.change S d} {J : S.Stress} {b : Final C f S}
    (hG : G.Simple) (hd : M.T.W=Maxwell.Free.scheme C.labels) (hT : M.T.K=Maxwell.Free.gear C.labels)
    (hJ : M.T.J=YM.UVNext.FreeStress.torch C.book.grid 1) (p : Supplier f E₀ M I X)
    (t : Tab S E₀ M I p.uv c U J) (eqb : b.sector=⟨E₀,mill M I c U,J⟩) : FirstExtension b X := by
  have he : b.sector.derivatives=E₀ := congrArg Spec.Algebra.derivatives eqb
  have hj' : (M.T.κ)⁻¹ • M.T.J = freeStress C.labels := by
    rw [kappa_eq hG hd hJ,inv_neg,inv_one,neg_smul,one_smul,hJ,common_stress]; rfl
  refine ⟨?_,fun n j q is a K hK hsep ε he => ?_,?_,fun d => ?_,fun j d => ?_⟩
  · rw [← hd,he]; exact p.fit
  · rw [(congrArg Spec.Algebra.energy eqb : b.sector.energy=J)]
    have hh := mixed_leading p t q is a j hK hsep he; rw [hj'] at hh; exact hh
  · revert he; cases b with | _ _ _ Z α phase B A action realization => cases Z with | _ E K' J' =>
      rintro rfl; exact one_line p
  · rw [he,← hd]; exact for_derivative p d
  rw [eqb,← hT]; exact rotation_lead p t d j

section start
variable {E : Extras G} (N : Nursery G hG) (h : Stock E N)
set_option quotPrecheck false
local notation "C!" => N.family

include h
lemma materials : MergeProof.Ribbons.Materials C! := by
  obtain ⟨_,hm,_,H,_,H'⟩ := h.chateau.reception
  exact ⟨hG,hm,h.pack.literal,h.pack.tabs,_,_,_,_,_,h.pack.accounting,H⟩

lemma bindings : ∃ B₀ : RankCovariance.Binding C!, B₀.world = N.A.B.M ∧ B₀.prices=N.M.K ∧ RankCovariance.Uncut C! B₀ := by
  obtain ⟨_,hm,_,_,_,B,hB,hK,H⟩ := h.chateau.reception
  exact ⟨B,eq_of_heq hB,hK,RankCovariance.uncut hm B⟩

-- not a replacement by a scaling/Final from another construction
lemma grown (f : Extraction.Order) :
    ∃ (g : Extraction.Order) (S : Table (C!).book), Services C! (f.refine g) S ∧
      ∃ (b : Final C! (f.refine g) S) (_R : Reader b.sector.derivatives b.sector.turns b.room.kernel.spin) (X : Scaling S),
        FirstExtension b X ∧ Levy.Anchored b.sector.derivatives (path X) (isoPanel X) ∧ Approaches (path X) (isoPanel X) := by
  -- keep R explicit for type but ensure downstream chooses this R (e.g., exposes Estate)
  obtain ⟨hC,hm,_,_,_,B₀,-,-,K₀,F₀,L,-,H⟩:= h.chateau.reception
  obtain ⟨g,U,L,R,z,S,E₀,_,hA,s,hN⟩ := H f
  obtain ⟨T',hM0,_⟩:= Maxwell.Free.maxwell_supplies C! hG 1 one_ne_zero
  obtain ⟨M,hJ,hM,hK,_,_,ht0,hf⟩:= YM.UVNext.FreeStress.fire hG T' 1 one_ne_zero
  have hd := hM.trans (congr_arg Lighthouse.W hM0)
  have hT := hK.trans (congr_arg Lighthouse.K hM0)
  have ⟨hs,hG'⟩ := h.order _ s.copies
  have hservices : Services C! (f.refine g) S := ⟨hs,hG,⟨_,_,_,h.pack⟩,U,L,R,E₀,hA⟩ -- nesting `∃` via notation
  have hsP : RoughFactory C! := ⟨_,_,_,h.pack.toTableTickets⟩
  obtain ⟨hfo,I,X,hI,hX,hY,hZ,hM',hA',hp,ha⟩ := Levy.readyM hA hG hsP hG' s.cutoff s.ordered s.generic s.kernel s.copies hA.clean.ready
    hA.clean.tilt (cap_given s.corrected) M.T M.hT M.lit.edges M.lit.pales M.lit.hers hf h.aroma
  let p : Supplier (f.refine g) E₀ M I X :=
    ⟨⟨s,hfo,hp,ha,hs⟩,hA.clean.ready,hA.clean.tilt,hI,hX,hf,hY,hZ,hM'⟩
  have ht := Bid.station M E₀ I p.uv YM.Outer.miles Work.A01.answer Work.A02.answer Work.A03.answer
    Work.A04.answer Work.A05.answer Work.A06.answer Work.A07.answer Work.A08.answer
    Work.A09.answer Work.A10.answer Work.A11.answer Work.A13.answer Work.A14.answer
    Work.A15.answer Work.A16.answer Work.A17.answer
  obtain ⟨c,u,J,t,K,hK'⟩ := ht.picks E₀ M I p.uv p.ider p.deriv
  obtain ⟨b,eqb⟩ := withFinal hC p.uv c u J t hK'
  obtain ⟨R,hR⟩:= Prescription.chosen b.room.kernel.laws.toSymmetric b.phase.transport.injection
  let r : Reader b.sector.derivatives b.sector.turns b.room.kernel.spin :=
    ⟨R,hR,b.room.kernel,b.phase.transport.injection,b.phase.transport.rights,b.phase.transport.spots⟩
  refine ⟨g,S,hservices,b,r,X,?_,eqb.symm ▸ hA',p.limit_⟩
  exact first hG hd hT hJ p t eqb
end start

open Pert.Position Pert.Parity
/-- Shared prereq on the WilsonX-independent side, including the known physical order-zero match
 on the weak scaling X. On the Phase side stronger than the BASELINE EveryPhase interface (includes
 e.g. every-phase OPE in *these* fields as in the docs of those components). No accuracy beyond
 those APIs asserted. Binding stronger settings in these records doesn't justify convergence rates. -/
structure Realty (E : Extras G) (F : Spec.Final C f S)
    (R : OPE.Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (L : EveryPhase.Almanac F)
    (X : Scaling S) (hG : G.Simple) : Prop where
  nursery : ∃ N : Nursery G hG, Stock E N ∧ C=N.family
  schedules : Kinetic.Conversion C ∧ Pert.Dense.Rectangles C ∧ MergeProof.Ribbons.Plenty C ∧ MergeProof.Ribbons.Materials C
  estimates : C.Makes ∧ Spec.Calibrated C ∧ UVExtension.Oasis.Floral (hG := hG) C ∧ Wcmain C ∧
    (Extraction.Order.mk Extraction.Sequence.full f.per).Ordered C S ∧
    (∀ d k : ℕ, ∀ᶠ n in atTop, ∀ (r : ℕ) (v : Fin r → C.book.Token), (∀ i, (v i).1 ≤ d) →
      ∃ g, UVExtension.Poppy.Margins C r n k v g)
  completed : EveryPhase.Completed F L
  first : Pert.FirstExtension F X ∧ Position.Crest X ∧ Triangle.TriangleBranch X ∧ Flow.RunningPort C f ∧
    ∃ (n:ℕ)(Q:Conditions C.labels 4 n) (φ : Position.Ledger Q→Position.Buffer C.labels 4) (J:Module.End ℝ (Fin n→ℝ)), CleanProfiles Q ∧ BoardAttains Q X φ ∧ Resident F X φ ∧ Parity.Fair Q J ∧ Parity.ParityFields φ ∧ Pert.Scale.Patch F X φ
  readout : Services C f S ∧ Sparse.Quiet F R ∧ Nesting.Uniform F R ∧ Foundation F R ∧ Levy.Ticket F R X ∧ Short.Partial F R X ∧ Approaches (path X) (isoPanel X)

open UVExtension
lemma Realty.avail {E : Extras G} {N : Nursery G hG} (h : Stock E N)
    (f : Extraction.Order) :
    ∃ (g: Extraction.Order) (S : Table N.family.book) (F : Final N.family (f.refine g) S), ∃ R L X, Realty E F R L X hG := by
  obtain ⟨g,T,hservices,F,R,X,hX,hY,hA⟩ := grown N h f
  obtain ⟨L,hC⟩:= EveryPhase.all_characters F
  obtain ⟨hc,hm,_,_,hW,H⟩:= h.chateau.reception
  refine ⟨g,T,F,R,L,X,⟨N,h,rfl⟩,⟨Kinetic.converted _ hG h.plenty hm,h.rectangles,h.plenty,materials N h⟩,
    ⟨hm,hc,h.floral,hW,Reports.useFull h.floral ⟨F⟩, Poppy.bravo (Oasis.appears h.floral)⟩,hC,?_,
    ⟨hservices,Sparse.quiet _ _ hservices,Nesting.uniform _ _ hservices,Orbits.produce _ _ hservices,Levy.tickets _ _ _ hY hservices hX, Short.wave _ _ _ hX hservices,hA⟩⟩
  obtain ⟨n,Q,J,hq,hJ,hClean⟩ := parity_four N.family hG
  have hr := credible F X hX
  obtain ⟨φ,hf⟩ := hr.position _ _ Q hClean hq
  exact ⟨hX,hr,Triangle.attachTriangle hG hX, Flow.running_port hG hm _,n,Q,φ,J,hClean,hf,
    residency F X hX hG hClean hf,hJ,fields_generator hJ hClean hf.toMode.patch,Pert.Scale.patch_ready hG hX hClean hf.toMode.patch⟩

theorem shared (G : Gauge) (hG : G.Simple) (penalty : ℝ) (hp : 0 < penalty) (E : Extras G) :
    ∃ (C : Family G) (f : Extraction.Order) (T : Table C.book) (F : Final C f T), ∃ R L X,
      C.path.levels.clock.kernel.penalty=penalty ∧ Realty E F R L X hG := by
  obtain ⟨N,hP,h⟩ := purchase E hG penalty hp
  obtain ⟨g,S,F,R,L,X,H⟩ := Realty.avail h Extraction.Order.full
  exact ⟨_,_,S,F,R,L,X,hP,H⟩
end YM.Juniper
