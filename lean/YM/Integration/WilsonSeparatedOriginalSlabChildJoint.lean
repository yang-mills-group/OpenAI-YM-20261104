import YM.Integration.WilsonSeparatedOriginalSlabJoint
import YM.Integration.WilsonSeparatedOriginalSlabChildLaw

/-! The complete global nonproduct profile under the genuine translated Wilson conditional, at its earlier held unit. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabChildJoint
open Function Set Finset MeasureTheory Lattice Wilson RG Source Extraction RG05Readout RG05Readout.Address RG05Readout.Native
open RG05Readout.Nuclear RG05Readout.Pulse RG05Readout.Records RG05Readout.Flatten PhysicalNext.Repeat.Legato
open WilsonSeparatedOriginalPairedFolio WilsonSeparatedOriginalSlabWave
open scoped BigOperators Classical Topology
variable {G:Gauge}(R:Run G){n N per u:ℕ}(s:Fin 3 → ℕ)(v:(i:Fin 3) → Palette R.family (s i))
  (o:Fin 3 → Site (R.family.side n per))(top:n ≤ N)
local notation "HH"=>Config G (R.family.side N per)
local notation "Z"=>Pulse.scalp (p:=per) s v o top
local notation "μ"=>WilsonMacroscopicRichFlatPosteriorLaw.law R N per

open private test matchAt productCost finiteCost regular from YM.Integration.WilsonSeparatedOriginalSlabJoint
open WilsonSeparatedOriginalSlabChildSites
variable (un:u+1 ≤ n)(A:Ratio (R.family.side u per) (R.family.side n per))(c:Site (R.family.side n per))
local notation "uN"=>un.trans top
local notation "π"=>pull 1 ((R.family.S.toDepth top per).embed c)
local notation "K"=>scan R s v (site A o c) top uN 1

private theorem tested (f:Fin 3 → Body):
    (∫W,test R s v o top (π W) (joint univ f) ∂(μ uN 1))=K (joint univ f):=by
  let P:C(HH,ℂ):=⟨fun W=>test R s v o top (π W) (joint univ f),(productCost R s v o top f).comp (continuous_pull ..)⟩
  change WilsonSeparatedOriginalResidentExpectation.mean R uN 1 P=_
  rw [WilsonSeparatedOriginalResidentExpectation.value,WilsonSeparatedOriginalSlabWave.clinics]
  have physical: (P:HH→ℂ)=WilsonSeparatedOriginalSlabChildLaw.marks R (N:=N) s v o f univ ∘ π:=by
    funext W;change Pulse.scalp (p:=per) s v o top (joint univ f) (π W)=_
    rw [Pulse.carving];rfl
  rw [physical]
  exact WilsonSeparatedOriginalSlabChildLaw.original R (Nat.le_of_succ_le un) top A s v o c f univ

variable {B:Type*}{allow:(Fin 3 → Body) → Prop}{book:(Fin 3 → Body) → (B → ℂ) → Prop}
private theorem applied (g:Body)(L:List (Entry s allow book)):
    (∫W,exposed g L (test R s v o top (π W)) ∂(μ uN 1))=exposed g L (K):=by
  letI:=WilsonMacroscopicRichFlatPosteriorLaw.prob R (per:=per) uN le_rfl 1
  have motion:Continuous (π:HH→HH):=continuous_pull ..
  induction L with
  | nil=>exact integral_zero ..
  | cons e L ih=>
    change (∫W,ink g e*test R s v o top (π W) (joint univ e.test)+exposed g L (test R s v o top (π W)) ∂(μ uN 1))=_
    have finite:Integrable (fun W:HH=>ink g e*test R s v o top (π W) (joint univ e.test)) (μ uN 1):=
      (((productCost R s v o top e.test).comp (continuous_pull ..)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).const_mul _
    have old:Integrable (fun W:HH=>exposed g L (test R s v o top (π W))) (μ uN 1):=
      ((finiteCost R s v o top g L).comp motion).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [integral_add finite old,integral_const_mul,tested R s v o top un A c e.test,ih]
    rfl

theorem parent {r η X:ℝ}(rp:0<r)(room:r ≤ R.family.S.a n)
    (ep:0<η)(small:η ≤ 1)(Ψ:Wave (Fin 3))(rank:ℕ)(grade:(∑i:Fin 3,(s i+2))+4*Fintype.card (Fin 3)<rank+1)
    (scatter:Scattering Ψ η)(xp:0 ≤ X)(sizeX:Tall Ψ (rank+1) 1 X)(g:Body):
    (∫W,Pulse.meet s v r Ψ top o g (π W) ∂(μ uN 1))=∫z in Native.box,g.val z*K (cropX Ψ o r z):=by
  obtain ⟨F,source,jets⟩:=regent s (C:=R.family) (p:=per) top o r η Ψ rp room ep small grade scatter xp sizeX
  let blank:=fun (_:Fin 3 → Body) (_:Unit → ℂ)=>True
  obtain ⟨L,_,represented⟩:=WilsonSeparatedOriginalPairedFolio.issued (book:=blank) source (fun _ _=>⟨fun _=>0,trivial⟩)
  have eq (z:E4)(hz:z∈Native.box):∀k ≤ ∑i,s i,∀t:Fin 3 → Site (R.family.S.toDepth top per).count,
      pie (submitted L z) (cropX Ψ o r z) k (placeR (R.family.S.toDepth top per) ∘ t):=by
    rw [represented hz];exact jets z
  have one (W:HH):Pulse.meet s v r Ψ top o g W=exposed g L (test R s v o top W):=by
    rw [←WilsonSeparatedOriginalPairedFolio.measured]
    apply setIntegral_congr_fun Pert.Cellular.cells_compact.measurableSet;intro z hz
    exact congrArg (fun v:ℂ=>g.val z*v) (matchAt R s v o top W _ _ (eq z hz)).symm
  simp_rw [one]
  rw [applied R s v o top un A c g L,←WilsonSeparatedOriginalPairedFolio.measured]
  apply setIntegral_congr_fun Pert.Cellular.cells_compact.measurableSet;intro z hz
  exact congrArg (fun v:ℂ=>g.val z*v) (WilsonSeparatedOriginalSlabWave.same R s v (site A o c) top uN 1 _ _ (eq z hz))

theorem original    {r η X:ℝ}(rp:0<r)(room:r ≤ R.family.S.a n)(ep:0<η)(small:η ≤ 1)(Ψ:Wave (Fin 3))(rank:ℕ)
    (grade:(∑i:Fin 3,(s i+2))+4*Fintype.card (Fin 3)<rank+1)(scatter:Scattering Ψ η)(xp:0 ≤ X)
    (sizeX:Tall Ψ (rank+1) 1 X)(g:Body)(m:ℕ):
    actualTransport R.family (N:=N) (Pulse.constellation s v r Ψ top m g ∘ π) (Nat.le_of_succ_le uN) 1=
      Pulse.premiums R.family s m n r*
        ∑o:Fin 3 → Site (R.family.side n per), ∫z in Native.box,g.val z*scan R s v (site A o c) top uN 1 (cropX Ψ o r z):=by
  let P:ContinuousMap HH ℂ:=⟨Pulse.constellation s v r Ψ top m g ∘ π,(WilsonSeparatedOriginalReplicaRegularity.physical s v top Ψ r m g).comp (continuous_pull ..)⟩
  have certified:=WilsonSeparatedOriginalResidentExpectation.value R uN 1 P
  change actualTransport R.family (N:=N) (P:HH→ℂ) _ 1=_
  rw [←certified]
  letI:=WilsonMacroscopicRichFlatPosteriorLaw.prob R (per:=per) uN le_rfl 1
  change (∫W,Pulse.constellation s v r Ψ top m g (π W) ∂(WilsonMacroscopicRichFlatPosteriorLaw.law R N per uN 1))=_
  simp only [Pulse.constellation,Pi.smul_apply,Finset.sum_apply,smul_eq_mul,integral_const_mul]
  have motion:Continuous (π:HH→HH):=continuous_pull ..
  have live (o:Fin 3 → Site (R.family.side n per)):Integrable (fun W:HH=>Pulse.meet s v r Ψ top o g (π W)) (μ uN 1):=
    ((regular R s v o top Ψ r g).comp motion).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_finsetSum univ (fun o _=>live o)]
  congr 1
  apply sum_congr rfl;intro o _
  exact parent R s v o top un A c rp room ep small Ψ rank grade scatter xp sizeX g


end YM.Integration.WilsonSeparatedOriginalSlabChildJoint
