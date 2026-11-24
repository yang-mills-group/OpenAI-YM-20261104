import YM.Integration.WilsonSeparatedOriginalSlabAtlas

/-! A single positive Wilson conditional integrates the complete physical constellation before the scalar grade-zero comparison. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabJoint
open Function Set Finset MeasureTheory Lattice Wilson RG Source Extraction RG05Readout RG05Readout.Address RG05Readout.Native
open RG05Readout.Nuclear RG05Readout.Pulse RG05Readout.Records RG05Readout.Flatten PhysicalNext.Repeat.Legato
open WilsonSeparatedOriginalPairedFolio WilsonSeparatedOriginalSlabWave
open scoped BigOperators Classical Topology
variable {G:Gauge}(R:Run G){n N per u:ℕ}(s:Fin 3 → ℕ)(v:(i:Fin 3) → Palette R.family (s i))
  (o:Fin 3 → Site (R.family.side n per))(top:n ≤ N)
local notation "HH"=>Config G (R.family.side N per)
local notation "Z"=>Pulse.scalp (p:=per) s v o top
local notation "μ"=>WilsonMacroscopicRichFlatPosteriorLaw.law R N per

private def test (W:HH):Wave (Fin 3) →ₗ[ℂ] ℂ:=(LinearMap.proj W).comp Z

private theorem matchAt (W:HH)(φ Ψ:Wave (Fin 3))
    (eq:∀d ≤ ∑i,s i,∀t:Fin 3 → Site (R.family.S.toDepth top per).count,pie φ Ψ d (placeR (R.family.S.toDepth top per) ∘ t)):
    test R s v o top W φ=test R s v o top W Ψ:=by
  change Z φ W=Z Ψ W
  rw [←WilsonSeparatedOriginalReplicaRegularity.diagonal s v o top φ W,←WilsonSeparatedOriginalReplicaRegularity.diagonal s v o top Ψ W,
    WilsonSeparatedOriginalReplicaWave.cuts s v o top φ Ψ eq]

private theorem productCost (f:Fin 3 → Body):Continuous (fun W:HH=>test R s v o top W (joint univ f)):=by
  change Continuous (fun W=>Z (joint univ f) W)
  rw [Pulse.carving]
  exact continuous_finsetProd _ (fun i _=>Records.clinic_cut ..)

variable {B:Type*}{allow:(Fin 3 → Body) → Prop}{book:(Fin 3 → Body) → (B → ℂ) → Prop}

private theorem finiteCost (g:Body)(L:List (Entry s allow book)):
    Continuous (fun W:HH=>exposed g L (test R s v o top W)):=by
  induction L with
  | nil=>exact continuous_const
  | cons e L ih=>
    exact (continuous_const.mul (productCost R s v o top e.test)).add ih

private theorem applied (g:Body)(L:List (Entry s allow book))(uN:u+1 ≤ N)(U:Config G (R.family.side u per)):
    (∫W,exposed g L (test R s v o top W) ∂(μ uN U))=exposed g L (scan R s v o top uN U):=by
  letI:=WilsonMacroscopicRichFlatPosteriorLaw.prob R uN le_rfl U
  induction L with
  | nil=>exact integral_zero ..
  | cons e L ih=>
    change (∫W,ink g e*test R s v o top W (joint univ e.test)+exposed g L (test R s v o top W) ∂(μ uN U))=_
    have finite:Integrable (fun W:HH=>ink g e*test R s v o top W (joint univ e.test)) (μ uN U):=
      ((productCost R s v o top e.test).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).const_mul _
    rw [integral_add finite
      ((finiteCost R s v o top g L).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)), integral_const_mul,ih]
    rfl

theorem parent (uN:u+1 ≤ N)(U:Config G (R.family.side u per)){r η X:ℝ}(rp:0<r)(room:r ≤ R.family.S.a n)
    (ep:0<η)(small:η ≤ 1)(Ψ:Wave (Fin 3))(rank:ℕ)(grade:(∑i:Fin 3,(s i+2))+4*Fintype.card (Fin 3)<rank+1)
    (scatter:Scattering Ψ η)(xp:0 ≤ X)(sizeX:Tall Ψ (rank+1) 1 X)(g:Body):
    (∫W,Pulse.meet s v r Ψ top o g W ∂(μ uN U))=∫z in Native.box,g.val z*scan R s v o top uN U (cropX Ψ o r z):=by
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
  rw [applied R s v o top g L uN U,←WilsonSeparatedOriginalPairedFolio.measured]
  apply setIntegral_congr_fun Pert.Cellular.cells_compact.measurableSet;intro z hz
  exact congrArg (fun v:ℂ=>g.val z*v) (WilsonSeparatedOriginalSlabWave.same R s v o top uN U _ _ (eq z hz))

private theorem regular (Ψ:Wave (Fin 3))(r:ℝ)(g:Body):Continuous (Pulse.meet s v r Ψ top o g):=by
  have eq:(fun W:HH=>WilsonSeparatedOriginalReplicaRegularity.meeting s v o top Ψ r g (fun _=>W))=Pulse.meet s v r Ψ top o g:=by
    funext W;unfold WilsonSeparatedOriginalReplicaRegularity.meeting Pulse.meet;simp_rw [WilsonSeparatedOriginalReplicaRegularity.diagonal]
  rw [←eq];exact (WilsonSeparatedOriginalReplicaRegularity.regular s v o top Ψ r g).comp (continuous_pi (fun _=>continuous_id))

theorem original {T:Type*}(age:T → ℕ)(opened:∀a,age a+1 ≤ N)(hold:(a:T) → Config G (R.family.side (age a) per))
    {r η X:ℝ}(rp:0<r)(room:r ≤ R.family.S.a n)(ep:0<η)(small:η ≤ 1)(Ψ:Wave (Fin 3))(rank:ℕ)
    (grade:(∑i:Fin 3,(s i+2))+4*Fintype.card (Fin 3)<rank+1)(scatter:Scattering Ψ η)(xp:0 ≤ X)
    (sizeX:Tall Ψ (rank+1) 1 X)(g:Body)(m:ℕ)(a:T):
    actualTransport R.family (N:=N) (Pulse.constellation s v r Ψ top m g) (Nat.le_of_succ_le (opened a)) (hold a)=
      WilsonSeparatedOriginalSlabAtlas.whole R s v top age opened hold r Ψ m g a:=by
  let P:ContinuousMap HH ℂ:=⟨Pulse.constellation s v r Ψ top m g,WilsonSeparatedOriginalReplicaRegularity.physical s v top Ψ r m g⟩
  have certified:=WilsonSeparatedOriginalResidentExpectation.value R (opened a) (hold a) P
  change actualTransport R.family (N:=N) (P:HH→ℂ) _ (hold a)=_
  rw [←certified]
  letI:=WilsonMacroscopicRichFlatPosteriorLaw.prob R (opened a) le_rfl (hold a)
  change (∫W,Pulse.constellation s v r Ψ top m g W ∂(WilsonMacroscopicRichFlatPosteriorLaw.law R N per (opened a) (hold a)))=_
  simp only [Pulse.constellation,Pi.smul_apply,Finset.sum_apply,smul_eq_mul,integral_const_mul]
  rw [integral_finsetSum _ (fun o _=>(regular R s v o top Ψ r g).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  unfold WilsonSeparatedOriginalSlabAtlas.whole;congr 1
  apply sum_congr rfl;intro o _
  exact parent R s v o top (opened a) (hold a) rp room ep small Ψ rank grade scatter xp sizeX g

end YM.Integration.WilsonSeparatedOriginalSlabJoint
