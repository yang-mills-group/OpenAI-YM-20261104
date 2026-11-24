import YM.OPE.Compatible.Oasis.Ball
import YM.OPE.Compatible.Niche.Chop
/-! # Obtaining sensor support on any slot of the true family. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Owl
open Function Filter MeasureTheory Spec Lattice RG Wilson Source Cov Allot MergeProof Next.Extract Dash Analysis Extra.Histories Next.Rank CardinalQ Spells
open scoped Topology BigOperators Classical
variable {d k m N p:ℕ}{Y:Side}{G:Gauge}{C:Family G}(T:C.Makes)
local notation "A"=>C.path.levels
local notation "X"=>C.label d
local notation "X0"=>C.labels.level d
variable (hp:C.ref d ≤ m)(hy:m ≤ N)
include hp T hy
local notation "λv"=>Lot T hp hy p
lemma pegL : IsLinearMap ℂ (λv):= (LinearMap.isLinear _ : IsLinearMap ℂ ((C.factory d N p).terminal.symm.toLinearMap.comp (Pinwheel T hp hy p).symm.toLinearEquiv.toLinearMap))
lemma ζTrace : Extra.Histories.Ledger (X0) (C.S.side m p) (Stepm T hp hy p):=by
       let P:=C.factory d N p; obtain ⟨hx,hv,hf,hz⟩:= (T.calibrated d N p (hp.trans hy)).linear m hp hy; have hu:= (pegL T hp hy (p:=p)); constructor
       · exact ((hx.mk' _).comp (hu.mk' _)).isLinear
       · exact ((hv.mk' _).comp (hu.mk' _)).isLinear
       · exact ((hf.mk' _).comp (hu.mk' _)).isLinear
       intro v; unfold Stepm; rw[hu.map_zero]; exact hz _
set_option quotPrecheck false
local notation "a0"=>(A).params m
local notation "Q"=> C.path.rep N p m
local notation "T'"=>(A).clock
omit hp in
lemma tagC : CardinalQ.Tag (a0) ((A).clock.hatBeta m) (Q).p (Q).beta:=by
       have h:= T.wilson.represents N p m hy; rw [h.vac]; exact ⟨rfl,rfl,rfl,rfl,rfl,h.band⟩
lemma prognosis : Registered ((A).clock.hatBeta m) (a0) C.params (Q) (C.localSection d) (Stepm T hp hy p):=by
       let Xp:= C.factory d N p; let b:=(T).calibrated d N p (hp.trans hy); have hp':(Q).p=(A).budget m:=(T.wilson.represents _ _ _ hy).vac; refine ⟨tagC T hy,⟨ζTrace T hp hy,fun v=> ⟨b.format m hp hy (λv v),?_,fun i=>?_⟩,lire T hp hy⟩⟩
       · have hK:= b.cap m hp hy (λv v); rw [lire T hp hy v (p:=p)] at hK; exact hK
       rw [hp']; exact T.priced d m p hp 0 i -- budget
end YM.OPE.Owl
