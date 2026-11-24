import YM.FVAAlt2.Boot.Physical
import YM.Comparison.RG02.Thermal.Kept
import YM.FVAAlt2.Block.Starts
import YM.FVAAlt2.Rocket.Export
/-! # Genuine top of ANY Block trajectory. Boot pension all orders & W initial, marker powers exactly compensated. No moving period comparison cost from this. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Boot
open Function Set Filter Finset MeasureTheory Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Geometry Prim Diagram Diagram.Formal PertExtension Series Series.Radial Series.Tested Chart Binding Ledger Gauge Booth
open Lattice RG Precision Comparison.RG02 Comparison.RG02.Bulk Comparison.RG02.Adjacent Comparison.RG02.FVAAlt2 Integral Wilson Exterior Arm Marker Multi
open FreeResolvent (flatten)
open PowerSeries
open scoped Topology BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius
variable {m:ℕ} {G:Gauge} {W I:Type} [DecidableEq W] (K:Census W)(u:W)
variable (Γ: History G)(C: Bulk.Chain Γ)(N p :ℕ)(B: Boot.Scout (G:=G) m)
local notation "f"=> Γ.S.side N p
local notation "D"=> Γ.rep N p N
local notation "E"=> fieldDir G (Γ.S.side N p) 1
-- generalized Bare.bareUp any cutoff α and all periods

def ink : Bulk.Colors K G (Γ.S.side N p):= { vac t U:= Wilson.energy U- mainTerm (D).clip (D).path U, power := fun _=>m, mark:= fun i _ z=> if i=(Arm.pub u:Multi.Hot K) then (↑(B.Vt _ z):ℂ) else 0 }
local notation "β"=> ink K u Γ N p B
include C
lemma kept0:∀ (U:Config G (Γ.S.side N p)), Precision.loop (D).path U=0:=by
 intro U; simp only [Precision.loop,RG.Patch.average,uncut,RG.Atom.unmasked, RG.Atom.poly, C.starts N p]; simp
lemma maskedV (i : ℕ)(hi:i≤5) : Assembly.GradeAt i (Bulk.projected (ink K u Γ N p B).vac):=by
    let P' : RG.Clip := (D).clip; let t: PathData G:=( D ).path
    have h:= C.peak N p 2 (by decide)
    have hm: Assembly.GradeAt 5 ( (Wilson.energy ∘ represent) - (mainTerm P' t ∘ represent («n»:= (Γ.S.side N p) )) ):=by
       refine ⟨ h.2.1.sub h.1, fun i hi=>?_ ⟩; rw [iteratedFDeriv_sub_apply ( (show ContDiffAt ℝ ω (Wilson.energy (G:=G) («n»:= (Γ.S.side N p) ) ∘ represent) 0 from h.2.1).of_le le_top ) ((show ContDiffAt ℝ ω (mainTerm P' t ∘ (represent (G:=G) («n»:=Γ.S.side N p))) 0 from h.1).of_le le_top), show iteratedFDeriv ℝ i (mainTerm P' t ∘ represent («n»:=Γ.S.side N p)) 0= iteratedFDeriv ℝ i (Wilson.energy (G:=G) («n»:=Γ.S.side N p )∘represent) 0 from (C.peak N p i (by omega)).2.2,sub_self] -- Wilson energy n binder?
    exact (hm.lower hi).coarse (g:=(Prod.snd:ℝ× (fieldDir G (Γ.S.side N p) 1)→_)) contDiffAt_snd rfl
lemma boundR : ∃ a b k, (D).path.Bounds (D).clip a b k:=by rw [C.selected N p N le_rfl,C.clips N p N le_rfl]; exact ⟨_,_,_,C.planned.cap N N le_rfl⟩
omit C
lemma tests (i:W) (x:ℕ) (U:Config G (Γ.S.side N p)): (ink K u Γ N p B).mark (Arm.pub i) (x:ℝ) U = if Arm.pub i=(Arm.pub u: Multi.Hot K) then (↑(B.Vt _ U):ℂ) else 0:=rfl -- arbitrary t
include C
lemma authentic : (ink K u Γ N p B).Standard:= by
   obtain ⟨a,b,k,hB⟩:= boundR Γ C N p
   refine ⟨ { suppose_vac:= maskedV K u Γ C N p B 3 (by decide), natural:= ?_, envelope:= ?_, suppose_mark:= ?_, gauges:= ?_, prices:=?_ }, maskedV K u Γ C N p B 5 le_rfl ⟩
   -- ordering records?
   case refine_2=> intro t k U; unfold ink; simp only [Wilson.energy_gauge,Work.F05.mainTerm_gauge hB U] -- by exact rfl?
   case refine_4=> intro t; exact Push.SectorMeasure.Env.compact (energy_cont.sub ((main_continuous_π hB).1))
   · intro i; by_cases h : i= (Arm.pub u: Multi.Hot K)
     · dsimp only [ink]; simp_rw [if_pos h]; exact B.prepared _ -- inside if comp tricky
     dsimp only [ink];simp_rw [if_neg h];exact Assembly.GradeAt.grade_zero m
   · intro i t; by_cases h:i= (Arm.pub u: Multi.Hot K)
     · exact (fun k U=> by unfold ink; dsimp only; simp_rw [if_pos h]; exact congr_arg _ (B.rooted _ k U))
     exact (fun k U=>by unfold ink; dsimp only;simp [h])
   intro i t; unfold ink; dsimp only; by_cases he : i= (Arm.pub u: Multi.Hot K) <;> simp only [ he, if_true, if_false ] <;> first | exact Envelope.compactC (Complex.continuous_ofReal.comp (B.payment _)) | exact Envelope.constC _ -- split binder under fun

variable (L: Lattice.Face ℤ → Orders (Foot G)) (hl:Prim.Plane Clocks.flat G L)
include hl
lemma payable (r:ℕ): Simmer (D).clip (D).path dormant (ink K u Γ N p B) (weights L (Γ.S.side N p)) r:=by
   refine ⟨(authentic K u Γ C N p B).1,symbol_p L Clocks.flat hl,symbol_k L Clocks.flat hl,fun e hh he v=>?_⟩
   rw [opening L Clocks.flat hl v e hh]; 
   congr 2; ext1 z
   unfold Gala.feeAct Ribbon.fees dormant ink Clocks.flat; dsimp only; simp_rw [kept0 Γ C]; simp
omit hl C
lemma singles (r:ℕ): Arm.Single dormant (ink K u Γ N p B) (Boot.view B (Γ.S.side N p)) u r m := by
   refine ⟨ Booth.known _ B.sight.symmetry,fun i=> Boot.cadre B i,fun e _ x=> ?_ ⟩
   let g(t:ℝ):= B.Vt (Γ.S.side N p) (sample t x); have ht : ContDiffAt ℝ ω g 0 := theoryM B x
   rw [vision B x]; unfold Comparison.RG02.Moving.Path.motion; rw [ show shineM _ (ink K u Γ N p B) u x= Complex.ofRealCLM ∘ g from ?_, show (β).power (pub u)=m from rfl, ← Assembly.jet_apply_left Complex.ofRealCLM g (i:= m+e) (ht.of_le le_top) ]; swap; · ext1 t; unfold shineM ink dormant; dsimp only; rw [one_pow, inv_one,one_smul,if_pos rfl];rfl
   rw [tale_jet, Nat.add_comm e]; exact congr_arg Complex.ofReal ( congr_fun (congr_fun ( Assembly.jet_eq g ) (m+e)) 1 )
end YM.RegulatorIR.FVAAlt2.Boot
