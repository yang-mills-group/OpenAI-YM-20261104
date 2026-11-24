import YM.Pert.Rigid.Spin
import YM.SignedWilsonExpansion.Dancer.Coats
import YM.SignedWilsonExpansion.Homes.MeterQ
import YM.SignedWilsonExpansion.Purchase.Shoot
/-!
# Thermal seats from ACTUAL shared hierarchy cutoff Books and trials
Includes sign, H-real compatibility (partial finite-accuracy from grant),
cap units including every proper face, relative scale colleagues, election symbols.
-/
set_option autoImplicit false
set_option maxHeartbeats 520000
set_option maxRecDepth 3072
noncomputable section
namespace YM.SignedWilsonExpansion.Dancer
open XSpace XSpace.Structure1 Normalize Future Gauge Filter Function Matrix
open WilsonCoeffUV.Bank WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Xa MarqueQ Stair
open Purchases Asymptotics Shell Lights Fort Coats Commission Maxwell Maxwell.Free Maxwell.Wick
open Precision Wilson Source WardBin Labels FVA2 FVA2.Dframe Homes
open Extraction Order Climb Spec Table Next.UVStress OPE.Levy Trace.Pilot PhysMS
open MergeProof.East Next.Rank Ward Next.Rank.East PhysicalNext.Repeat.Legato Lattice FullVolume Cells
open Extra.Histories Pert
open scoped BigOperators Topology Classical
variable {G:Gauge}{C:Family G}{b d h t w n k u j N p:ℕ}{ι:Type}{L:Filter ι}{ρ r:ℝ}
namespace Stitch
variable (C)
abbrev pre (x:Sec G d) : (Bel C.book).Field d:= (Free.fields C.labels d).symm x
variable (F : Labels.Frames G)
local notation "ℎ₀"=> (C.labels.level d)
abbrev rep (x:Sec G d) := Further.CorrectedLift.ladder C d (pre C x)
lemma rep_eq (x:Sec G d) : bulb G d ((C.labels.level d).coords.symm (rep C x))=x:=by
    let q:= pre C x; have h:q= (Bel C.book).project d (rep C x):= ( Further.CorrectedLift.ladder_reads q ).symm; nth_rw 2 [← (Free.fields C.labels d).apply_symm_apply x]; change _= fields _ _ q; rw [h,fields_eval]; rfl
lemma staffed (x:Sec G d): pre C x= Pert.RawLabels.enroll C.labels d ( On.sectionMap d x ):=by
    apply (Free.fields C.labels d).injective; change _=bulb G d ((ℎ₀).coords.symm ((ℎ₀).coords (On.sectionMap d x))); rw [pre,LinearEquiv.apply_symm_apply,LinearEquiv.symm_apply_apply,bulb_recovers]
lemma pulse_logo (x:Toon G d)(t:ℝ): Pert.Scale.gear C.labels d t (pre C (Logo G d x))= ((t:ℂ)^x.size) • pre C (Logo G d x):=by
     rw [staffed, Pert.Scale.gear_inherit, Pert.Scale.grow_weights ( w:=x.size ) (t:=t),map_smul]; intro i hi; exact congr_arg Prod.fst ((Labels.weight_slot _).symm.trans (((Labels.pure_grade ..).mp (Fort.grade x)) hi))
lemma reelLogo (H:(Bel C.book).RealSpin)(x:Sec G d): pre C (reel d x)= (Bel C.book).conj H d (pre C x):=by
     let p:=pre C x; let F:=C.labels; apply (address_inj F d); have he: Free.address F d p=x.val:=by rw [address_eval]; exact congr_arg Subtype.val ( (Free.fields ..).apply_symm_apply x )
     rw [ Free.address_star , he, Free.address_eval ]; unfold F; rw [pre,LinearEquiv.apply_symm_apply]; rfl -- implicit?
lemma orientLogo (H:(Bel C.book).RealSpin)(x: Sec G d)(s:Signed): pre C (ori s.ortho d x)= (Bel C.book).mirror H d s (pre C x):=by
     let p:=pre C x; let F:=C.labels; apply (address_inj F d); have he: Free.address F d p=x.val:=by rw [address_eval]; exact congr_arg Subtype.val ( ( Free.fields .. ).apply_symm_apply _ ); -- binder
     rw [Free.address_motion,he,Free.address_eval]; unfold F; rw [pre,LinearEquiv.apply_symm_apply]; rfl
lemma leafLogo : pre C (Normalize.leaf G d)= (Bel C.book).unit d :=by
    apply address_inj C.labels d; rw [unit_address,address_eval]; exact congr_arg Subtype.val ((fields ..).apply_symm_apply _)
-- gear commutes for any F prop, use basis test. Grow_weights and uniqueness section.Tactics
lemma reelWheel (H:(Bel C.book).RealSpin)(x:Sec G d)(r:ℝ):
     Pert.Scale.gear C.labels d r (pre C (reel d x))=(Bel C.book).conj H d (Pert.Scale.gear C.labels d r (pre C x)):= by rw [reelLogo C H x]; exact ( Pert.Scale.gear_conj C.labels (pre C x) r ).symm
lemma spinWheel (H:(Bel C.book).RealSpin)(x:Sec G d)(r:ℝ)(s:Signed) :
     Pert.Scale.gear C.labels d r (pre C (ori s.ortho d x))=(Bel C.book).mirror H d s (Pert.Scale.gear C.labels d r (pre C x)):=by
     rw [orientLogo C H x s]; simp_rw [show ∀ x:(Bel C.book).Field d,(Bel C.book).mirror H d s x=Extra.FD.rideO C.labels s.ortho d x from Pert.Rigid.wear_ride C.labels s ]; exact ( Pert.Scale.gear_spin C.labels (pre C x) s.ortho r ).symm -- ride vs gear_mirror
open Further.CorrectedLift Push Price
-- needed preserve symbol support under ladder retain. powers 2 distinct via strict monotone.
lemma desired (x: Toon G d)(i:(C.labels.level d).Index)(v: rep C (Logo G d x) i≠0) : (C.labels.level d).grades i=(x.size,x.grade):=by
    let a₀:= On.sectionMap d (Logo G d x); let F':= ℎ₀; let y:= Logo G d x; let S:= Push.CutoffProjectors.retain F' ((Bel C.book).null d); let z:= F'.coords a₀; let B:= S z; have hz : rep C y=B:=by unfold rep; rw [staffed]; rfl
    let e₁:= (free_scaled (d:=d) C 2 z); let e₂:=free_zoom C 2 z; have hF: F'.scaled 2 B= ( (↑((2:ℝ)^x.grade)) :ℂ) • B := by rw [ ← show S (F'.scaled 2 z) = F'.scaled 2 B from e₁,show (F'.scaled 2 z)=( ( ↑( (2:ℝ)^x.grade ) ) :ℂ) • z from F'.scaled_pure (m:=(x.size,x.grade)) _ (Fort.grade x) ,map_smul]
    have hw: Further.CorrectedLift.zoom F' 2 B= ( (↑ ((2:ℝ)^x.size)) :ℂ ) • B:= by rw [← show S (Further.CorrectedLift.zoom F' 2 z) = Further.CorrectedLift.zoom F' 2 B from e₂, show Further.CorrectedLift.zoom F' 2 z= ( (↑ ((2:ℝ)^x.size)) :ℂ ) • z from zoom_pure _ _ _ (Fort.grade x),map_smul]
    have h0:B i≠0:= hz ▸ v
    have hx(u v:ℕ)(h: (( (↑((2:ℝ)^u)):ℂ)* B i= ((↑((2:ℝ)^v)):ℂ) * B i)): u=v :=by exact (pow_right_strictMono₀ (a:=(2:ℝ)) one_lt_two).injective ( Complex.ofReal_injective ( mul_right_cancel₀ h0 h ))
    exact Prod.ext (hx _ _ (congr_fun hw i)) (hx _ _ (congr_fun hF i))
variable {C}(q:BeamT C){f:Extraction.Order}{H:(Bel C.book).Hierarchy}
-- observation: base and gears capture from wheel
abbrev streak (x:Sec G d)(N p:ℕ) := q.microphone (N,p) d (pre C x)
abbrev worn (x:Sec G d)(N p:ℕ)(r:ℝ) := q.microphone (N,p) d (Pert.Scale.gear C.labels d r (pre C x))
variable (v:q.Given f H ρ)(K:d≤ q.k)(h':q.V.k<N)
local notation "µ"=> Next.Rank.Station.mag C.path.levels q.V.b q.V.k
abbrev pub (q:BeamT C) {d:ℕ} (p:d≤q.k) (N u:ℕ):= q.V.R N u ⟨d,Nat.lt_succ_of_le p⟩
lemma sparK (h:d≤ q.k)(x: (Bel C.book).Field d): q.microphone (N,p) d x= ladd C µ q.V.k N p d (pub q h N p) (Further.CorrectedLift.ladder C d x) := by unfold BeamT.microphone; rw[dif_pos h]; rfl
variable (P : C.Makes)
include v h' K P
lemma pulse_task (x: Toon G d) : Attention C d q.V.k N p x.size x.grade ρ (streak q (Logo G d x) N p) (rep C (Logo G d x)) := by
    let z:= rep C (Logo G d x); let L:= pub q K N p; let a:Sec G d:= Logo G d x; let y:= streak q a N p -- wrong name
    let T:=v.1.rate N p h'; let i:Fin (q.k+1):=⟨d,Nat.lt_succ_of_le K⟩; have hh:L= _:= (show L=q.V.R N p i from rfl); have hz:= v.2; let F:= C.path.levels; refine ⟨desired C x, L,(T.1 i).1, ?_, T.2 i _ ⟩
    rw [streak,sparK q K]; have he: µ=ρ/C.S.a q.V.k:=by
       rw [← hz]; change _= (_ * _ ) / _; rw [mul_comm]; exact (((mul_div_cancel_right₀ µ ( (C.S.a_pos q.V.k).ne'))).symm)
    rw [← he]; exact poured P (v.1.early i) h'.le _ L (T.1 i).1 _
lemma pulse_unit : worn (d:=d) q (Normalize.leaf G d) N p r = C.refUnit d := by
     rw [worn, leafLogo (G:=G), Pert.Scale.gear_unit,sparK q K,ladder_unit]; let i: Fin (q.k+1):= ⟨d,Nat.lt_succ_of_le K⟩; exact pure_start P (v.1.early i) h'.le _ _ ((v.1.rate N p h').1 i).1
lemma pulse_startSpin (x:Sec G d)(s:Signed): worn q (ori s.ortho d x) N p r=(C.labels.level d).act s.ortho (worn q x N p r):=by
     unfold worn; rw [sparK q K,spinWheel C H.spin x r s, sparK q K,Further.CorrectedLift.ladder_spin H.spin s ]; let i :Fin (q.k+1):=⟨d,Nat.lt_succ_of_le K⟩; exact rider P (v.1.early i) h'.le _ _ ((v.1.rate N p h').1 i).1 ((v.1.rate N p h').1 i).2 s _
lemma pulse_startReel (x:Sec G d): worn q (reel d x) N p r= star ( worn q x N p r ) :=by
    unfold worn; rw [sparK q K,reelWheel C H.spin x r,sparK q K, Further.CorrectedLift.ladder_conj H.spin ]; let i :Fin (q.k+1):=⟨d,Nat.lt_succ_of_le K⟩; exact purer P (v.1.early i) h'.le _ _ ((v.1.rate N p h').1 i).1 _
omit v h' K P
lemma wears (x:Toon G d) : worn (d:=d) q ( Logo G d x) N p r= ( r:ℂ )^ x.size • streak q ( Logo G d x ) N p:=by rw [worn,pulse_logo,map_smul]
-- multiplier signs: rank status cost checks AFTER gear.Normalization ξ.About ratios with any θ.
end Stitch
end YM.SignedWilsonExpansion.Dancer
