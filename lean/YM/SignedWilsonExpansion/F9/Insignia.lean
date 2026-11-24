import YM.SignedWilsonExpansion.F9.Mover
/-!
# Coherence calls made from Ward ensemble. Commission L and Bare publication
- /
-/
set_option autoImplicit false
set_option maxHeartbeats 410000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Wilson Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG Laurent Bloch Metric
open Blue FreeResolvent Work.F08 Bank Soil Exterior Next.Free Tree Precision Power Embroider
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb
open Realm Fountain PathCost Embroider.Canvas Shard PowerSeries XSpace
open Supply Ticket Polestar Next.Foundations Patrol Shard.Plan
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{A:Levels G}{Ñ:ChartRatio G}{J:Type*}{e k h m c v b T N M i j l r d p u n :ℕ}
variable {B Q D Z X Y η t a ρ:ℝ}{E W U V:Credit}{P:Era G ℝ}{R:Realm G (e+1) E}
local notation "κ'"=> ((n+1)*k)
variable {F:Frames G}{H:Hol G}{A':∀ h, Survey G H h}{K:∀ h,Rays G h H}
local notation "Rι"=> (F.level h)
namespace Stair
open Cirrus
open Normalize (Sec Formal)
open Tape
variable (W:Initialize G){A'' :∀ h,Rays G h W.hol}{Ω:Council F}{P':Normalize.Store G}
variable (q': Stair Ω (launch F W.hol W.surveys A'' k) A Ñ m c c h e k u Z)
section motions
variable (t':Mesh)(ρ:ℝ)
lemma vista_zero (F:Frames G)(h:ℕ): vista F (h:=h) 0= Normalize.leaf G h:=by rw [carried F,(F.level h).starts_unit]; exact Subtype.ext (map_one Maxwell.reduceEq)
lemma Mora_unit : q'.Mora (Nat.zero_le h) 0 0=1:=by
    let V:= F.level 0; let x:= Nat.zero_le h; unfold Stair.Mora raft; rw [loft_zero F (q'.supply 0 x) (q'.charm 0 x) (launch_unit W.hol A'' W.surveys (Nat.zero_le k) F)]; unfold stamps; rw [Finset.sum_eq_single 0]; · simp [pureF]
    · intro i _ h; rw [pureF,Pi.single_eq_of_ne (fun q=>h (congr_arg Prod.snd q)),zero_smul]
    simp
lemma bare_unit : q'.bareTape W t' ρ (0:(F.level h).Index)= Tape.side (Normalize.leaf G h) 1:=by
    rw [← ascendsUnit F (Nat.zero_le h), own_print W q' t' ρ (Nat.zero_le h) _ (wt_zeroH _),printTape]; rw [Finset.sum_eq_single 0]
    · unfold flagTape; rw [wt_zeroH,pow_zero,pow_zero,inv_one,mul_one,one_smul,q'.Mora_unit W,map_one,vista_zero]; rfl
    · intro j _ h; exact (h (wt_of_r F j (Nat.eq_zero_of_le_zero ((F.level 0).bound j)))).elim
    simp
lemma line_unit (P':Normalize.Store G)(v:ℕ): q'.lineTape W P' t' v ρ 0=Tape.side (Normalize.leaf G h) 1:=by
    rw [lineTape,bare_unit,leafFormal _ (guardH W t' _), Tape.side_tempo (flight_zero _),← flight_sub,map_one]
def publish (Q:Normalize.Store G)(l:ℕ)(r:ℕ): Label G h→ₗ[ℂ] Sec G h:= (F.level h).basis.constr ℂ (fun i=> q'.lineTape W Q t' l ρ i r)
def originalT (r:ℕ): Label G h→ₗ[ℂ] Sec G h:= (F.level h).basis.constr ℂ (fun i=> q'.bareTape W t' ρ i r)
lemma published (Q:Normalize.Store G)(l r:ℕ)(i:(F.level h).Index): publish W q' t' ρ Q l r ((F.level h).basis i)= lineTape W q' Q t' l ρ i r:=by rw [publish, Module.Basis.constr_basis]
lemma published0 (r:ℕ)(i:(F.level h).Index): originalT W q' t' ρ r ((F.level h).basis i)= q'.bareTape W t' ρ i r:=by rw [originalT,Module.Basis.constr_basis]
lemma first_pass (Q:Normalize.Store G)(l:ℕ): publish W q' t' ρ Q l 0= (coeff 0 (inverseH W Q t' h)) ∘ₗ originalT W q' t' ρ 0:=by
    apply (F.level h).basis.ext; intro i; rw [LinearMap.comp_apply,published0,published,lineTape, tempo_first (flight_zero _), Tape.respond]; simp only [LinearMap.coe_mk, AddHom.coe_mk,facet]; rw [show Finset.antidiagonal (0:ℕ)={(0,0)} from (by simp),Finset.sum_singleton]
lemma authorize (e':ℕ):Trustee (originalT W q' t' ρ e') (if e'=0 then 1 else 0):=by
    refine galleryH F (?_) (fun i=>by rw [published0]; exact tape_permit ..) (fun i=>by rw [published0]; exact q'.bare_real W t' ρ i e') fun s i=>?_
    · rw [← (F.level h).starts_unit,published0,bare_unit, side_read,coeff_one]
    simp_rw [published0]; have h:=congr_fun (bare_spin W q' t' ρ i s) e'; rw [Finset.sum_apply] at h; exact h
lemma custody (e':ℕ)(Q:Normalize.Store G)(l:ℕ): Trustee (publish W q' t' ρ Q l e') (if e'=0 then 1 else 0):=by
   let S:= starFlight (relativeF A Ñ c l (c-l)); let P:=inverseH W Q t' h; have hx:Formal P:= guardH W _ _
   refine galleryH F (?_) (fun i=> by rw [published]; exact frame_height P hx _ (q'.tape_permit W t' ρ i) ((F.level h).bound i) S e') (fun i=> by rw [published]; exact tempoF_real _ (frame_real P hx (q'.bareTape W t' ρ i) (q'.bare_real W t' ρ i)) _ (realZx _) e') (fun s i=>?_)
   · rw [← (F.level h).starts_unit,published, line_unit,side_read,coeff_one]
   simp_rw [published]; have ht: Tape.layer (Normalize.ori s.ortho h) (q'.lineTape W Q t' l ρ i)=∑ j:(F.level h).Index,(↑(realM Rι s j i):ℂ) • q'.lineTape W Q t' l ρ j:=by unfold lineTape; rw [tempo_spin s P hx,bare_spin]; simp_rw [map_sum,map_smul]; rfl
   have hz:=congr_fun ht e'; rw [Finset.sum_apply] at hz; exact hz
end motions
end Stair
end YM.WilsonCoeffUV.Mer.Xa
