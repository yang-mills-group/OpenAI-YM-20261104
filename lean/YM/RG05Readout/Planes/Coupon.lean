import YM.RG05Readout.Planes.Cove
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Planes
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Cells Overlay
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons
open Records Basket Halls Shadow Flatten
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}
    {b k l:ℕ}{Q:ℝ}(h:C.Makes){D: Address.Rail C}{B:ℕ→ℕ→ℝ}
set_option quotPrecheck false
open Pulse Extraction Extraction.Lease
open Push.RelayDifference
variable {D:Address.Rail C}

variable {f: Extraction.Order}

/-! A transcription at common origin: affordable → vetted literal against calibrated matrices, absorb a finite bank then same at ALL higher SBP orders on-demand. For low-weight planes repaint them further. -/
open Bay Chalice

/-!
# Cone receipts.Boolean Ward.
 Weighted REAL ancestry maps. Projection kernel not discarded here. This proves linear inverse attenuation for surviving low-engineering weights and propagation bound for the rest, not lower/separated aperture budget by assumption. Using m≫ as required from Husk.C. -/
local notation "Z!"=> C.path.levels
local notation "χ"=> Address.clear C
local notation "S"=> Palette C d
local notation "J"=> Mark C d
local notation "ξ"=> C.S.block
local notation "L"=> C.S.block i
local notation "p!"=> BudgetPoint
variable {e:ℕ}{s t α A E:ℝ}
local notation "ΠΩ"=> Address.clear C d e
local notation "T"=> LinearMap.id (R:=ℂ) (M:=S) - Address.clear C d e
local notation "Ω"=> amplify d C L
/-!
# Actual limiting dictionary including transitions on same extraction. E units threshold within. Holds in kernel identified by all Poem tests.This is same linear mapping in ANY extraction.H.Phase fields ported by common T.F. -/
open Function Filter MeasureTheory Extraction Next.Extract
open Petals Dash
variable {b₀:ℕ→ℕ} (Y:∀ d:ℕ,Cutoffs→ Emblems C d)
variable {T₀ S₀:YM.Table C.book}{L0:ℕ→YM.Table C.book}{W:DiffPlan T₀}{R:Dash.Bin S₀}(H:Next.Extract.Base C f S₀ L0 R T₀ W) {g:Extraction.Order}
variable {G':∀ d:ℕ,ℕ→Palette C d→ₗ[ℂ] C.label d}(hp:Chalice.Anchored D B h b₀ Y)(ht:Tune (dims:=b₀) H Y g G')
variable {q:Extraction.Order} {θ:∀ d:ℕ,Emblems C d}(hΘ:Tempo Y b₀ q θ)(hF:q.fuse ≤ (f.refine g).fuse)
/-! Pass plane camouflage to the actual continuum table T per extraction, even using a different DiffPlan (Final). Exact containment of the discounted incoming covers on each e-plane at this test convention.Requires ancestors bought from same C. -/
variable {Z₁:DiffPlan T₀}(he:e<d)(hM:b₀ d ≤ m)(T':Tint B C d m)
local notation "K₀"=> Cutoffs
-- nada
local notation "Z"=> G' d m
local notation "Tn"=> bounty B d
local notation "U!"=>C.S.a
variable {φ:Filter Cutoffs}[φ.NeBot] (hv:φ≤ q.fuse)(x:Cutoffs→Palette C d) {v:Palette C d}
variable {W' r'}(L':OPE.Package C W' r' D) (hA:Storage C D)(hG:G.Simple)(hBin:∀ d,UVExt.Slots.StrongBin C R f d)(hs:Z₁.Inclusions T₀)
local notation "o!"=> fun i:K₀=> ((↑(C.S.a i.1):ℂ)^(d-e))⁻¹

/-!
# Sizing the discounted rows at fixed admissions T/meshing.
 Witnesses chosen per horizon/map.First grow from actual reference tickets using measured tree. Costs not packed with a powers s_m loss after final relative profile projection.Need both this subpower and normalized Replica.NEVER rebase pivots symbolically for these bounds. -/
-- if ξ measurement at level i uniform. descend to m. choose v low.P.trace
local notation "η"=> C.S.a
local notation "π"=> bounty B d
local notation "fμ"=> powerFare B d
local notation "Q"=> finer (θ d)
def quotaP (C: Family G)(B:ℕ→ℕ→ℝ)(d e m i:ℕ):ℝ:= bounty B d i * (C.S.a m / C.S.a i)^e*(1+grow (powerFare B d i))
local notation "Δ"=> quotaP C B d (d-(e+1)) m i
include ht hp h hM T' he
omit ht in
lemma auditions (p n:ℕ)(hi:m ≤ i)(hk:i ≤ n)(x:S):
    let r:= finer (Y d (n,p)) hi
    ∃ a:Palette C d, let w:= (finer (Y d (n,p)) (hi.trans hk)) a; ΠΩ w=w ∧ size (r.symm x-a)≤ quotaP C B d (d-(e+1)) m i * size x:=by
     intro r; obtain ⟨V,hV⟩:= hp.paid (n,p) d (hM.trans (hi.trans hk));
     let X':= finer (Y d (n,p)) hk x; let v:= (finer (Y d (n,p)) (hi.trans hk));
     obtain ⟨a,hA,hp',hX⟩:= just_sized h (hp.age d) hV T' hM hi hk he X'; obtain ⟨b,hb,hY,hL⟩:= quotient_move h (hp.age d) hV T' hM le_rfl hi hk (X'-a) he hp'; let δ:= size x
     let W:= (finer (Y d (n,p)) hk).symm; have hf: W X'=x:=LinearEquiv.symm_apply_apply ..
     have hg:v.symm X'=r.symm x:=by unfold v; rw [Many.sumwalk _ hi hk]; change r.symm (W X') = r.symm x; rw [hf]
     refine ⟨v.symm (a+b),?_,?_⟩; · rw [show _= a+b from v.apply_symm_apply _,map_add,hA,hb]
     change size _ ≤ Δ*δ; rw [← hg,←map_sub,←sub_sub]
     have ht': size (W (X'-a)) ≤ (1+grow (powerFare B d i))*δ:= (hX.trans_eq (by change _ = _ * size x; rw [← hf])) -- orientation
     have hr: 0 ≤ π i * (η m/η i)^(d-(e+1)):= mul_nonneg (zero_le_one.trans (bounty_head _)) (pow_nonneg (div_nonneg (C.S.a_pos _).le (C.S.a_pos _).le) _)
     exact (show size (v.symm (X'-a-b))≤ _ from (le_mul_of_one_le_left (size_ge _) (bounty_head (B:=B) (d:=d) m))).trans (hL.trans ((mul_le_mul_of_nonneg_left ht' hr).trans_eq (by unfold quotaP; ring)))
omit ht he T' in
lemma whole (p n:ℕ)(hi:m≤ i)(hk:i ≤ n)(x:S): size ((finer (Y d (n,p)) hi).symm x) ≤ quotaP C B d d m i *size x :=by
    -- apply backsteps, product paid instead height.Shadow
    have h': (π m)*size ((finer (Y d (n,p)) hi).symm x) ≤ π i * ((η m)/(η i))^d*size x:=by
       induction i,hi using Nat.le_induction generalizing x with
       | base => rw [base_value,LinearEquiv.refl_symm,LinearEquiv.refl_apply,div_self (C.S.a_pos _).ne',one_pow,mul_one]
       | succ k₁ hk₁ ih=>
         obtain ⟨v,hV⟩:=hp.paid (n,p) d ((hM.trans hk₁).trans (k₁.le_succ.trans hk)); let z:= Y d (n,p) k₁; let t:ℝ:= (C.S.block k₁).val; have hT: 0<t:=by unfold t; positivity
         let s:= (η m)/(η k₁);
         rw [finer_next hk₁]; apply le_trans (ih (k₁.le_succ.trans hk) (z x)); have ht:= Costume.earned (e:=0) h hV (hp.age _) (hM.trans hk₁) hk|>.body x
         have hg : size (z x)≤ productCost B d k₁*(t^d*size x):=by
             have hv'' := ht.trans (mul_le_mul_of_nonneg_left (size_tuned ..) (zero_le_one.trans (grows _).1)); exact hv''.trans (mul_le_mul_of_nonneg_right (le_trans (by have h:=grows (d:=d) (B:=B) k₁|>.1; linarith only [h]) (grows k₁|>.2.2.1)) (mul_nonneg (pow_nonneg hT.le _) (size_ge _)))
         apply (mul_le_mul_of_nonneg_left hg (mul_nonneg (zero_le_one.trans (bounty_head _)) (pow_nonneg (div_nonneg (C.S.a_pos _).le (C.S.a_pos _).le) _))).trans_eq
         rw [bounty_up,show η m/η (k₁+1)= (η m/η k₁)*t from ?_, mul_pow]; -- α notation fix
         swap; · rw [C.S.a_step]; unfold t;field_simp
         ring
    let a:= π i * ((η m)/(η i))^d; have ha:0 ≤ a:= mul_nonneg (zero_le_one.trans (bounty_head _)) (pow_nonneg (div_nonneg (C.S.a_pos _).le (C.S.a_pos _).le) _)
    exact (le_mul_of_one_le_left (size_ge _) (bounty_head (B:=B) (d:=d) m)).trans (h'.trans (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right ha (le_add_of_nonneg_right (zero_le_one.trans (grows _).2.1))) (size_ge x)))
include H hΘ hF
-- extraction has Θ; use also only subfilter. get uniform constants on discount despite not passing lower k reading for ANY kernel cutoff limit.
variable (u:Palette C d)(hi:m ≤ i)
omit H hΘ ht hF
include hM hi hΘ ht H hF L' hA hG hBin he hs T'
lemma epilogue : ∃ w:S,T₀.project d (G' d m w) ∈ LinearMap.range (Z₁.rise he.le) ∧ ‖(Q hi).symm u -w‖ ≤ Δ*size u:=by
   let x: Cutoffs→ Palette C d:= fun j=>(finer (Y d j) hi).symm u; let α₀:=size u
   have Hx: Tendsto x q.fuse (𝓝 ((Q hi).symm u)):= Dash.arcing ((Tempo.across Y hΘ hM hi).snd_nhds) tendsto_const_nhds
   let t:=quotaP C B d d m i * size u; let D':=Δ*size u
   choose a ha using fun j:Cutoffs=> show ∃ a:Palette C d,i ≤ j.1 → Address.clear C d e (Many.point (Y d j) a m j.1) =Many.point (Y d j) a m j.1 ∧ size (x j-a) ≤ D' from (by
      by_cases h':i ≤ j.1
      · obtain ⟨a,hx,hK⟩:= auditions h Y hp he hM T' j.2 j.1 hi h' u; refine ⟨a,fun hl=>?_⟩; rw [Many.weave_fine (hi.trans h')]; exact ⟨hx,hK⟩
      exact ⟨0,fun hx=>False.elim (h' hx)⟩)
   have hS: ∀ᶠ j in f.fuse, Address.clear C d e (fastU (Y d) a m j)=fastU (Y d) a m j:= ((cutoff_grows f).eventually_ge_atTop i).mono fun j hh=> (ha j hh).1
   let C':= t+D'; have hB:∀ᶠ j in f.fuse,size (a j)≤ C':= ((cutoff_grows f).eventually_ge_atTop i).mono fun j hh=> by
       rw [show a j=x j+(a j-x j) by abel]; exact (size_add ..).trans (add_le_add (whole h Y hp hM j.2 j.1 hi hh u) (le_trans (size_turn ..|>.le) ((ha j hh).2)))
   have hg:q.fuse ≤ f.fuse:= hF.trans (Tails.refine f g).fused
   obtain ⟨l,hl,hlen,V,hV⟩:= Next.UVStress.finite_extract a C' ((hB.mono (fun j hi=> le_trans (size_norm _) hi)).filter_mono hg);
   refine ⟨V, graded_in h Y H hp ht hF he hM T' hl a L' hA hG hBin hs ⟨_,hB⟩ hS hV,?_⟩; refine le_of_tendsto (((Hx.mono_left hl).sub hV).norm) (((cutoff_grows q).mono_left hl|>.eventually_ge_atTop i).mono (fun k hk=> (size_norm _).trans ((ha k hk).2)))
omit ht H hF L' hA hG hBin hs T' he in
lemma origin0 : ‖(Q hi).symm u‖≤ quotaP C B d d m i*size u:=by
    let x:Cutoffs→Palette C d:=fun j => (feeling Y d m i hi j).snd u; have hx:Tendsto x q.fuse (𝓝 ((Q hi).symm u)):= Dash.arcing ((Tempo.across Y hΘ hM hi).snd_nhds) tendsto_const_nhds
    apply le_of_tendsto hx.norm; exact ((cutoff_grows q).eventually_ge_atTop i).mono fun j hj=> (size_norm _).trans (whole h Y hp hM j.2 j.1 hi hj u)
end YM.RG05Readout.Planes
