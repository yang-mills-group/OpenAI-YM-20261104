import YM.RG05Readout.Bay.Depot
import YM.RG05Readout.Harvest.FrameReport
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Bay
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Cells Overlay
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons
open Records Basket Halls Shadow Flatten
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}
    {j b k l:ℕ}{e Q:ℝ}(h:C.Makes){D: Address.Rail C}{B:ℕ→ℕ→ℝ}
set_option quotPrecheck false
local notation "t!"=> (1,false)
local notation "L"=> C.path.levels
local notation "χ"=> C.path.levels.clock.J
local notation "λ₀"=> C.S.toDepth
local notation "Α"=> C.S.a
local notation "Z"=> C.path.levels.budget
local notation "R0"=> C.path.rep N p
variable {V:Address.Sight C d p}{U:Address.Emblems C d}(hw:Awake D B b d)(ht:Spine D B h b p d N V U)
open Pulse Nuclear
local notation "ν"=> Many.envelope C (b+1) (d+1) k Q b
variable {w:Worth}{r:ℕ→ℕ}(Yc:OPE.Package C w r D)(Ys:Storage C D)
noncomputable def season (C:Family G)(b d j k:ℕ)(Q:ℝ)(B:ℕ→ℕ→ℝ):ℝ:=
     let t:=Many.envelope C (b+1) (d+1) k Q b; Real.exp ((C.S.a j/C.S.a b)^4*Vac.treasury C.path.levels b+ t*sequin C b d B Q+t*sequin C b d B Q+2*1)/t
local notation "w!"=> season C b d j k Q B
local notation "u"=> sequin C b d B Q
include h ht hw Yc Ys
variable (hp : b < N)(hA : j ≤ b) (M:Palette C d)(hM:size M≤ Q)(hQ:0<Q)(hX:Warm C b (d+1) k)
    (hy:1 ≤ C.path.levels.clock.J b)(hh:Stock.Tabs.opens C.path.levels (bumper 0) j b)
local notation "T!"=> Cells.center C.S p (hA.trans hp.le) 0
local notation "X"=> Many.point U M (b+1) N
include hp hA M hM hQ hX hy hh
lemma stamped (z: Site (C.side b p))(hf:separation z 0 ≤ (C.S.toDepth hA p).count.val/4)(f:Body)(hc:Cap (d+2) f 1) : (T!).rootTest (C.beta N p) (clinic C p N d X b z t! f) ≤ season C b d j k Q B:=by
    let P':=T!; let Z':= housed j hA z; let L₀:=hands C p j
    let I:=Site (C.side j p); let a:=Mine.remap Z' L₀; let C₀:=(Mine.ward Z' L₀ (Stock.census I)); let v:= ManyStem C Z' b; let s:(C₀ b).Mode:=⟨Finset.univ,Finset.mem_filter.mpr ⟨Finset.mem_univ _,Finset.mem_univ _,a.injective.injOn⟩⟩ 
    obtain ⟨ht',hq⟩:= inSequence h hw ht Yc Ys Z' L₀ f hc M hp hM hQ hX (house_gap j hA z _ (opened_lot j hA _ hh) hf) hy s
    let f':= headings Z' L₀ (fun _=>f); let W:= swell (le_refl N) (Mine.tree Z' L₀) (fun _ => d) (fun _=>precinct C p N d X) f'
    have he (i:I): P'.copy i (clinic C p N d X b z t! f)= W b (a.symm i):=by
       let t:= (λ₀ hp.le p); let Q':= clinic C p N d X b z t! f; have ht:P'.copy i Q'= stepUp (L₀ i) ((λ₀ (hA.trans hp.le) p).embed i) Q':=by rw [← elev C j p N (hA.trans hp.le) i]; exact (handmove C N p j (hA.trans hp.le) Q' i).symm -- find sort
       change P'.copy i Q'= _; rw [ht]; unfold W swell uniform; dsimp only [Q',clinic, uniform]; rw [dif_pos hp.le,dif_pos hp.le, show f' b=fun _=>f from (Many.headlines Z' L₀ (fun _=>f) (N:=N)).1,embed_comp (λ₀ hA p) t]; exact stair_rot ..
    let Z₁:=fun V₁=>∏ i:I, P'.copy i (clinic C p N d X b z t! f) V₁; have hv:C.omega N p (fun V₁=>∏ i:v, W b i V₁)= moment (C.beta N p) Z₁:=by
        unfold Family.omega; congr 1; funext V₁; unfold Z₁; rw [← Equiv.prod_comp a.symm]; exact Finset.prod_congr rfl (fun i _=> congr_fun (he i).symm _)
    change ‖C.omega N p (fun V₁=>∏ i:v, W b i V₁)‖*_ ≤ _ at hq; rw [hv,show s.val.card=Fintype.card (ManyStem C Z' b) from Finset.card_univ,Fintype.card_congr a,Stock.tallies C.S j b p] at hq
    refine Stock.spacer ‖moment (C.beta N p) Z₁‖ _ _ (Fintype.card (Site (C.side j p))) (norm_nonneg _) ht' Fintype.card_pos (hq.trans ?_)
    refine le_of_eq (congr_arg _ ?_); ring
lemma shallot (e:ℕ)(hl:b=e+1) (hx:16*(1+0+Scope C d) ≤ (C.S.toDepth hA p).count.val)
   (hr:C.S.a j/8+C.S.a b ≤ C.S.a j/4) (hR:C.S.a j/8+C.S.a b*3< C.S.radius p) (q:Body)
   (hP:∀ x∈tsupport q.val, ‖x‖≤C.S.a j/8)(he: Tall (E:=E4) q (d+2) 1 1):
    Interior ((T!).chamber 0) (fieldC C m N p d X q)∧ (T!).rootTest (C.beta N p) (fieldC C m N p d X q)≤ (Α m/Α b)^d*((Α b)^4*(Α j/Α b)^4*w!) :=by
    let F:= precinct C p N d X
    have hW:0 < ν:= mul_pos (rust_paid _).1 (grantw (totalpos hQ _)); have hp1:0 ≤ w!:= div_nonneg (Real.exp_pos _).le hW.le
    have h_W: 16 * (1+0+Scope C d) ≤ (C.S.toDepth hA p).count.val:=hx
    have hYz:=valueSum hA (le_refl N) F (precinct_null X) q hP hr hp.le ‹C.Makes› hp1 (fun i hi => ?_)
    swap
    · let f:=restricted C b p i q; have hh':= (Finset.mem_filter.mp hi).2
      have hB:Interior ((T!).chamber 0) (clinic C p N d X b i t! f):=by
         subst b; refine clusterInside (G:=G) (d:=d) ‹C.Makes› hA (le_refl (e+1)) hp.le i hh' h_W i ?_ i (by simp) le_rfl _ _; exact Mine.equal_site ..
      refine ⟨hB, stamped h hw ht Yc Ys hp hA M hM hQ hX hy hh _ hh' f (fun j' hj y _=>?_)⟩
      unfold f restricted; rw [Native.pulled,norm_smul,Real.norm_of_nonneg (pow_nonneg (C.S.a_pos _).le _)]
      exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (C.S.a_pos _).le (by have h₀:= C.S.strictAnti.antitone (Nat.zero_le b); simpa only [Schedule.a_zero] using h₀))).trans ((he j' hj _).trans_eq (by simp))
    obtain ⟨hZ,hY⟩:= hYz
    have hz: (Α b:ℂ)^4 • gathered C N N p d le_rfl F b q=fieldC C b N p d X q:=by
       have h:= Harvest.return_weight X hp.le q (le_refl N) hP hR; rw [crops_head] at h; exact h
    let v:ℂ:= (Α m:ℝ)/(Α b:ℝ); have hv:v=↑((Α m)/(Α b)):=by unfold v; push_cast; rfl
    rw [show fieldC C m N p d X q=v^d • fieldC C b N p d X q from ?_,←hz, Next.Extract.root_smul,Next.Extract.root_smul]; refine ⟨(hZ.scale _).scale _,?_⟩
    · have hp:0 < (Α m)/(Α b):= div_pos (C.S.a_pos _) (C.S.a_pos _); rw [norm_pow,hv,Complex.norm_real, Real.norm_of_nonneg hp.le,norm_pow,Complex.norm_real,Real.norm_of_nonneg (C.S.a_pos _).le]
      exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hY (pow_nonneg (C.S.a_pos _).le 4)) (pow_nonneg hp.le _)).trans_eq (by ring)
    unfold fieldC; rw [smul_smul]; congr 1; unfold Pulse.gate v; have he:(Α b:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (C.S.a_pos _).ne'; simp_rw [div_pow]; field_simp
end YM.RG05Readout.Bay
