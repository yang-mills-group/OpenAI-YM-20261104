import YM.RG12.Kintsugi.Sector
import YM.RG12.Kintsugi.Inlet
/-!
# Angular-family outlet on authentic stations

Don't assume stress-account invertibility! Use measured angular dual sector, whose
limit calibration from the energy labels controls op norm at EXACT engineering price.
Then compare to *arbitrary* cutoff charts; although these are not assumed
nonredundant, a rank accounting at d=4 shows exact dimension on those reference spaces.
Thus authentic prices suffice to read ALL at 4 (still only protected *rows*).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Kintsugi
open Filter Set Function MeasureTheory Analysis Extraction Table Climb Ward Next.UVStress Spec Org Next.Rank Next.Rank.Perch
set_option maxHeartbeats 420000
open Next.Rank.Atlas Next.Rank.East MergeProof MergeProof.East Source UVNext.FreeStress Further.CorrectedLift Commission
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(U : Final C f S)(M:∀ d,ℕ→RepChart C d){ϕ:Filter UVIndex}[ϕ.NeBot]
variable {lit:ℕ→Prop}(P:Commission.Port C)(h : Rail.Outbound P lit U.room.cutoff) (hS:Ranked P)
variable (T:MaxwellData C)(hG:G.Simple)
local notation "χ"=>C.path.levels.clock.hatBeta
include hG
local notation "B!"=>Bel C.book
local notation "F!"=>C.book.grid
set_option quotPrecheck false
local notation "V!"=>(B!).Field 4
lemma four_full : Surjective (ladder C 4):=by
   have hi: Injective (ladder C 4):=fun _ _ h=>(ladder_reads _).symm.trans ((congr_arg _ h).trans (ladder_reads _))
   have hh: Module.finrank ℂ (C.label 4) ≤ Module.finrank ℂ (V!) := by
      rw [show Module.finrank ℂ (V!)=22 from four_size (F!) hG]
      have hC:= (C.labels.level 4).coords.finrank_eq
      rw [show Module.finrank ℂ (C.label 4)=Module.finrank ℂ (Labels.Label G 4) from hC.symm]
      -- existing result up_to + freelance pb
      let I:Type:=Option Face
      let F : Module.Basis I ℂ (Labels.Label G 4):= Module.Basis.mk (LinearIndependent.of_comp (embed (F!) 4) (freelance (F!) hG)) (up_to hG)
      rw [Module.finrank_eq_card_basis F,howMany]
   exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f:=(ladder C 4).toLinearMap)
      (le_antisymm (LinearMap.finrank_le_finrank_of_injective (f:=(ladder C 4).toLinearMap) hi) hh)).1 hi
lemma ladder_back : ∃ y:ℝ,0≤y∧∀v:C.label 4,∃ x:(V!), ladder C 4 x=v ∧ ‖x‖ ≤ y *mass C 4 v:=by
   let p:= ((B!).project 4).toContinuousLinearMap
   exact ⟨‖p‖,ContinuousLinearMap.opNorm_nonneg _,fun v=>by
      obtain ⟨x,h⟩:=(four_full (C:=C) hG) v
      have hx : x=p v:=by rw [← h]; exact (ladder_reads x).symm
      exact ⟨x,h,(le_of_eq (congr_arg norm hx)).trans ((p.le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_le_mass ..) (ContinuousLinearMap.opNorm_nonneg _)))⟩⟩
local notation "h'"=>U.room.kernel.spin
local notation "h!"=>T.hT.spin
variable {D k:ℕ}{Z:TableL C D}
lemma compare_out {A:Auspect S}(hA:Peal (h') A):
   ∃ y:ℝ,0≤ y ∧ ∀ {k D:ℕ}{Z:TableL C D}, Authentic U M P T k D Z→∀ _hk:4≤D,
     ∀ (L:Drop (Bel C.book))(X₁:(B!).Field 3≃ₗ[ℂ]S.Field 3), X₁ ((B!).unit 3)=S.unit 3 → X₁.toLinearMap= corrected U.sector.derivatives T.T.W L (shore M k D Z) 3 →
     ∀ (X:(B!).Field 4≃ₗ[ℂ] S.Field 4), X.toLinearMap=corrected U.sector.derivatives T.T.W L (shore M k D Z) 4→
      ∀v:C.label 4,∃ x: (V!),‖x‖ ≤ y * mass C 4 v ∧ ∀ a b:Axis,(C.S.a k)^4 • A a b (S.project 4 (M 4 k v))=A a b (X x):=by
   obtain ⟨y,hy,h⟩:= ladder_back (C:=C) hG
   refine ⟨y*24,by positivity,?_⟩
   intro k D Z H hk L X₁ hX hz X he v
   let i:Fin (D+1):=⟨4,Nat.lt_succ_of_le hk⟩
   have hS:= (H.covers i) v
   obtain ⟨j,hJ⟩:=hS
   have ht:= recovers_cost U M P T H hk j
   obtain ⟨x,hx,hW⟩:=h j
   refine ⟨x,hW.trans ((mul_le_mul_of_nonneg_left ht hy).trans (show _ ≤ y*24*mass C 4 v from ?_)),?_⟩
   · rw [hJ, mul_assoc]
   intro a b
   let F:= A a b; let W:= (Arche.aligned C M k (Z i)); let hC:=C.S.a k
   have hv : Peal (h') A := hA
   obtain ⟨l,hs,hx'⟩:= chart_rep U M T hG hk L X₁ hz hX x (Z:=Z)
   have hM : ∀ k':Signed, (B!).mirror (h!) _ k' ((B!).unit 4) = (B!).unit 4 := fun k'=> Table.mirror_unit _ _ _ _
   have hl : T.T.W.rise (Nat.le_succ 3) ((B!).unit 3)=(B!).unit 4:= T.T.W.fixs T.lit.edges T.hT.laws _
   have hh : S.project _ (W (ladder C 4 ((B!).unit 4)))= (shore M k D Z 4) ((B!).unit 4):=(shore_at M k D 4 Z hk _).symm
   let y:= (shore (S:=S) M k D Z 4) ((B!).unit 4)
   have hy: ∀ k':Signed,S.mirror (h') 4 k' y=y:= fun s'=>by unfold y; rw [← (H.straight 4 hk).reflects,hM]
   have nt: T.T.W.rise (Nat.le_succ 3) (L 3 x) = l • (B!).unit 4:= by rw [hs,map_smul,hl]
   have hr:W (ladder C 4 x)= ((hC^4:ℝ):ℂ) • M 4 k v:=by -- use W (ladder C 4 x)
      dsimp only [W, Arche.aligned,LinearMap.smul_apply,LinearMap.comp_apply]
      rw [hx,hJ]; rfl
   rw [← LinearEquiv.coe_coe X,he,hx'] -- maybe works
   rw [show sinking T L x=x-l • (B!).unit 4 from ?_,map_add,map_smul,hA.silence _ (S.unit 4) (fun s=>Table.mirror_unit ..),smul_zero,zero_add,map_sub,map_smul,map_sub,map_smul,map_sub,map_smul,hh]
   change _ = A a b (S.project _ (W ((ladder C 4) x)) - l • y)
   rw [hr,map_sub,map_smul,map_smul,map_smul,hA.silence _ _ hy,smul_zero,sub_zero,Complex.coe_smul]
   change x - ((T.T.W).rise _) _ = _; rw [nt]

def Quoter {d:ℕ}(L:S.Field d→ₗ[ℂ]ℂ)(p w k:ℕ):Prop:=∀ v:C.label d,‖L (S.project _ (M d k v))‖ ≤ (χ k)^p/(C.S.a k)^(d-w)*mass C d v
include h hS in
lemma good_out (H:OPE.Facilities C f S) (he:Observing C U.room.cutoff ϕ M)(hf:ϕ≤ f.fuse) {A:Auspect S}(hA:Peal (h') A):
    ∀ᶠ k in atTop,lit k→∀ a b,Quoter M (A a b).toLinearMap 5 4 k:=by
   by_contra! e
   obtain ⟨T,hK,hT⟩:= oracle (C:=C) hG
   let Bad(k:ℕ):= ∃ a b, ¬ Quoter M (A a b).toLinearMap 5 4 k
   have hB:∃ᶠ k in atTop, Bad k ∧ lit k:=e.mono fun _ h=> ⟨h.2,h.1⟩
   obtain ⟨g,Z,hg,hΛ,X,hX⟩:= rooted U M P h hS T H he hf hG _ hB
   obtain ⟨R,hR⟩:=lines T.hT _ T.lit.edges T.lit.hers
   obtain ⟨K,He,Ha,Hs,Hk⟩:= zooms U M P T (fun i=>(hΛ i).2.2) hX R hR
   obtain ⟨w,hw⟩:= persistent U T K hT Ha Hs
   obtain ⟨d,hd,hD⟩:= sectors_on T U K hG hK hw (vector_coherence U.room.kernel T.hT Hs) hA
   obtain ⟨y,hy,ht⟩:=compare_out U M P T hG hA
   obtain ⟨i,hw',h₃,h₄,hu,hκ,hA'⟩:= (((w.cofinal.eventually_ge_atTop 4).and ((w.cofinal.eventually (Hk 3)).and ((w.cofinal.eventually (Hk 4)).and ((w.cofinal.eventually (Hs.units 3)).and ((((hat_grows (C:=C) hG).comp hg).comp w.cofinal|>.eventually_ge_atTop (d*y)).and hD)))))).exists
   let j:=w i; let k:=g j; let β:=χ k;let r:=K.r j
   obtain ⟨a,b,hb⟩:=(hΛ j).1
   let z:=C.S.a k; have hQ := (hΛ j).2.2
   have hT:(0:ℝ)<z:= C.S.a_pos _; have hr:0<r:=K.positive _
   obtain ⟨hβ,hz,hL⟩:= clock_fee _ _ _ _ hQ
   change z≤Next.Rank.Station.gap _ _ k at hz; rw [← hX j,← He] at hz hL
   apply hb
   intro v; obtain ⟨x,hx,hQ'⟩:=ht hQ hw' R (K.U j 3) hu h₃ (K.U j 4) h₄ v
   have hx' := congr_arg norm (hQ' a b);rw [norm_smul,Real.norm_of_nonneg (pow_nonneg hT.le _)] at hx'
   rw [Nat.sub_self,pow_zero,div_one]; change ‖(A a b) _‖ ≤ β^5*mass C 4 v
   have h₁:= hA' a b
   have hp:= (shears K A j a b).le_opNorm x
   change z^4* ‖A _ _ _‖=‖_‖ at hx'
   apply le_of_mul_le_mul_left (a:=z^4) ?_ (by positivity); rw [hx']
   apply hp.trans
   apply (mul_le_mul h₁ hx (norm_nonneg x) (by change (0:ℝ)≤ d* _ ; positivity)).trans
   change d*r^4*(y*mass C 4 v)≤ _
   change r≤z*β at hL; have he':d*y≤β:=hκ
   rw [show d*r^4*(y*mass C 4 v)= r^4*(d*y)*mass C 4 v by ring]
   exact (mul_le_mul_of_nonneg_right (mul_le_mul (pow_le_pow_left₀ hr.le hL _) he' (mul_nonneg hd hy) (by positivity)) (mass_nonneg ..)).trans_eq (by ring)

include h in
lemma the_price_out {d w p:ℕ}(H:Observing C U.room.cutoff ϕ M) (L:S.Field d→ₗ[ℂ]ℂ)(hX:∀ᶠ k in atTop,lit k → Quoter M L p w k):∀ᶠ k in atTop,Quoter M L (d+p+1) w k:=by
   filter_upwards [h.covered.1.eventually hX,h.covered.2.2 d,h.scope,h.covered.1.eventually_ge_atTop (C.ref d)] with k he hv hk hp
   let i:=P.rate k
   let r:=C.S.a i / C.S.a k
   obtain ⟨A,hA⟩:= passage U.room.cutoff H hp hv.1
   have hr:0 < r:=div_pos (C.S.a_pos _) (C.S.a_pos _)
   have hR: r ≤ χ k:= hv.2.1
   have hL: C.S.a k ≤ C.S.a i:= C.S.strictAnti.antitone hv.1
   have hE:0<C.S.a i:= C.S.a_pos i
   have hV:0<C.S.a k:= C.S.a_pos k
   have hχ: χ i ≤ χ k:= WilsonStartup.Timing.hat_mono _ (Gauge.slopeConstant_pos hG).le hv.1
   have hY (i): (1:ℝ) ≤ χ i:= (C.path.levels.fits.delayed i).le
   intro v
   have hg:=he hk (A v)
   let F(j)(x:C.label d):=‖L (S.project d (M d j x))‖
   have hx:=hA.pulls v
   have hx1 : F k v = r^d * F i (A v):=by
       have hi:= congr_arg (fun y=>‖L (S.project d y)‖) hx
       simp only [map_smul,norm_smul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hV.le,Real.norm_of_nonneg (C.S.a_pos _).le] at hi
       unfold r F; rw [div_pow]; field_simp; first |exact hi.symm | linarith only [hi] -- maybe
   change F k v ≤ _
   let t:= χ k
   have ht:1≤t:=hY _
   change F i (A v) ≤ _ at hg
   rw [hx1]
   apply (mul_le_mul_of_nonneg_left hg (pow_nonneg hr.le _)).trans
   apply le_trans (mul_le_mul (pow_le_pow_left₀ hr.le hR _) (mul_le_mul (div_le_div₀ (pow_nonneg (zero_le_one.trans ht) _) (pow_le_pow_left₀ (zero_le_one.trans (hY i)) hχ p) (pow_pos hV _) (pow_le_pow_left₀ hV.le hL _)) ((hA.norms v).trans (mul_le_mul_of_nonneg_right hR (mass_nonneg ..))) (mass_nonneg ..) (div_nonneg (pow_nonneg (zero_le_one.trans ht) _) (pow_nonneg hV.le _))) ?_ (pow_nonneg (zero_le_one.trans ht) _))
   · exact le_of_eq (by rw [pow_add,pow_one,pow_add];ring)
   exact mul_nonneg (div_nonneg (pow_nonneg (zero_le_one.trans (hY _)) _) (pow_nonneg hE.le _)) (mass_nonneg ..)

include h hS in
lemma sectors_ship (H:OPE.Facilities C f S) (he:Observing C U.room.cutoff ϕ M)(hf:ϕ≤ f.fuse) {A:Auspect S}(hA:Peal (h') A):
    ∀ᶠ k in atTop, ∀ a b,Quoter M (A a b).toLinearMap 10 4 k:= eventually_all.mpr (fun a=>eventually_all.mpr fun b=>
       the_price_out U M P h hG he _ ((good_out U M P h hS hG H he hf hA).mono fun _ hi hl=> hi hl a b))
end YM.RG12.Kintsugi
