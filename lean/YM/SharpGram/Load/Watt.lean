import YM.SharpGram.Load.Key

/-!
# Projection lifetime for the stress leg.
True price on **all representatives including before projection** after
limit receipt, stress-sector in output. Need still other sectors and
higher horizons. No strengthening of log-OPE geometry in this file.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SharpGram.Load
open Function Filter Set Table Climb Analysis Org Extraction Spec Next.UVStress Maxwell
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
set_option quotPrecheck false
variable {G: Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book} {F:Final C f S}
open UVNext.FreeStress
local notation "X"=> Bel C.book
local notation "Z"=> UVNext.FreeStress.canonicalStress C.labels
local notation "T!"=> F.phase.transport
local notation "Z'"=> wing F
local notation "α"=> F.sector.turns
local notation "E"=> Maxwell.Free.gear C.labels
variable {u:Filter (ℕ×ℕ)} (B:Lenses.Mantle F u)
local notation "A"=> tent B
local notation "W"=> S.Field 4
local notation "r"=> B.radius

section numeric
variable {k l:ℕ}{c:ℂ}
def literal (k:ℕ) (c:ℂ) := ∀ i j:Axis,(A k 4).symm (wing F i j)=c • Z i j
variable (h:literal B k c)
include h
lemma wingOut {v : W} (hx:v∈zone (wing F)) : (A k 4).symm v ∈ zone Z := by
   apply cross_line (w:=(A k 4).symm.toLinearMap) _ hx; intro i j
   change (A k 4).symm _ ∈ _; rw [h];exact Submodule.smul_mem _ _ (line_mem Z i j)
lemma oppositePick (hc:c≠0)(i j:Axis) : A k 4 (Z i j)=c⁻¹ • wing F i j := (A k 4).symm.injective (by rw [LinearEquiv.symm_apply_apply,map_smul,h i j, inv_smul_smul₀ hc])
lemma wingIn (hc:c≠0) {v} (hx:v∈zone Z) : A k 4 v∈zone (wing F):= by
    apply cross_line (w:=(A k 4).toLinearMap) _ hx; intro i j; change A k 4 (Z i j)∈ _
    rw [oppositePick B h hc]; exact Submodule.smul_mem _ _ (line_mem _ i j) -- use without .. (∈ Submodule preservation)
lemma wingMove (hc:c≠0){w:ℂ} (hw:literal B l w)(hz:w≠0)(x:(Bel C.book).Field 4)(hx:x∈zone Z):
       A k 4 x= (w/c) • A l 4 x := by
    apply Submodule.span_induction (p:=fun y _=> A k 4 y=(w/c) • A l 4 y) _ _ _ _ hx
    · rintro _ ⟨⟨i,j⟩,rfl⟩; rw [oppositePick B h hc,oppositePick B hw hz,smul_smul];congr 1;field_simp
    · simp
    · intro _ _ _ _ he ht; rw [map_add,map_add,smul_add,he,ht]
    intro t _ _ he; rw [map_smul,map_smul,he,smul_comm t]

omit h
lemma literal_gain (hg:OPE.Services C f S) : ∃ c: ℕ→ℂ, Tendsto (fun k=> ((r k^4:ℝ):ℂ)*c k) atTop (𝓝 (-1)) ∧
    ∀ᶠ k in atTop,c k≠0 ∧ ‖(c k)⁻¹‖ ≤ 2*r k^4 ∧ literal B k (c k):=by
   obtain ⟨z,hz,H⟩:=ledger_delta B hg
   let i (k:ℕ):ℂ:=((B.radius k^4:ℝ):ℂ)
   let c(k:ℕ) := z k/i k; have hi(k):i k≠0:=by exact Complex.ofReal_ne_zero.mpr ((pow_pos (B.positive k) 4).ne')
   have hc(k): z k=i k*c k:=by unfold c; field_simp [hi k]
   refine ⟨c,hz.congr (fun k=>(hc k)),?_⟩
   filter_upwards [hz.eventually_ne (b₂:=0) (by norm_num), H,hz.norm.eventually (le_mem_nhds (by norm_num:(1/2:ℝ)<‖(-1:ℂ)‖))] with k hk hK h'
   refine ⟨div_ne_zero hk (hi k),?_,fun a b=> ?_⟩
   · unfold c; rw [inv_div, norm_div, show ‖i k‖=r k^4 from by simp [i,(B.positive k).le], div_le_iff₀ (norm_pos_iff.mpr hk)]; have hg := mul_le_mul_of_nonneg_right h' (show 0≤ r k^4 from pow_nonneg (B.positive k).le _); linarith only [hg]
   have hx:= hK a b; change _ = c k • Z a b; rw [map_smul,hc k,mul_smul] at hx
   exact smul_right_injective ((X).Field 4) (hi k) hx -- W wrong

lemma motions {k:ℕ}(h:IsUnit (shift B k 4)) (v:Ortho)(x:S.Field 4): (A k 4).symm ((α).act 4 v x)= (E).act 4 v ((A k 4).symm x):=by
    apply (A k 4).injective; rw [LinearEquiv.apply_symm_apply,tensor_edge B h,LinearEquiv.apply_symm_apply]
end numeric

local notation "P"=> C.path.levels.clock.hatBeta
variable (hg:OPE.Services C f S)
include hg
lemma watts : ∃ K:ℝ, ∃ p:Module.End ℂ ((Bel C.book).Field 4), ∃ q:Module.End ℂ (S.Field 4),
    0≤ K ∧ Retraction (zone Z) E p ∧ Retraction (zone (wing F)) α q ∧ q (S.unit 4)=0 ∧ q ≠ 0 ∧
    ∀ᶠ k in atTop, ∀ x,
       q (A k 4 x)= A k 4 (p x) ∧ ‖q (A k 4 x)‖ ≤ K*(B.radius k)^4* ‖x‖ := by
   obtain ⟨p,hp,hh,h0⟩:= absolutely (C:=C) hg.simpleGate
   obtain ⟨c,Hc,hc⟩:= literal_gain B hg
   obtain ⟨l,hL,hl,HL⟩:= ((tented B hg 4).and ((authored B hg 4).and hc)).exists
   let Y:=A l 4
   let q:= Y.toLinearMap.comp (p.comp Y.symm.toLinearMap)
   have Hq (x): q x=Y (p (Y.symm x)):=rfl
   have hpQ (x) : q (Y x)=Y (p x):=by rw [Hq,Y.symm_apply_apply]
   let L:= LinearMap.toContinuousLinearMap (Y.toLinearMap.comp p)
   let K:= 2*(‖c l‖ * ‖L‖)
   have ht : q (S.unit 4)=0 := by
       rw [← show Y ((X).unit 4)=_ from (hl.1 4 le_rfl).2.2, hpQ,h0,map_zero]
   have hq: Retraction (zone (wing F)) α q:= by
       refine ⟨fun v x=> ?_,fun x=>wingIn B HL.2.2 HL.1 (hp.slides _),fun x hx=>?_⟩
       · simp only [Hq,show ∀ x:S.Field 4,Y.symm ((α).act 4 v x)=(E).act 4 v (Y.symm x) from motions B hL v,hp.inter_ v]
         exact tensor_edge B hL _ _
       rw [Hq, hp.fixes _ (wingOut B HL.2.2 hx), Y.apply_symm_apply]
   have hz : q≠0 := by
       intro h
       obtain ⟨i,j,hij⟩:=canView (C:=C) hg.simpleGate
       have he := hpQ (Z i j); rw [hp.fixes _ (line_mem _ i j)] at he; apply hij; apply Y.injective
       rw [← he,h,map_zero]; rfl
   refine ⟨K,p,q,(by unfold K; positivity),hp,hq,ht,hz,?_⟩
   filter_upwards [hc,tented B hg 4] with k hk hK x
   let η:= A k 4; let ψ : Module.End ℂ ((Bel C.book).Field 4) := Y.symm.toLinearMap.comp η.toLinearMap
   have he:Intervenes E ψ:= by
       intro v a; change Y.symm (A k 4 ((E).act 4 v a))=_; rw [tensor_edge B hK]; exact motions B hL _ _
   have Hx : q (η x)= η (p x):=by
      rw [Hq,show p (Y.symm (η x))=_ from hh ψ he x]; exact Y.apply_symm_apply _
   refine ⟨Hx,?_⟩
   rw [show q _=η (p x) from Hx,wingMove B hk.2.2 hk.1 HL.2.2 HL.1 _ (hp.slides x)] -- eta defeq?
   calc
     _ = ‖(c k)⁻¹‖ *(‖c l‖ * ‖L x‖) := by rw [norm_smul,div_eq_mul_inv,norm_mul]; change ‖c l‖ * ‖(c k)⁻¹‖ * ‖L x‖ = _; ring
     _ ≤ (2 * r k^4)*(‖c l‖ * (‖L‖*‖x‖)) := mul_le_mul hk.2.1 (mul_le_mul_of_nonneg_left (L.le_opNorm x) (norm_nonneg _)) (by positivity) (by positivity [B.positive k])
     _ = _ := by unfold K;ring

include B
/-- Partial MatrixTicket.outlet with genuine fixed-field (upper bound
for all representatives) and exact cancellation on input scale after
engineering shift across actual rotation. This projection onto traceless
stress doesn't require representatives themselves to lie in a low sector;
quote all. d=w=4. No positivity hypotheses, and don't change u for
field-family contingencies, under refinements specified. -/
theorem outletStress : ∃ q:Module.End ℂ (S.Field 4), Retraction (zone (wing F)) α q ∧ q (S.unit 4)=0 ∧ q≠0 ∧
     ∀ w:S.Field 4 →ₗ[ℂ] ℂ, Kills F.sector.derivatives (d:=4) (w:=4) le_rfl (w.comp q) ∧ Releases C u 4 4 (w.comp q):=by
   obtain ⟨K,p,q,H,hp,hq,ht,hZ,h⟩:= watts B hg
   refine ⟨q,hq,ht,hZ,fun w=> ?_⟩
   constructor
   · intro e he x; obtain ⟨t,hx⟩:= Trace.first_grade F hg.simpleGate he x
     rw [hx,map_smul,F.sector.derivatives.fixs (T!).injection F.room.kernel.laws,map_smul]; simp [ht]
   let L := LinearMap.toContinuousLinearMap w
   let Z0 := 2* Lenses.bonus C 4
   have h0 : 0≤Z0:= by unfold Z0; positivity [Lenses.bonused C 4]
   refine ⟨9,?_⟩
   filter_upwards [investors B hg 4,h,B.proper,(Next.Rank.Station.hat_rate C.path.levels hg.simpleGate).eventually_ge_atTop (‖L‖*K*Z0)] with k hk he hA hK
   intro v hv hu y x z hy hx
   have ht := hk.2 v hv hu y x z hy hx; let a:= C.S.a k; let i:=(A k 4).symm (S.project _ x)
   have hY := (he i).2; rw [show A k 4 i=S.project _ x from LinearEquiv.apply_symm_apply ..] at hY
   have hz : 0≤z:=by obtain ⟨j,hj⟩:= hy.exists; exact (quota_nonneg ..).trans hj
   simp only [tsub_self,pow_zero,div_one]
   have ha:= C.S.a_pos k
   have hb:=B.positive k
   have hv' : 0<P k := zero_lt_one.trans (C.path.levels.fits.delayed k)
   apply (L.le_opNorm _).trans
   calc
    _ ≤ ‖L‖ * ((K*(a* (P k)^2)^4)*(Z0/a^4*z)) :=
      mul_le_mul_of_nonneg_left (hY.trans (mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb.le hA.2 _) H) ht (norm_nonneg _) (by positivity [ha]))) (norm_nonneg L)
    _ = (‖L‖*K*Z0) * P k^8 * z := by unfold a;field_simp
    _ ≤ (P k)^9*z := by rw [show P k^9 = (P k)*(P k)^8 from pow_succ' _ _]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK (by positivity)) hz
end YM.SharpGram.Load
