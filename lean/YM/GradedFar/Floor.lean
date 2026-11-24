import YM.GradedFar.Nimbus
/-!
# On `m_N` itself in (G.9.ii)

This specifically for **constant reference implementation** (Root F etc. Y_r constant physical present & unit convention).
Point queries any meshes on paired tail. Does not compare file history nor T-tr estimators or assert
`m_N` equals such a comparator. Slack exp chosen for g-threshold after fixing geometry and extra
precision. Centers of authentic reading can actually be translated arbitrarily on that later mesh.
Translation of ALL slots also of later replacement still uses same s. (And if reading at
unrounded o rather than grid s, the target continuum S reading here is exactly translation-
invariant.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Auth
open Function Filter Set PowerSeries Metric
open Extraction Table Spec PhysMS Trace.Pilot OPE OPE.Orbits Lattice FullVolume
open XSpace XSpace.Normalize XSpace.Structure1 FVA2 FVA2.Scale FVA2.Scale.Facets FVA2.Scale.Equator FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh
open MS MS.Native MS.Land MS.Fleet Neighbor Tariff Tariff.Playbill Tariff.Crosser Tariff.Billboard Tariff.Sunshine Batch
open Fork (Sold Safe)
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
   (R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (J P:ℝ→tower S) (Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
   {hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H:Main.Match Z hG M σ true) (ν:ℝ)
    {t:ℝ→ℝ}(Ht:Pose F J Z t)(hF:Prepared F J P Z t)(Hq:LogTrace F R.port)
variable {n m h p:ℕ} {K K':Set (Points n)}{N N':Set (Points m)} {U B:ℝ}
local notation "g∴"=> strength G
local notation "X"=> Scale.Measure.outlook Z.scheme Z.criterion
local notation "S•"=> moving G U B
local instance {n:ℕ} : ContinuousSMul ℝ (Points n):= IsBoundedSMul.continuousSMul

def rounded (C:Family G)(r:ℝ)(p:ℕ)(u:Positions n):Points n:= r⁻¹ • Order.grid C p u
lemma targeted (C:Family G){r:ℝ}(hr:0<r)(p:ℕ)(u:Positions n): Order.grid C p u = r • rounded C r p u:= (smul_inv_smul₀ hr.ne' _).symm
lemma landscape (T:ℝ)(K:Set (Points n))(N:Set (Points m))(hK:IsCompact K)(hN:IsCompact N):
    IsCompact {x:Points (n+m)| Fits K N T x}:= by
    let f : Points n × Points m → Points (n+m):= fun p=> forest p.1 (T • p.2); have h:Continuous f:= continual continuous_fst (continuous_snd.const_smul T)
    have hQ : {x:Points (n+m)| Fits K N T x}= f '' (K ×ˢ N) := by
        ext x; constructor
        · rintro ⟨a,ha,b,hb,rfl⟩; exact ⟨(a,b),⟨ha,hb⟩,rfl⟩
        rintro ⟨⟨a,b⟩,⟨ha,hb⟩,rfl⟩; exact ⟨a,ha,b,hb,rfl⟩
    rw [hQ]
    exact (hK.prod hN).image h
-- cost for m_N all H_r on this R. precision g^k includes copying/scaling. same through GridMoments pulse budgets;
-- all placements precise enough (thus in particular report f at those `r` with rounding hypotheses). paired tails of finite costs so no conditional scope. uniform positions & mesh origins, shape paths.
variable {d:Fin (n+m)→ℕ}(ha:AppointedH140Through h d)
def FullSales (U B:ℝ)(K:Set (Points n))(N:Set (Points m))(d:Fin (n+m)→ℕ)(q:ℕ)(S':ℝ):Prop:= ∃ b:ℝ,0≤b ∧
    ∀ᶠ p in moving G U B, ∀ᶠ i : ℕ×ℕ in (again f).fuse, Awarded (C:=C) d i.1 i.2 ∧ ∀ s x, Fits K N p.2 x →
    ∀ y : Positions (n+m), ‖rounded C p.1 i.1 y - x‖ ≤ S'*g∴ p.1^(q+1) → ∀ u:AppointedH140Inputs G d, Box u 1 →
        ‖assemble F P (fun _=>p.1) d i.1 i.2 s y u-nl P d (fun _=>p.1) (p.1•x) u‖ ≤ b*g∴ p.1^q
variable (hU:0<U)(hB:0<B)(hK:IsCompact K)(hx:K⊆conf n)(hN:IsCompact N)(hz:N ⊆ Outside m)
    (hQ:FullVolume.FixedBounds C)(hp:ClusterFrames C)(hC:C.Makes)
include hK hx hN hz hU hB hQ hp hC H Ht hF Hq ν ha
theorem within_sales (q:ℕ)(S':ℝ)(he:0≤S'): FullSales F P U B K N d q S' := by
    obtain ⟨K',N',hK',hN',hk,hn,hx',hz'⟩:= Crosser.larger hK hN hx hz
    obtain ⟨b,d',hb,hd,H⟩:= rounding F R J P Z M H ν Ht hF Hq ha hU hB hK hx hN hz hK' hx' hN' hz' hk hn
    have hv:Tendsto (fun r=> S'*g∴ r^(q+1)) trail (𝓝 0):= by simpa using ((Coupling.conforms hG (strength_coupling hG)).pow (q+1)).const_mul S'
    refine ⟨1+b*S',by positivity,?_⟩
    filter_upwards [poses (hv.eventually_lt_const hd), H, Road.funded_forms hK' hx' hN' hz' (W:=appointment K' N') (z:=fun p x=>x)
       (fun _ _ h=> h), poses (strength_positive hG), poses (show ∀ᶠ r in trail,0<r from self_mem_nhdsWithin)] with p hs H hi hT hr
    let Ω:= (fun x:Points (n+m)=> p.1 • x) '' {x:Points (n+m)| Fits K' N' p.2 x}; have hX:IsCompact Ω:= (landscape _ _ _ hK' hN').image (continuous_id.const_smul p.1)
    have hx:Ω⊆conf (n+m):= by rintro x ⟨q,hq,rfl⟩; exact Work.A05.smul_conf hr (hi q hq)
    filter_upwards [unselected_fixed F P hX hx hQ hp hC d (fun _=>p.1) (g∴ p.1^q) (by positivity)] with i H'
    refine ⟨H'.1,fun s x hx y he u hu=>?_⟩
    obtain ⟨hy,H⟩:= H _ hx _ (he.trans_lt hs)
    specialize H u hu; let m:=Order.grid C i.1 y; have ht:m∈ Ω:= ⟨rounded C p.1 i.1 y,hy,(targeted C hr _ _).symm⟩
    refine (opt _ _ (nl P d (fun _=>p.1) m u)).trans ((add_le_add (H'.2 _ _ ht _ hu) (d:= b*S'*g∴ p.1^q) ?ble).trans_eq (by ring))
    unfold m; rw [targeted C hr]; refine H.trans ((mul_le_mul_of_nonneg_left he (by positivity)).trans_eq ?_); rw [pow_succ]; field_simp
omit hK hx hN hz hU hB hQ hp hC H Ht hF Hq ν ha
-- exact a concrete choice of Mesh offsets in these Y units at a given f-grid *when using direct rounding*, cf. `nearest`.`nogap.`
-- Works paired tails after λ=r,T. address each position EXACT for this order & all δ; never need change test.
theorem valid_round (r:ℝ)(hr:0<r)(δ:ℝ)(hd:0<δ): ∀ᶠ z in (again f).fuse,
    ∀ x:Points n, ‖rounded C r z.1 (address (C.S.a z.1) (r•x)) - x‖ < δ := by
 refine (Order.fused (again f) _).mpr (Eventually.of_forall fun i=> ?_)
 filter_upwards [FullVolume.nearest (n:=n) (C:=C) Extraction.Sequence.full (mul_pos hd hr)] with i hi x
 let A:= address (C.S.a i) (r•x); let m:= rounded C r i A-x; change ‖m‖<δ; specialize hi (r•x)
 change dist (Order.grid C i A) (r•x)<δ*r at hi; rw [dist_eq_norm,targeted C hr,← smul_sub,norm_smul, Real.norm_of_nonneg hr.le] at hi; exact
    lt_of_mul_lt_mul_left ((show r*‖m‖<δ*r from hi).trans_eq (mul_comm ..)) hr.le
end YM.Integration.GradedFar.Auth
