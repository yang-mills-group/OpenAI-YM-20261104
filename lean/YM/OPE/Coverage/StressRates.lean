import YM.OPE.Coverage.StressMeter

/-!
# All-length polylog bound with the correct power on physical stress tuples
in the symmetric Euclidean theory. Aperture condition is pairwise cube-dist
only; this part is an unselected-table estimate (no optimized dependence on
ratios). Threshold is for each arity/clearance, not across arbitrary demand.
-/
set_option autoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.OPE.Coverage
open Function Set Filter Table Extraction Ward Climb Spec Maxwell Org Maxwell Next.UVStress Extra Real Pert
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
open WeakScaling
variable {G:Gauge}{C:Family G}{F:Order}{S:Table C.book} (U :Final C F S)
variable {R:ℝ}{d D N n m:ℕ}
set_option quotPrecheck false
local notation "Φ" => U.sector.derivatives
local notation "𝐄" => U.sector.energy
local notation "E₀" => reCenter S (U.sector.energy)
local notation "𝒟" => fun e=>Nonempty (YM.Spin.change S e)

def stressing (r:ℝ)(a c:Fin m→Axis):Fin m→ S.Tag:=hang (T:=S) (fun _:Fin m=>4) (fun i=> r^4 • U.sector.energy (a i) (c i))
variable (earlier : ∀ d:ℕ,  Nonempty (YM.Spin.change S d))

include earlier
lemma grid_test (a c:Fin m→Axis)(hr:Services C F S)(hg:G.Simple)(ht:Paved C F)(hDir : (E₀: S.Stress)≠0)
     (r:ℕ→ℝ)(hτ:Fine r) (y:ℕ→Points m) (η:ℝ) (hη:0<η)(hz:∀ᶠ i in atTop, y i∈airy m (η*r i)) :
    Poly r (fun i=>disc (stressing U (r i) a c) (y i)) := by
      obtain ⟨W,hW,-⟩:=Maxwell.Free.maxwell_supplies C hg 1 one_ne_zero
      obtain ⟨P,hJ,hD,hK,hH,h0,ht0,hF⟩:= YM.UVNext.FreeStress.fire hg W 1 one_ne_zero
      have hD : P.T.W = Maxwell.Free.scheme C.labels:=hD.trans (congr_arg Lighthouse.W hW)
      obtain ⟨D,N,m₀,R,hR,hA⟩:=unique_ξ (J:= (E₀)) hF U.phase.transport.injection U.phase.transport.derivatives hDir (centered_pre U) (expectation_zero U)
      let k:= max D 4 + m₀ + 1
      obtain ⟨n,L,Q,h₁,h₂,h₃,hq,h₅⟩:=equipment P.hT k (max N m) R
      let n':=n+1
      obtain ⟨p,hp⟩:=under_produced U (r:=r) ht hτ n L Q hq hr
      have hv' (e:ℕ)(he:e≤k):Equipped P.hT e n' L Q:= by
        obtain ⟨w,hw,hs⟩:= h₅ e he; exact ⟨w,hw,fun i hi=> let H:=hs i hi; ⟨H.1.trans n.le_succ,H.2⟩⟩
      obtain ⟨b,hb,hZ,hV⟩ := deploy_ledger U p P.hT earlier P.T.W (le_refl Q) hq hv' h₂ (N:=n') hg (by omega) le_rfl P.lit.edges P.lit.hers P.lit.pales
      have h₄ : 4 ≤ k := by omega
      let old j d := (oldChart U p.toShelf d j (earlier d))
      have h': ∀ x≤k, ∀ᶠ i:ℕ in atTop,Bijective (p.maps i x):= fun x hx=>shelf_equipment_bij U p.toShelf P.hT earlier (le_refl Q) hq ?equip h₂ _ hx
      case equip => intro e he; obtain ⟨w,hw,hs⟩:= h₅ e he; exact ⟨w,hw,fun i hi=> let H:=hs i hi; ⟨H.1.trans n.le_succ,H.2⟩⟩
      have Hs(a c : Axis) : Poly r (fun i=> (old i 4).symm (r i^4 • (𝐄) a c)) := shelf_stress U p earlier b hb (hV 4 h₄) (h' 4 h₄) h₄ (hA b (by omega) (show 1 ≤ n' from Nat.le_add_left ..) ((le_max_left N m).trans (h₁.trans n.le_succ)) h₃) hτ a c
      let v(i):=fun j:Fin m=>(old i 4).symm ((r i)^4 • (𝐄) (a j) (c j))
      have hy : ∀ᶠ i in atTop, y i∈airy m (p.path i / (2*Q)) := by
         have he' :=hp.eventually (gt_mem_nhds (by positivity : 0<η*(2*Q))) -- lt/gt reversed
         filter_upwards [hz,he'] with i hi he u l hu
         exact (hi u l hu).trans_le' (by change p.path i / (2*Q) ≤ _; have hh:= (div_lt_iff₀ (hτ.1 i)).mp (show p.path i / r i < η*(2*Q) from he); apply (div_le_iff₀ (by positivity)).mpr; linarith only [hh])
      have hp :=airy_moving p hq (fun _:Fin m=>4) v hτ (((le_max_right N m).trans h₁).trans n.le_succ) (fun _=>h₄.trans h₂) y (fun i=>Hs ..) hy
      refine hp.congr ((h' 4 h₄).mono fun i hi=> congr_arg (fun f:Fin m→S.Tag => Ward.disc f (y i)) ((funext fun j=> (?datum))))
      case datum => refine Sigma.ext rfl (heq_of_eq (?term : (p.maps i 4 (v i j))=_)); erw [← old_agrees U p.toShelf earlier i _ hi,LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply]; rfl

theorem stress_all(a c:Fin m→Axis)(h:Services C F S)(p:Paved C F)(hX: (E₀ : S.Stress)≠0)(η:ℝ)(hη:0<η): ∃ b:ℝ,0≤ b ∧
   ∀ᶠ r in 𝓝[>] 0,∀ z∈ airy m (η*r), ‖disc (stressing U r a c) z‖ ≤exp (b*log (1-log r)):=by
      by_contra! hq
      have hBad(i:ℕ):∃ r:ℝ,0<r ∧ r<1/(i+1:ℝ) ∧ ∃ z∈airy m (η*r), exp ((i:ℝ)*log (1-log r)) < ‖disc (stressing U r a c) z‖:=?witness
      case witness =>
        have h:=hq i (Nat.cast_nonneg _)
        have ht: ∀ᶠ r in 𝓝[>] (0:ℝ),0 < r ∧ r<1/(i+1:ℝ):= (show ∀ᶠ r:ℝ in 𝓝[>] 0,r∈Ioi (0:ℝ) from self_mem_nhdsWithin).and (mem_nhdsWithin_of_mem_nhds (gt_mem_nhds (by positivity)))
        obtain ⟨r,hr,hw⟩:= (h.and_eventually ht).exists -- frequently? `.and_eventually`
        
        exact ⟨r,hw.1,hw.2,hr⟩
      choose r hpos hprice x hX' hy using hBad
      have hr: Tendsto r atTop (𝓝[>]0):=tendsto_nhdsWithin_iff.mpr ⟨squeeze_zero (fun i=>(hpos i).le) (fun i=>(hprice i).le) tendsto_one_div_add_atTop_nhds_zero_nat,Eventually.of_forall hpos⟩
      have hf:Tendsto (mark r) atTop atTop := tendsto_neg_atTop_iff.mpr (Real.tendsto_log_nhdsGT_zero.comp hr)
      obtain ⟨b,hB⟩ := grid_test U earlier a c h h.simpleGate p hX r ⟨hpos, hf⟩ x η hη (Eventually.of_forall hX')
      obtain ⟨i,h₁,h₂,h₃⟩ := (((tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop (b+1)).and ((fare_large r ⟨hpos,hf⟩).eventually_ge_atTop 0 |>.and (hB (b+1) (by linarith)))).exists
      refine (lt_of_lt_of_le (hy i) (h₃.trans (Real.exp_monotone ?_))).false
      exact mul_le_mul_of_nonneg_right h₁ h₂

-- physical restoring factor exactly
lemma stress_restore(a c:Fin m→Axis){y:Points m}{t:ℝ} (ht:0<t): ‖disc (stressing U t a c) y‖ = t^(4*m)*‖disc (stressing U 1 a c) y‖:=by
      have hh i : (1:ℝ)^4 • (𝐄) (a i) (c i)=(𝐄) (a i) (c i):=by rw [one_pow,one_smul]
      let T:= S.classMoment S (fun _:Fin m=>4) y
      unfold stressing hang Ward.disc Table.useAt
      simp only [hh,RCLike.real_smul_eq_coe_smul (K:=ℂ)]
      have he: T (fun i=> (↑(t^4):ℂ) • (𝐄) (a i) (c i)) = _ := T.map_smul_univ _ _
      change ‖T (fun i=> (↑(t^4):ℂ) • U.sector.energy (a i) (c i))‖ = _
      rw [he,norm_smul]
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin, norm_pow, Complex.norm_real,Real.norm_of_nonneg (pow_nonneg ht.le _),← pow_mul]
      rfl
end YM.OPE.Coverage
