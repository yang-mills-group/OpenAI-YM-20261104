import YM.SignedWilsonExpansion.F9.Focus
/-!
# Pre-length bill on a point pulse

WCU/Bid test basis, but only one pulse and no negative-dimension area factor.
As with the appertaining smeared estimates in Shard.reproduction and TaylorGain,
such a statement requires reserving a high enough moment **before** asking for
spatial gain. The exponential widths on the source are qualitative only and may
collapse at a horizon. Use no projective positivity.
-/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG Laurent Bloch Metric
open Blue FreeResolvent Work.F08 Bank Soil Exterior Next.Free Tree Precision Power Embroider
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb
open Realm Fountain PathCost Embroider.Canvas Shard PowerSeries
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{h D a p k N t u e i j l r:ℕ}{F:Labels.Frame G h}{A x s s' B M X:ℝ}
-- Pulse versions of WCU Stable/TaylorGain's two-region proof
lemma mantleW (P:Patch)(w:Site P.L)(Q:Drip P G)(hs:0<s)(p:dragCup Bank.terrain s B Q)
    (u:ℕ)(Y:ChamberTen G (Vote D) r)(η:ℝ)(he:0≤η)(hu:η≤1)(g: Fruit 0 (η/P.L.val) u Y A):
    Fruit 0 η u (pulseS P w Q Y) ((B*tender (Hooks G) s u)^r*(9^u*A)):=by
    have hv: Fruit (P.L.val • (0:Cover)+ lift w) (η/P.L.val) u (featherS P w Y) A:=by
        rw [smul_zero,zero_add]; exact (((show Fruit (lift w) _ _ _ _ by simpa only [add_zero] using g.turn (lift w)).touch (soprano P w D) (by positivity)).more (mul_le_of_le_one_left g.C (budgetS ..)))
    have hk:= roses _ hs _ (fun _=>p) hv he hu; rw [Finset.prod_const, Finset.card_univ,Fintype.card_fin] at hk; exact hk

lemma pulse_gain (F:Labels.Frame G h)(H:Hol G)(u r:ℕ)(e:h<D)(X:ℝ)(hs:0<s)(g:h+(h+1)≤u)(hp:(h+1)*r≤u):
    ∃ C:ℝ,0≤C∧∀ (P:Patch)(w:Site P.L)(Q:Drip P G)(Y:ChamberTen G (Vote D) r)(t A M B:ℝ),
     0<t →Crank Q (h+1) s X→ Smooth Y→ mural Y→ Twig 0 t B Y→ VectorWind 0 1 u M Y→ Hears F h M Y → Fruit 0 1 u Y A →
       Fruit 0 1 u (pulseS P w Q Y) (C*(speck P^(h+1)*A+M)):=by
    by_cases hv:0≤X; swap; · exact ⟨0,le_rfl,fun _ _ _ _ _ _ _ _ _ H=>(hv H.1).elim⟩
    obtain ⟨T,hT,p⟩:= coastPrice F H r e X g hp hs; let S:= throughP s G u r; let V:= (X*tender (Hooks G) s u)^r*9^u*2^u
    have hV:0≤V:=by unfold V; have h:= tender_nn hs (Hooks G) u; positivity
    have hS:0≤S:= mul_nonneg (ceilPoly_pos ..).le (tie_nn (by positivity) _)
    let C:= T*S+V
    refine ⟨C,by unfold C; positivity,fun P w Q Y t A M B ht g' a v q m z Yp=>?_⟩; set L:ℝ:=(P.L.val:ℝ); set Z:=Pasture P.L Y
    have hL:0<L:=by unfold L; positivity
    have hx:= p P w Q Y t A M B ht g' a v q m z Yp
    have hx: Fruit 0 1 u (pulseS P w Q (Coast P.L Y)) (T*(A*speck P^(h+1)+M)*S):= twig_lp (s:=s) (V:=Vote D) hx hs u
    have hB: dragCup Bank.terrain s X Q:= g'.polish.le (div_le_self hv (by exact_mod_cast P.L.property))
    have hy:= mantleW P w Q hs hB u Z 1 zero_le_one le_rfl (cloudPay P Yp (k:=h+1) (by omega))
    let c:=min t s; have hc':0<c:=lt_min ht hs; have hk:c/L≤ t:= le_trans (div_le_self hc'.le (by unfold L; exact_mod_cast P.L.property)) (min_le_left ..)
    have he: pulseS P w Q (Coast P.L Y)+pulseS P w Q Z=pulseS P w Q Y:=by
        rw [show Coast P.L Y= Y-Z from eq_sub_of_add_eq (zoned P Y),pulse_diff P w Q (hB.mono (min_le_right ..)) Y Z q (pastureC P.L q) hc' hk, sub_add_cancel]
    rw [←he]; apply (hx.plus hy zero_le_one).more; have he:=z.fair; have hh:0≤V*M:=mul_nonneg hV he
    calc
      _ ≤ (T*(A*speck P^(h+1)+M)*S + (X*tender (Hooks G) s u)^r*(9^u*(2^u*speck P^(h+1)*A))) + V*M:= le_add_of_nonneg_right hh
      _ = _:= by unfold C V; ring

lemma nearAll (r:ℕ)(H:Hol G)(F:Frame G h)(h0:h<D)(e:h<u)(u':ℝ)(hx:0<u')(hj:4≤j)(hl:4≤l)(hg:h≤ j)(W:Embroider.Spiral h)(p:a+W.val.card≤ h):
     ∃ C:ℝ,0≤C∧∀ (g:Flight j l)(P:Patch)(w:Site P.L)(_ : P.L=g.L) (X: Carrier.Lines P.L), HEq X (linesOf g u')→ ∀ (Y:ChamberTen G (Vote D) r)(A t s Z M:ℝ), Twig 0 t A Y →0<s→dragCup Bank.terrain s Z (Agate P X G) → s/P.L.val≤t→Smooth Y→mural Y→VectorWind 0 1 u M Y→ Hears F h M Y →
     ‖Bell F a r (arret (wallope W.val D) (pulseS P w (Agate P X G) Y) h r)‖ ≤ C*M:=by
    let I:= Wait h r a×(Fin r→ Cart G h); let U (i:I):= pearls i.1 i.2; let f (i:I) j:=sampled (U i j)
    let n(i:I)(j:Fin r):=(i.1.val j).val+2
    have hq (i:I)(j):f i j∈ rangeLt _ (n i j):= through_sample _ (pearls_tapped i.1 i.2 j)
    have he (i:I):(∑ j,n i j)=a:= i.1.property
    choose E hE H' using fun i:I=> flight_p H F h0 u' hx hj hl hg (f i) (n i) (hq i) W (by rw [he i]; exact p) e
    let V:= ∑ i,E i; have hv:0≤V:= Finset.sum_nonneg fun _ _=> hE _
    obtain ⟨R,hR,hp⟩:=quarantine F a r
    refine ⟨R*V,by positivity,fun g P w hk X hX Y A t s Z M v hs u0 ha hY hv' y hK=>?_⟩; let y':=pulseS P w (Agate P X G) Y; let T:=arret (wallope W.val D) y' h r; have hM:=hK.fair
    let θ:=s/2; have hθ:0<θ:=by unfold θ; positivity
    have hQ := pulse_fares P w _ u0 Y v ha hθ.le (show θ<s from by unfold θ; linarith)
    have HH : ‖bagg G h r a T‖ ≤ V*M:=by
       refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun i=>?_); change ‖latent T (U i)‖≤ _; unfold T; rw [gems_pluck _ y' hQ hθ (canopy P w (Agate P X G) Y hY)]
       change ‖pluck y' (assay∘ f i) (wallope W.val D)‖≤ _; exact (H' i g P w hk X hX Y A t s Z M v hs u0 ha hY hv' y hK).trans (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun i _=>hE i) (Finset.mem_univ _)) hM)
    exact (hp T).trans ((mul_le_mul_of_nonneg_left HH hR).trans_eq (by ring))

variable {P:Patch}{K:Carrier.Lines P.L}{g:Flight j l}{Y:ChamberTen G (Vote D) r}
-- Weight-a leading formula at exact zero-clutter on a point. Versions of hall_top without smearing
lemma pulse_top (H:Hol G)(F:Frame G h)(w:Site P.L)(c:ℝ)(hq:P.L=g.L)(p:HEq K (linesOf g c))(hc:0<c)
    (hv:4≤l)(hm:h≤j)(h0:h<D)(hg:Twig 0 s' A Y)(hq':Wing 0 s' 0 Y)(u:Cosmos.Slate Y F k) (pp:k≤h)
    (Yp:mural Y)(yp:Smooth Y)(τ:dragCup Bank.terrain s B (Agate P K G))(δ:0<s)(α:s/P.L.val≤s')
    (ht:mural (pulseS P w (Agate P K G) Y))(W:Embroider.Spiral h)(z:a+W.val.card≤ k):
    let c:= speck P^(a+W.val.card); let X:=wallope W.val D
    Bell F a r (arret X (pulseS P w (Agate P K G) Y) h r)= c • Bell F a r (arret X Y h r):=by
   intro c' X; let δ':=s/2; have hv':0<δ':=by unfold δ'; positivity
   let b:=pulseS P w (Agate P K G) Y; let T:=arret X b h r; let U:=arret X Y h r
   have hh:= pulse_fares P w _ τ _ hg α hv'.le (show δ'<s from by unfold δ'; linarith)
   have hx:= lt_of_lt_of_le (div_pos δ (by positivity)) α
   have he:a≤ h:= by omega
   have hX : Tensor.Sym (T-c' • U):=fun x t=> congr_arg₂ (·-·) (arret_seal X b h r hh hv' x t) (congr_arg (c' • ·) (arret_seal X Y h r hg hx x t))
   have hU : seedTile (T-c' • U) a ∈ localFields G h:= by rw [sub_eq_add_neg,← neg_smul,seeding_sum,seeding_scale]; exact Submodule.add_mem _ (seed_paint H X hh hv' ht h r he) (Submodule.smul_mem _ _ (seed_paint H X hg hx Yp _ _ he))
   change Bell F a r T=_; apply sub_eq_zero.mp; rw [← map_smul,← map_sub,bell_floor F (T-c' • U) hX hU]; funext ⟨Z,r'⟩
   let A': Fin r→Snap G h:= pearls Z r'; let M:=Z.val; let f:= fun i=>sampled (A' i); let n i:= (M i).val+2
   have ha: (∑ i,n i)=a:= Z.property
   have hB i: f i∈ rangeLt _ (n i):= through_sample _ (pearls_tapped Z r' i)
   change latent T A'- c' • latent U A'=0; unfold T U; rw [gems_pluck A' b hh hv' (canopy P w (Agate P K G) Y yp),gems_pluck A' Y hg hx yp, sub_eq_zero]
   unfold c'; rw [←ha]; exact harbour P g hq.symm K c hc p w hv hm Y hg f n hB (fun i=>by unfold n; omega) hq' u Yp yp pp H τ δ α W h0 (ha.symm ▸ z)
end YM.WilsonCoeffUV.Mer.Xa
