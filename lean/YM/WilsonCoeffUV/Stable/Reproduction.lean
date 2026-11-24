import YM.WilsonCoeffUV.Stable.Evaluations
/-! # Post price on potential probes. Rescaling on test included. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.WilsonCoeffUV.Shard
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n c:Side}{U V:Type*}{r h D l j e k a m u:ℕ} {G:Gauge}{F:Labels.Frame G h}{s t A X B C δ:ℝ}
lemma nomadic (H:Hol G)(F: Frame G h)(e:h<D)(n:Fin r→ℕ)(v: Fin r→ℝ)(hv:∀ i,0≤ v i) (W:Embroider.Spiral h)(hW: (∑ i,n i)+W.val.card≤h)(y: (i:Fin r)→Pane (n i))(j:Embroider.Spiral W.val.card)(h0:h<u):
    ∃ C:ℝ, 0≤ C∧ ∀ (P:Patch)(w:Site P.L)(t A M:ℝ)(Y:ChamberTen G (Vote D) r)(c: (i:Fin r)→ Prism G.Color (n i)), (∀ i j, ‖c i j‖≤ v i*speck P^(j.val+1))→0<t→ Twig 0 t A Y→Smooth Y→mural Y→VectorWind 0 1 u M Y→ Hears F h M Y →
      ‖(halo P w j.val (testa D W.val)) • pluck Y (fun i=> assay (shim P w (c i) (y i))) (wallope j.val D)‖≤ C*M:=by
   let m i:=lustre (y i); let L:= ∑ i,m i; let b:=j.val.card
   have he:L+b≤h:= (Nat.add_le_add (Finset.sum_le_sum (fun i _=>lustre_cap _|>.trans (show n i≤ n i from le_rfl))) j.property).trans hW
   obtain ⟨T,hT,hg⟩:= gateway H F m j.val he le_rfl D h0
   choose C hc H' using fun i=> shim_money G (y i)
   let V:= ∏ i,C i*v i; have hV :0≤ V:= Finset.prod_nonneg fun _ _=> mul_nonneg (hc _) (hv _)
   let X:= ‖wallope W.val D‖; have hx:0≤X:=norm_nonneg _
   refine ⟨T*V*X,by positivity, fun P w t A M Y c θ ht t0 pY g u' R=>?_⟩
   set Q:= speck P; have hp:0<Q:= speck_pos _; have heM:=R.fair
   let F i:= shim P w (c i) (y i); let N:= ∏ i,slideRank (m i) (F i)
   have hu: ‖pluck Y (assay ∘ F) (wallope j.val D)‖≤T*M*N:= hg t Y A M ht t0 g pY R u' F (fun i=>shored P w (c i) (y i))
   have hh: N ≤ V*Q^L:= (Finset.prod_le_prod (s:= Finset.univ) (fun i _=> slide_nn (m i) (F i)) (fun i _=> H' i P w (v i) (c i) (hv i) (θ i))).trans_eq (by rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum])
   rw [norm_smul]; refine (mul_le_mul (halo_bound P w _ j.val (le_trans j.property (W.property.trans e.le))) (hu.trans (mul_le_mul_of_nonneg_left hh (by positivity))) (norm_nonneg _) (by positivity [speck_pos P])).trans ?_
   change Q^b*X*(T*M*(V*Q^L))≤ _; rw [show Q^b*X*(T*M*(V*Q^L))= T*V*X*M*Q^(L+b) by ring]; exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ hp.le (speck_le P))
lemma flight_p (H:Hol G)(F: Frame G h)(h0:h<D)(u':ℝ)(hx:0<u')(hj:4≤j)(hl:4≤l)(hg:h≤j)(p:Fin r→ Place.Potential G)(n:Fin r→ℕ)(hn:∀ i,p i ∈ rangeLt _ (n i))(W:Embroider.Spiral h)(hp:(∑ i,n i)+W.val.card≤h)(e:h<u): ∃ C:ℝ,0≤ C∧∀ (g:Flight j l)(P:Patch)(w:Site P.L)(_hk:P.L=g.L)(X: Carrier.Lines P.L), HEq X (linesOf g u')→∀ (Y:ChamberTen G (Vote D) r)(A t s Z M:ℝ), Twig 0 t A Y →0<s→dragCup Bank.terrain s Z (Agate P X G)→s/P.L.val≤t→Smooth Y→mural Y→VectorWind 0 1 u M Y→Hears F h M Y →
      ‖pluck (pulseS P w (Agate P X G) Y) (assay ∘ p) (wallope W.val D)‖≤ C*M:=by
   have hv i:n i≤ j:= (Finset.single_le_sum (f:=n) (fun _ _=> Nat.zero_le _) (Finset.mem_univ i)).trans ((Nat.le_add_right _ _).trans (hp.trans hg))
   choose b hb hxq using fun i=>Carrier.analyze (p i) (hn i)
   choose C hc h using fun i=> Carrier.deliver (E:=G.Color) u' hx hj hl (n i) (hv i)
   let T i:= C i*Carrier.pile (b i); have hT i:0≤ T i:= mul_nonneg (zero_le_one.trans (hc _)) (Carrier.pile_pos _)
   choose B hB hu using fun (y:(i:Fin r)→Pane (n i))(u:Embroider.Spiral W.val.card)=> nomadic H F h0 n T hT W hp y u e
   refine ⟨∑ y,∑ u,B y u,Finset.sum_nonneg fun _ _=> Finset.sum_nonneg fun _ _=> hB _ _,fun g P w hk X hz Y A t s Z M t' p' q v ev em et eqM=>?_⟩
   choose d hd using fun i=> h i g (b i)
   have he' (L:Side)(X:Carrier.Lines L)(e:L=g.L)(p:HEq X (linesOf g u')): Whole X∧∀ i,Carrier.Reel X (b i) (d i) (C i):= by
       subst L; rw [eq_of_heq p]; exact ⟨stored g u' hx hl,hd⟩
   obtain ⟨heX,heQ⟩:=he' P.L X hk hz
   let A' i j:= assay (shim P w (d i) j)
   have ha i j : Wages (A' i j):= pays_assay (k:=lustre j) _ (shored P w _ j)
   let R i:=charted (d i); have ht:0<t:= lt_of_lt_of_le (by positivity) v
   have hed i j: ‖d i j‖≤ T i*speck P^(j.val+1):= (heQ i).pay j
   rw [pluck_roller P X w p n n R hn (fun i=> Carrier.read_poly (d i)) (fun i=> by rw [← hxq]; exact (heQ i).rolled) heX q p' Y t' v, show (fun i=> _)= (fun i=>∑ j,A' i j) from funext fun i=> ledge P w (d i), gathers Y A' ha t' ht];
   let V (y:(i:Fin r)→Pane (n i)):= pluck Y (fun i=> A' i (y i))
   change ‖(∑ i,V i) (foldWord P w D (page D (testa D W.val)))‖≤ _; rw [observed,Embroider.emboss P w W h0, flower_hint,map_sum,_root_.sum_apply]; simp_rw [map_sum,map_smul,Finset.sum_mul]; apply (norm_sum_le ..).trans
   exact Finset.sum_le_sum fun i _=> (norm_sum_le ..).trans (Finset.sum_le_sum fun a _=> hu i a P w t A M Y d hed ht t' ev em et eqM)
lemma heritage_h (H:Hol G)(F:Frame G h)(h0:h<D)(u':ℝ)(hx:0<u')(hj:4≤j)(hl:4≤l)(hg:h≤ j)(p:Fin r→Place.Potential G)(n:Fin r→ℕ)(hn:∀ i,p i∈rangeLt _ (n i))(W:Embroider.Spiral h)(hp:(∑ i,n i)+W.val.card≤h)(e:h<u):
     ∃ C:ℝ,0≤C∧∀ (g:Flight j l)(P:Patch), P.L=g.L→ ∀ X: Carrier.Lines P.L, HEq X (linesOf g u')→∀ (Y:ChamberTen G (Vote D) r)(A t s Z M:ℝ), Twig 0 t A Y →0<s→dragCup Bank.terrain s Z (Agate P X G) → s/P.L.val≤t→Smooth Y→mural Y→VectorWind 0 1 u M Y→ Hears F h M Y →
      ‖pluck (hall P h (Agate P X G) Y) (assay ∘ p) (wallope W.val D)‖ ≤ (P.L.val:ℝ)^h*C*M:=by
    obtain ⟨C,H,h'⟩:= flight_p H F h0 u' hx hj hl hg p n hn W hp e
    refine ⟨C,H,fun g P hk X hX Y A t s Z M v hs u0 ha hY hv w hK=>?_⟩
    set η:=s/2; have he:0<η:=by unfold η; positivity
    rw [hall,tally_serve _ (fun w:Site P.L=> pulseS P w (Agate P X G) Y) (assay ∘ p) (fun i=>pays_assay _ (hn i)) _ (fun i _=>⟨η,_,he,pulse_fares P i (Agate P X G) u0 Y v ha he.le (by unfold η; linarith)⟩),_root_.smul_apply,_root_.sum_apply,norm_smul,Real.norm_eq_abs]; refine (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (Finset.sum_le_sum fun i _=> h' g P i hk X hX Y A t s Z M v hs u0 ha hY hv w hK)) (abs_nonneg _)).trans_eq ?_
    rw [tier_cash]; ring
lemma hall_near (r:ℕ)(H:Hol G)(F:Frame G h)(h0:h<D)(e:h<u)(u':ℝ)(hx:0<u')(hj:4≤j)(hl:4≤l)(hg:h≤ j)(W:Embroider.Spiral h)(p:a+W.val.card≤ h):
     ∃ C:ℝ,0≤C∧∀ (g:Flight j l)(P:Patch), P.L=g.L →∀ X: Carrier.Lines P.L, HEq X (linesOf g u')→∀ (Y:ChamberTen G (Vote D) r)(A t s Z M:ℝ), Twig 0 t A Y →0<s→dragCup Bank.terrain s Z (Agate P X G) → s/P.L.val≤t→Smooth Y→mural Y→VectorWind 0 1 u M Y→ Hears F h M Y →
     ‖Bell F a r (arret (wallope W.val D) (hall P h (Agate P X G) Y) h r)‖ ≤ (P.L.val:ℝ)^h*C*M:=by
    let I:= Wait h r a×(Fin r→ Cart G h); let U (i:I):= pearls i.1 i.2; let f (i:I) j:=sampled (U i j)
    let n(i:I)(j:Fin r):=(i.1.val j).val+2
    have hq (i:I)(j):f i j∈ rangeLt _ (n i j):= through_sample _ (pearls_tapped i.1 i.2 j)
    have he (i:I):(∑ j,n i j)=a:= i.1.property
    choose E hE H' using fun i:I=> heritage_h H F h0 u' hx hj hl hg (f i) (n i) (hq i) W (by rw [he i]; exact p) e
    let V:= ∑ i,E i; have hv:0≤V:= Finset.sum_nonneg fun _ _=> hE _
    obtain ⟨R,hR,hp⟩:=quarantine F a r
    refine ⟨R*V,by positivity,fun g P hk X hX Y A t s Z M v hs u0 ha hY hv' w hK=>?_⟩; let y':=hall P h (Agate P X G) Y; let T:=arret (wallope W.val D) y' h r; set C :=(P.L.val:ℝ)^h; have hM:=hK.fair; have hc:0≤ C:=by unfold C; positivity
    let θ:=s/2; have hθ:0<θ:=by unfold θ; positivity
    have hQ := hall_fares P _ u0 Y h v ha hθ.le (show θ<s from by unfold θ; linarith)
    have HH : ‖bagg G h r a T‖ ≤ C*V*M:=by
       refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun i=>?_); change ‖latent T (U i)‖≤_
       unfold T; rw [gems_pluck _ y' hQ hθ (hall_grace P (Agate P X G) Y h hY)]; change ‖pluck y' (assay∘ f i) (wallope W.val D)‖≤ _; exact (H' i g P hk X hX Y A t s Z M v hs u0 ha hY hv' w hK).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun i _=>hE i) (Finset.mem_univ _)) hc) hM)
    exact (hp T).trans ((mul_le_mul_of_nonneg_left HH hR).trans_eq (by unfold C; ring))
end YM.WilsonCoeffUV.Shard
