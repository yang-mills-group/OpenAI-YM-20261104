import YM.WilsonCoeffUV.Root.Gain.SlotDiagonal
/-!
# Slot-diagonal across threshold family. Γ insertions and ratio haven't happened HERE. Full block lift. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n c:Side}{U V:Type*}{r h D l j e k a m:ℕ} {G:Gauge}{F:Labels.Frame G h}{s t t' A X B C δ:ℝ}

def tiara (P:Patch)(k:ℕ):ℝ:= ((P.L.val:ℝ)^k/(P.L.val:ℝ)^4)
lemma tier_nn (P:Patch)(k:ℕ): 0≤tiara P k:=by unfold tiara; positivity
lemma tier_out (P:Patch): (Fintype.card (Site P.L):ℝ)= (P.L.val:ℝ)^4:=by exact_mod_cast (site_card P.L)
lemma tier_cash (P:Patch)(h:ℕ)(T:ℝ): |tiara P h| * ∑ _ : Site P.L,T= (P.L.val:ℝ)^h*T:=by
    rw [abs_of_nonneg (tier_nn ..),Finset.sum_const,Finset.card_univ,nsmul_eq_mul,tier_out]; unfold tiara; field_simp

def hall (P:Patch)(k:ℕ)(Q:Drip P G)(Y:ChamberTen G (Vote D) r): ChamberTen G (Vote D) r:= tiara P k • ∑ w:Site P.L,pulseS P w Q Y
lemma pulse_fares (P:Patch)(w:Site P.L)(Q:Drip P G)(g:dragCup Bank.terrain s B Q)(Y:ChamberTen G (Vote D) r)(p:Twig 0 t A Y)(hp:s/P.L.val≤ t)(he:0≤t')(hs:t'<s): Twig 0 t' ((B^r*(A*Real.exp (8*s)))*tiePay (Co P.L (Hooks G)) r (s-t')) (pulseS P w Q Y):=
    pumpFace (((Cork.turn (lift w) p).touch (soprano P w D)).cost (mul_le_of_le_one_left p.1 (budgetS ..))) (fun _=>g) hp he hs
lemma finite_pot {S:Finset U}{F:U→ChamberTen G V r}{M:U→ℝ}[NormedAddCommGroup V](h:∀ i∈S,Twig 0 s (M i) (F i)): Twig 0 s (∑ i∈S,M i) (∑ i∈S,F i) := Cork.sum h
lemma hall_fares (P:Patch)(Q:Drip P G)(g:dragCup Bank.terrain s B Q)(Y:ChamberTen G (Vote D) r)(k)(p:Twig 0 t A Y)(hp:s/P.L.val≤ t)(he:0≤t')(hs:t'<s): Twig 0 t' ((P.L.val:ℝ)^k*((B^r*(A*Real.exp (8*s)))*tiePay (Co P.L (Hooks G)) r (s-t'))) (hall P k Q Y):= by rw [← tier_cash]; exact Cork.μ (Cork.sum (fun i _=> pulse_fares P i Q g Y p hp he hs)) _
lemma hall_pay (F:Labels.Frame G h)(H:Hol G) (r:ℕ)(e:h<D)(C:ℝ)(hs:0<s)(ht:0<t):
    ∃ T:ℝ,0≤ T∧∀ (P:Patch)(Q:Drip P G)(Y:ChamberTen G (Vote D) r)(A M:ℝ), Crank Q (h+1) s C→ r *(s/P.L.val)≤t/2 → Smooth Y→ mural Y→ Twig 0 t A Y→ Wing 0 t M Y→ Hears F h M Y →
       Twig 0 s (T/(P.L.val:ℝ)* A+(P.L.val:ℝ)^h*T*M) (hall P h Q Y):=by
   obtain ⟨T,hT,h'⟩:=pulse_pay F H r e C hs ht
   refine ⟨T,hT,fun P Q Y A M g p a v q e z=>?_⟩
   have hx : ((P.L.val:ℝ)^h)*(T*(A*speck P^(h+1)+M))=T/(P.L.val:ℝ)*A+(P.L.val:ℝ)^h*T*M:=by unfold speck; rw [pow_succ (P.L.val:ℝ)⁻¹,inv_pow]; field_simp
   rw [←hx,←tier_cash]; exact Cork.μ (Cork.sum (fun i _=> h' P i Q Y A M g p a v q e z)) _
lemma tally_serve {V:Type*}[NormedAddCommGroup V][NormedSpace ℝ V][CompleteSpace V](c: ℝ)(Q:U→ChamberTen G V r)(h:Fin r→Leg G)(g:∀ i,Wages (h i))(S:Finset U)(p:∀ i∈ S,∃ t A:ℝ,0<t∧Twig 0 t A (Q i)) : pluck (c • ∑ i∈ S,Q i) h=c • ∑ i∈ S,pluck (Q i) h:=by
    have hx i (hi:i∈ S): Summable fun y=>pressOn (Q i) h y:= by obtain ⟨t,A,h,h'⟩:=p i hi; exact (pluck_profit h' h g).of_norm
    unfold pluck; rw [←Summable.tsum_finsetSum hx,←tsum_const_smul'']; apply tsum_congr; intro y; simp only [pressOn,Pi.smul_apply,Finset.sum_apply,Finset.smul_sum]; exact Finset.sum_congr rfl fun i _=>smul_comm ..
lemma lux (P:Patch){a b:ℕ}(h:b≤a): (P.L.val:ℝ)^a*speck P^b=(P.L.val:ℝ)^(a-b):=by unfold speck; rw [inv_pow]; field_simp; rw [← pow_add,show b+(a-b)=a from by omega]

-- either side not exact `spin` UNTIL aggregate. Inputs filtered by Slate.
variable {P:Patch}{K:Carrier.Lines P.L}{g:Flight j l}
lemma hall_top {Y:ChamberTen G (Vote D) r}(H:Hol G)(F: Labels.Frame G h)(hq:P.L=g.L)(p:HEq K (linesOf g C))(hc:0<C)(hv:4≤l)(hm:h≤j)(h0:h<D)(hg:Twig 0 t A Y)(hq':Wing 0 t 0 Y)(u:Slate Y F k) (pp:k≤h)(Yp:mural Y)(yp:Smooth Y)(τ:dragCup Bank.terrain s B (Agate P K G))(δ:0<s)(α:s/P.L.val≤t)(hs: Smooth (hall P h (Agate P K G) Y))(ht:mural (hall P h (Agate P K G) Y))(w:Embroider.Spiral h)(z:a+w.val.card≤ k):
    let c:=(P.L.val:ℝ)^(h-(a+w.val.card)); let X:=wallope w.val D
    Bell F a r (arret X (hall P h (Agate P K G) Y) h r)= c • Bell F a r (arret X Y h r):=by
   intro c X; let δ':=s/2; have hv':0<δ':=by unfold δ'; positivity
   let b:=hall P h (Agate P K G) Y; let T:=arret X b h r; let U:=arret X Y h r
   have hh:= hall_fares P _ τ _ h hg α hv'.le (show δ'<s from by unfold δ'; linarith)
   have hx:= lt_of_lt_of_le (div_pos δ (by positivity)) α
   have he:a≤ h:= by omega
   have hX : Tensor.Sym (T-c • U):=fun x t=> congr_arg₂ (·-·) (arret_seal X b h r hh hv' x t) (congr_arg (c • ·) (arret_seal X Y h r hg hx x t))
   have hU : seedTile (T-c • U) a ∈ localFields G h:= by rw [sub_eq_add_neg,← neg_smul,seeding_sum,seeding_scale]; exact Submodule.add_mem _ (seed_paint H X hh hv' ht h r he) (Submodule.smul_mem _ _ (seed_paint H X hg hx Yp _ _ he))
   change Bell F a r T=_; apply sub_eq_zero.mp; rw [← map_smul,← map_sub,bell_floor F (T-c • U) hX hU]; funext ⟨Z,r'⟩
   let A': Fin r→Snap G h:= pearls Z r'; let M:=Z.val; let f:= fun i=>sampled (A' i); let n i:= (M i).val+2
   have ha: (∑ i,n i)=a:= Z.property
   have hB i: f i∈ rangeLt _ (n i):= through_sample _ (pearls_tapped Z r' i)
   let A0:= Agate P K G
   have hg' (w':Site P.L): pluck (pulseS P w' A0 Y) (assay ∘ f) X = speck P^(a+w.val.card) • pluck Y (assay ∘ f) X:=by
       rw [←ha]; exact harbour P g hq.symm K C hc p w' hv hm Y hg f n hB (fun i=>by unfold n; omega) hq' u Yp yp pp H τ δ α w h0 (ha.symm ▸ z)
   change latent T A'- c • latent U A'=0; unfold T U; rw [gems_pluck A' _ hh hv' hs, gems_pluck A' _ hg hx yp]
   let N:= pluck Y (assay ∘ f) X
   change pluck b (assay ∘ f) X - c • N=0; change pluck (tiara P h • ∑ w:Site P.L,pulseS P w A0 Y) (assay ∘ f) X - c • N=0; rw [sub_eq_zero, tally_serve _ (fun w:Site P.L=> pulseS P w A0 Y) (assay ∘ f) (fun i=>pays_assay (f i) (hB i)) _ (fun i _=>⟨δ',_,hv',pulse_fares P i A0 τ Y hg α hv'.le (by unfold δ'; linarith)⟩),_root_.smul_apply,_root_.sum_apply]
   simp_rw [hg', smul_eq_mul]; rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; change tiara P h * ((Fintype.card (Site P.L):ℝ)*(speck P^(a+w.val.card)*N))=c*N
   rw [show tiara P h * ((Fintype.card (Site P.L):ℝ)*(speck P^(a+w.val.card)*N))= (P.L.val:ℝ)^h*speck P^(a+w.val.card)*N from ?_,lux P (z.trans pp)];
   rw [tier_out]; unfold tiara; field_simp
lemma hall_pluck (H:Hol G)(F:Frame G h)(h0:h<D)(e:k≤h)(u:ℝ)(hx:0<u)(hj:4≤j)(hl:4≤l)(hg:h≤ j)(p:Fin r→Place.Potential G)(n:Fin r→ℕ)(hn:∀ i,p i∈rangeLt _ (n i))(W:Embroider.Spiral h)(hp:(∑ i,n i)+W.val.card≤h)(t:ℝ)(ht:0<t):
     ∃ C:ℝ,0≤C∧∀ (g:Flight j l)(P:Patch), P.L=g.L→ ∀ X: Carrier.Lines P.L, HEq X (linesOf g u)→∀ (Y:ChamberTen G (Vote D) r)(A s Z M:ℝ), Twig 0 t A Y →0<s→dragCup Bank.terrain s Z (Agate P X G) → s/P.L.val≤t→Smooth Y→mural Y→Wing 0 t M Y→(0<k→Wing 0 t 0 Y)→ Slate Y F k→ Hears F h M Y →
      ‖pluck (hall P h (Agate P X G) Y) (assay ∘ p) (wallope W.val D)‖ ≤ (P.L.val:ℝ)^(h-k)*C*M:=by
    obtain ⟨C,H,h'⟩:= flight_cap H F h0 e u hx hj hl hg p n hn W hp t ht
    refine ⟨C,H,fun g P hk X hX Y A s Z M v hs u0 ha hY hv w κ k0 hK=>?_⟩
    set η:=s/2; have he:0<η:=by unfold η; positivity
    rw [hall,tally_serve _ (fun w:Site P.L=> pulseS P w (Agate P X G) Y) (assay ∘ p) (fun i=>pays_assay _ (hn i)) _ (fun i _=>⟨η,_,he,pulse_fares P i (Agate P X G) u0 Y v ha he.le (by unfold η; linarith)⟩),_root_.smul_apply,_root_.sum_apply,norm_smul,Real.norm_eq_abs]; refine (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (Finset.sum_le_sum fun i _=> h' g P i hk X hX Y A s Z M v hs u0 ha hY hv w κ k0 hK)) (abs_nonneg _)).trans_eq ?_
    rw [tier_cash,←lux P e]; ring
lemma hall_dear (r:ℕ)(H:Hol G)(F:Frame G h)(h0:h<D)(e:k≤h)(u:ℝ)(hx:0<u)(hj:4≤j)(hl:4≤l)(hg:h≤ j)(W:Embroider.Spiral h)(p:a+W.val.card≤ h)(t:ℝ)(ht:0<t):
     ∃ C:ℝ,0≤C∧∀ (g:Flight j l)(P:Patch), P.L=g.L →∀ X: Carrier.Lines P.L, HEq X (linesOf g u)→∀ (Y:ChamberTen G (Vote D) r)(A s Z M:ℝ), Twig 0 t A Y →0<s→dragCup Bank.terrain s Z (Agate P X G) → s/P.L.val≤t→Smooth Y→mural Y→Wing 0 t M Y→(0<k→Wing 0 t 0 Y)→ Slate Y F k→ Hears F h M Y →
      ∀ y':ChamberTen G (Vote D) r, y'=hall P h (Agate P X G) Y → Smooth y' → ‖Bell F a r (arret (wallope W.val D) y' h r)‖ ≤ (P.L.val:ℝ)^(h-k)*C*M:=by
    let I:= Wait h r a×(Fin r→ Cart G h); let U (i:I):= pearls i.1 i.2; let f (i:I) j:=sampled (U i j)
    let n(i:I)(j:Fin r):=(i.1.val j).val+2
    have hq (i:I)(j):f i j∈ rangeLt _ (n i j):= through_sample _ (pearls_tapped i.1 i.2 j)
    have he (i:I):(∑ j,n i j)=a:= i.1.property
    choose E hE H' using fun i:I=> hall_pluck H F h0 e u hx hj hl hg (f i) (n i) (hq i) W (by rw [he i]; exact p) t ht
    let V:= ∑ i,E i; have hv:0≤V:= Finset.sum_nonneg fun _ _=> hE _
    obtain ⟨R,hR,hp⟩:=quarantine F a r
    refine ⟨R*V,by positivity,fun g P hk X hX Y A s Z M v hs u0 ha hY hv' w κ k0 hK y' ht p'=>?_⟩; let T:=arret (wallope W.val D) y' h r; set C :=(P.L.val:ℝ)^(h-k); have hM:=hK.fair; have hc:0≤ C:=by unfold C; positivity
    let θ:=s/2; have hθ:0<θ:=by unfold θ; positivity
    have hQ : Twig 0 θ _ y':= ht.symm ▸ hall_fares P _ u0 Y h v ha hθ.le (show θ<s from by unfold θ; linarith)
    have HH : ‖bagg G h r a T‖ ≤ C*V*M:=by
       refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun i=>?_); change ‖latent T (U i)‖≤_
       unfold T; rw [gems_pluck _ y' hQ hθ p']; change ‖pluck y' (assay∘ f i) (wallope W.val D)‖≤ _; rw [ht]; exact (H' i g P hk X hX Y A s Z M v hs u0 ha hY hv' w κ k0 hK).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun i _=>hE i) (Finset.mem_univ _)) hc) hM)
    exact (hp T).trans ((mul_le_mul_of_nonneg_left HH hR).trans_eq (by unfold C; ring))
end YM.WilsonCoeffUV.Cosmos
