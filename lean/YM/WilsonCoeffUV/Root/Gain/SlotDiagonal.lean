import YM.WilsonCoeffUV.Root.Gain.Jet
/-! # And priced interslot trim. Cue and grade audited. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n c:Side}{U V:Type*}{r h D l j e k a m:ℕ} {G:Gauge}{F:Labels.Frame G h}{s t A X B C δ:ℝ}

abbrev Pane (n:ℕ):= Sigma (fun j:Fin n=>Place.Slices j.val)
def shim (P:Patch)(w:Site P.L)(Y: Prism G.Color k)(i: Pane k): Place.Potential G:= fun x=> Place.forSlice (Y i.1) i.2 x (Place.seat (lift w))
def lustre (i:Pane k):= Place.home i.2+1
lemma lustre_cap (i:Pane k): lustre i≤ k:=by unfold lustre; have hx:=Place.covers i.2; have hc:=i.1.isLt; omega
lemma ledge (P:Patch)(w:Site P.L)(Y: Prism G.Color k): assay (nativ P w (charted Y))= ∑ i:Pane k, assay (shim P w Y i):=by
   let L:Place.Potential G→ₗ[ℝ]Leg G:= { toFun:=assay,
                                          map_add':=assay_add,
                                          map_smul':=assay_mu }
   change L _=∑ i,L (shim P w Y i); rw [←map_sum]; apply congr_arg L; funext x
   rw [Fintype.sum_sigma]; simp only [nativ,charted,Finset.sum_apply]; exact Finset.sum_congr rfl (fun i _=> by simpa [shim] using Place.slice_diagonal (Y i) x (Place.seat (lift w)) 1)
lemma shored (P:Patch)(w:Site P.L)(Y: Prism G.Color k)(i: Pane k): shim P w Y i∈ rangeLt _ (lustre i):= Place.exact_le_band (Nat.lt_succ_self _) (Place.forSlice_home (Y i.1) i.2 (Place.seat (lift w)))
lemma shim_money (G:Gauge)(i:Pane k) : ∃ C:ℝ,0≤C∧∀ (P:Patch)(w:Site P.L)(D:ℝ)(Y: Prism G.Color k), 0≤D→ (∀ j, ‖Y j‖≤ D*speck P^(j.val+1))→slideRank (lustre i) (shim P w Y i)≤ C*D*speck P^(lustre i):=by
   classical
   let V := Place.home i.2; let v:= Place.away i.2
   let K:=Zest G (lustre i); let T:= ∑ u∈K,‖u‖^V; have hT:0≤T:= Finset.sum_nonneg fun _ _=> by positivity
   refine ⟨T*4^v,by positivity,fun P w D Y h H=>?_⟩; let y:=lift w; let L :ℝ:=P.L.val; let S:=speck P; have hh:=speck_pos P
   apply slidek _ _ (by positivity); intro x hx
   have he : ∏ a:Fin i.1.val, ‖(if i.2 a then Place.seat y else x)‖=‖x‖^V*‖Place.seat y‖^v:=by
       unfold V v Place.home Place.away; rw [←Finset.prod_pow_eq_pow_sum, ←Finset.prod_pow_eq_pow_sum,←Finset.prod_mul_distrib]; exact Finset.prod_congr rfl (fun j _=>by split<;> simp [*])
   have hv:= Bank.crowd w; have ht : ‖Place.seat y‖≤ 4*L:= (shade_seat _).trans (by unfold y L; exact_mod_cast hv)
   refine ((Y i.1).le_opNorm (fun a=>if i.2 a then Place.seat y else x)).trans ?_; change _ * (∏ a,_)≤_; rw [he]; apply (mul_le_mul (H i.1) (mul_le_mul (Finset.single_le_sum (f:=(‖·‖^V)) (fun i _=>by positivity) hx) (pow_le_pow_left₀ (norm_nonneg _) ht _) (by positivity) hT) (by positivity) (by positivity)).trans_eq
   change D*S^(i.1.val+1)*(T*(4*L)^v)=T*4^v*D*S^(lustre i)
   have hp:i.1.val+1=v+lustre i:=by unfold v lustre; rw [← add_assoc,Place.covers]
   rw [hp,pow_add,mul_pow]; unfold S speck; change D*(L⁻¹ ^v* L⁻¹ ^_ )*(T*(4^v*L^v))=_
   have hz:0<L:=by unfold L; positivity
   rw [show D*(L⁻¹ ^v* L⁻¹ ^(lustre i))*(T*(4^v * L^v))= (L⁻¹^v*L^v)*(T*4^v*D*L⁻¹^(lustre i)) by ring,← mul_pow, inv_mul_cancel₀ hz.ne']; simp [L]

-- augment slate to suture for any relevant grade with curve. Exact lower.
lemma glaze (H:Hol G)(F: Frame G h)(e:h<D)(p:k≤h)(n:Fin r→ℕ)(v: Fin r→ℝ)(hv:∀ i,0≤ v i) (W:Embroider.Spiral h)(hW: (∑ i,n i)+W.val.card≤h)(y: (i:Fin r)→Pane (n i))(u:Embroider.Spiral W.val.card)(ha:0<t):
    ∃ C:ℝ, 0≤ C∧ ∀ (P:Patch)(w:Site P.L)(A M:ℝ)(Y:ChamberTen G (Vote D) r)(c: (i:Fin r)→ Prism G.Color (n i)), (∀ i j, ‖c i j‖≤ v i*speck P^(j.val+1))→ Twig 0 t A Y→Smooth Y→mural Y→Wing 0 t M Y→(0<k→Wing 0 t 0 Y)→ Slate Y F k → Hears F h M Y →
      ‖(halo P w u.val (testa D W.val)) • pluck Y (fun i=> assay (shim P w (c i) (y i))) (wallope u.val D)‖≤ C*M*speck P^k:=by
   let m i:=lustre (y i); let L:= ∑ i,m i; let b:=u.val.card
   have he:L+b≤h:= (Nat.add_le_add (Finset.sum_le_sum (fun i _=>lustre_cap _|>.trans (show n i≤ n i from le_rfl))) u.property).trans hW
   by_cases h0:L+b<k
   · refine ⟨0,le_rfl,fun P w A M Y c θ t pY v τ β tK eK=>?_⟩
     rw [show pluck Y (fun i=> assay (shim P w (c i) (y i))) _=0 from bare H F Y t ha v pY p (β (by omega)) tK (fun i=>shim P w (c i) (y i)) m (fun i=> shored P w (c i) (y i)) u.val h0,smul_zero,norm_zero,zero_mul,zero_mul]
   obtain ⟨T,hT,hg⟩:= laurels H F m u.val he le_rfl D ha
   choose C hc H using fun i=> shim_money G (y i)
   let V:= ∏ i,C i*v i; have hV :0≤ V:= Finset.prod_nonneg fun _ _=> mul_nonneg (hc _) (hv _)
   let X:= ‖wallope W.val D‖; have hx:0≤X:=norm_nonneg _
   refine ⟨T*V*X,by positivity, fun P w A M Y c θ t0 pY g u' _ S R=>?_⟩
   set Q:= speck P; have hp:0<Q:= speck_pos _; have heM:=R.fair
   let F i:= shim P w (c i) (y i); let N:= ∏ i,slideRank (m i) (F i)
   have hu: ‖pluck Y (assay ∘ F) (wallope u.val D)‖≤T*M*N:= hg Y A M t0 g pY R u' F (fun i=>shored P w (c i) (y i))
   have hh: N ≤ V*Q^L:= (Finset.prod_le_prod (s:= Finset.univ) (fun i _=> slide_nn (m i) (F i)) (fun i _=> H i P w (v i) (c i) (hv i) (θ i))).trans_eq (by rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum])
   rw [norm_smul]; refine (mul_le_mul (halo_bound P w _ u.val (le_trans u.property (W.property.trans e.le))) (hu.trans (mul_le_mul_of_nonneg_left hh (by positivity))) (norm_nonneg _) (by positivity [speck_pos P])).trans ?_
   change Q^b*X*(T*M*(V*Q^L))≤ _; rw [show Q^b*X*(T*M*(V*Q^L))= T*V*X*M*Q^(L+b) by ring]; apply mul_le_mul_of_nonneg_left _ (by positivity); exact pow_le_pow_of_le_one hp.le (speck_le P) (le_of_not_gt h0)

lemma flight_cap (H:Hol G)(F: Frame G h)(h0:h<D)(e:k≤h)(u:ℝ)(hx:0<u)(hj:4≤j)(hl:4≤l)(hg:h≤j)(p:Fin r→ Place.Potential G)(n:Fin r→ℕ)(hn:∀ i,p i ∈ rangeLt _ (n i))(W:Embroider.Spiral h)(hp:(∑ i,n i)+W.val.card≤h)(t:ℝ)(ht:0<t): ∃ C:ℝ,0≤ C∧∀ (g:Flight j l)(P:Patch)(w:Site P.L)(_hk:P.L=g.L)(X: Carrier.Lines P.L), HEq X (linesOf g u)→∀ (Y:ChamberTen G (Vote D) r)(A s Z M:ℝ), Twig 0 t A Y →0<s→dragCup Bank.terrain s Z (Agate P X G)→s/P.L.val≤t→Smooth Y→mural Y→Wing 0 t M Y→(0<k→Wing 0 t 0 Y)→ Slate Y F k→ Hears F h M Y →
      ‖pluck (pulseS P w (Agate P X G) Y) (assay ∘ p) (wallope W.val D)‖≤ C*M*speck P^k:=by
   have hv i:n i≤ j:= (Finset.single_le_sum (f:=n) (fun _ _=> Nat.zero_le _) (Finset.mem_univ i)).trans ((Nat.le_add_right _ _).trans (hp.trans hg))
   choose b hb hxq using fun i=>Carrier.analyze (p i) (hn i)
   choose C hc h using fun i=> Carrier.deliver (E:=G.Color) u hx hj hl (n i) (hv i)
   let T i:= C i*Carrier.pile (b i); have hT i:0≤ T i:= mul_nonneg (zero_le_one.trans (hc _)) (Carrier.pile_pos _)
   choose B hB hu using fun (y:(i:Fin r)→Pane (n i))(u:Embroider.Spiral W.val.card)=> glaze H F h0 e n T hT W hp y u ht
   refine ⟨∑ y,∑ u,B y u,Finset.sum_nonneg fun _ _=> Finset.sum_nonneg fun _ _=> hB _ _,fun g P w hk X hz Y A s Z M t' p' q v ev em et κ eS eqM=>?_⟩
   choose d hd using fun i=> h i g (b i)
   have he' (L:Side)(X:Carrier.Lines L)(e:L=g.L)(p:HEq X (linesOf g u)): Whole X∧∀ i,Carrier.Reel X (b i) (d i) (C i):= by
       subst L; rw [eq_of_heq p]; exact ⟨stored g u hx hl,hd⟩
   obtain ⟨heX,heQ⟩:=he' P.L X hk hz
   let A' i j:= assay (shim P w (d i) j)
   have ha i j : Wages (A' i j):= pays_assay (k:=lustre j) _ (shored P w _ j)
   let R i:=charted (d i)
   have hed i j: ‖d i j‖≤ T i*speck P^(j.val+1):= (heQ i).pay j
   rw [pluck_roller P X w p n n R hn (fun i=> Carrier.read_poly (d i)) (fun i=> by rw [← hxq]; exact (heQ i).rolled) heX q p' Y t' v, show (fun i=> _)= (fun i=>∑ j,A' i j) from funext fun i=> ledge P w (d i), gathers Y A' ha t' ht];
   let V (y:(i:Fin r)→Pane (n i)):= pluck Y (fun i=> A' i (y i))
   change ‖(∑ i,V i) (foldWord P w D (page D (testa D W.val)))‖≤ _; rw [observed,Embroider.emboss P w W h0, flower_hint,map_sum,_root_.sum_apply]; simp_rw [map_sum,map_smul,Finset.sum_mul]; apply (norm_sum_le ..).trans
   exact Finset.sum_le_sum fun i _=> (norm_sum_le ..).trans (Finset.sum_le_sum fun a _=> hu i a P w A M Y d hed t' ev em et κ eS eqM)
end YM.WilsonCoeffUV.Cosmos
