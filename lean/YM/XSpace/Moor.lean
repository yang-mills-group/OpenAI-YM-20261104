import YM.XSpace.Nail

/-!
# Shell transcript: pay weighted layer times, contract at separated distance.

All on one *harmonic polynomial* input. α^−d actual factor and chosen
engineering multiplier on gauge parameter, producing exact first-order local
change on normalized inputs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Prelude
open MeasureTheory Filter Function Set Future Mu Drama Lows Lattice Sail Further.FreeCovariance.KP Playpen Trace Chart2 Scale JetGauge Next.Rank.Normal MvPolynomial
open scoped Topology BigOperators ContDiff
variable {G:Gauge} {ι:Type} {L:Filter ι}{k b d:ℕ}
variable (X:Litter.Stamp k G.Color)
def blast (a:ℝ): Warp G:= (a^k) • Litter.feed 0 X
lemma layer_fx (i b:G.ColorIndex)(q:Axis): ∃ f: G.Color×G.Color→L[ℝ] ℝ,∀ v:Warp G,∀ x:Cover, layer v x q i b=f (v (x+step q),v x):=by
  let p: G.Color×G.Color→ₗ[ℝ] G.Color:= (1/2:ℝ) • (LinearMap.fst ℝ G.Color G.Color+LinearMap.snd ℝ G.Color G.Color)
  let f: G.Color×G.Color→ₗ[ℝ] ℝ:= (EuclideanSpace.proj i).toLinearMap ∘ₗ G.ad (basisC G b) ∘ₗ p
  exact ⟨LinearMap.toContinuousLinearMap f,fun v x=> layered v x q i b⟩
lemma blast_cost (R:ℝ)(h:0≤R)(u:Cover):∃ C:ℝ,0≤C∧∀ a:ℝ,0≤a→∀ x:Cover, a*area x≤R→ ‖blast X a (x+u)‖≤C:=by
  obtain ⟨C,hC,H⟩:=Litter.pay (F:=G.Color) [] 0 k; set b:=area u; have hb:0≤b:=(included u).le; refine ⟨C*‖X‖*(R*b)^k,by positivity,fun a ha x hx=>?_⟩
  rw [blast,Pi.smul_apply,norm_smul,Real.norm_of_nonneg (pow_nonneg ha _)]; refine (mul_le_mul_of_nonneg_left (H (x+u) X) (pow_nonneg ha _)).trans ?_; set Y:=area (x+u); have hv:Y ≤ area x * b:=by
    have he:(reach (x+u):ℝ)≤(reach x:ℝ)+reach u:=by exact_mod_cast Sail.tree x u
    unfold Y b area; nlinarith [Nat.cast_nonneg (reach u) (α:=ℝ),Nat.cast_nonneg (reach x) (α:=ℝ)]
  calc
    _ = C*‖X‖*(a*Y)^k:= by change a^k*(C* ‖X‖* Y^(k-0))=_; rw [Nat.sub_zero,mul_pow]; ring
    _ ≤ _:= by gcongr _ * (?_^_); · positivity [included (x+u)]
               calc _ ≤ a*(area x*b):=mul_le_mul_of_nonneg_left hv ha
                    _ ≤ _:=by rw [← mul_assoc]; gcongr
lemma blast_layer (R:ℝ)(h:0≤R)(q:Axis)(i b:G.ColorIndex):∃ C:ℝ,0≤C∧∀ a:ℝ,0≤a→∀ x:Cover, a*area x ≤ R→‖layer (blast X a) x q i b‖ ≤ C:=by
  obtain ⟨f,hf⟩:=layer_fx i b q; obtain ⟨C,hC,H⟩:=blast_cost X R h (step q); obtain ⟨P,hP,Y⟩:=blast_cost X R h 0; simp_rw [add_zero] at Y; refine ⟨‖f‖*(C⊔P),mul_nonneg (norm_nonneg _) (hC.trans le_sup_left),fun a h x hh=>?_⟩
  rw [hf]; apply (f.le_opNorm _).trans; rw [Prod.norm_def]; refine mul_le_mul_of_nonneg_left (max_le (?_) (?_)) (norm_nonneg _); exact (H _ h _ hh).trans le_sup_left; exact (Y _ h _ hh).trans le_sup_right
lemma approach (q:Axis)(i b:G.ColorIndex){A:ι→ℝ}(h:Tendsto A L (𝓝 0)){x:ι→Cover}{z:E4}(he:Tendsto (fun i=> actual (A i) (x i)) L (𝓝 z)):
    Likely L fun j=>layer (blast X (A j)) (x j) q i b:=by
  have ht(v:Cover): Tendsto (fun j=> blast X (A j) (x j+v)) L (𝓝 (motifValue X z)):= by
    change Tendsto (fun j=> A j^k • Litter.board (rcast (x j+v)+0) X.val) _ _
    simp_rw [add_zero]; apply Litter.slopes (x:=fun i=>rcast (x i+v)) (v:=fun _=>X.val) tendsto_const_nhds _ h; simp_rw [Cross.rcast_add,smul_add]; simpa [actual] using he.add (h.smul_const (rcast v))
  obtain ⟨f,hf⟩:=layer_fx (G:=G) i b q; simp_rw [hf]; have h0:=ht 0; simp_rw [add_zero] at h0; exact ⟨_, f.continuous.continuousAt.tendsto.comp ((ht (step q)).prodMk_nhds h0)⟩

-- boundary is priced in books. cancel tadpoles (incl in shell) before pricing

def glaze (q r:Axis)(i b:G.ColorIndex)(x:Cover): Stamp G:= harp (curlFee (x-step q) q r i).line * MvPolynomial.X ((x,r),b)
lemma vent (q r:Axis)(i b:G.ColorIndex)(x:Cover): glaze q r i b x=Trace.volume x (glaze q r i b 0) :=by
  apply Chart2.same; intro A; rw [ting]; simp only [glaze,map_mul, leg_test,curls_hit]; simp only [pit,MvPolynomial.aeval_X,crackle_ap, numbers,zone_ap]; simp [sub_eq_add_neg,← add_assoc]
lemma winded (q r:Axis)(i b:G.ColorIndex): glaze q r i b 0∈ elemental G 3:=by
  unfold glaze; rw [← wall_entry (G:=G) ((0,r),b)]; apply productKeen (d:=2) (e:=1); exacts [ (read_cut _ (curlFee (0-step q) q r i) trivial), (read_cut _ (freeLeg (G:=G) ((0,r),b)) trivial)]
lemma whirs (q r:Axis)(i b:G.ColorIndex) (v:Warp G)(x:Cover): flicker ((layer v x r i b:ℂ) • glaze q r i b x)=(layer v x r i b:ℂ) • glaze q r i b x:=by
  by_cases h:b=i; simp only [h,layered,pebble_zero,Complex.ofReal_zero,zero_smul,map_zero]; rw [map_smul, show flicker (glaze _ _ _ _ _)=_ from (congr_arg flicker (price_arm x q r i h x)).symm.trans (gone _)]; rfl
lemma plume (v:Warp G)(p:Mark): flicker (shellK p v)= ∑ j:Axis,∑ q:Axis,∑ i:G.ColorIndex,∑ b:G.ColorIndex, send (sibling p q) (fun x=> (layer v x j i b:ℂ) • glaze q j i b x):=by
  have he x j i:pulseR v x j i=∑ b:G.ColorIndex,(layer v x j i b:ℂ) • MvPolynomial.X ((x,j),b) :=by
    apply same; intro A; rw [pulseR,leg_test,rollLine]; simp_rw [map_sum,LinearMap.sum_apply,map_smul, probes, LinearMap.smul_apply,smul_eq_mul,Complex.ofReal_sum,Complex.ofReal_mul,pit,MvPolynomial.aeval_X, ram_at]; rfl
  unfold shellK; simp_rw [map_sum,by_send,he,Finset.mul_sum,mul_smul_comm]; -- simplify whirs
  change _= _; conv_rhs=> arg 2; ext j; arg 2; ext i; arg 2; ext b; rw [send_many]; skip
  simp_rw [map_sum, show ∀ q j i b x,flicker ((layer v x j i b:ℂ) • (harp (curlFee (x-step q) q j i).line * MvPolynomial.X ((x,j),b)))=(layer v x j i b:ℂ) • glaze q j i b x from fun q j i b x=>whirs q j i b v x]

private lemma paper_price (q r:Axis)(i b:G.ColorIndex)(p: Stamp G) (h:p∈elemental G d): Book G (d+3) (fun x:Cover=> tie G p (glaze q r i b x)):=by
  conv => arg 3; ext x; rw [vent _ _ _ _ x]; skip
  exact earned h (winded q r i b)

private lemma hatch (b a m C D E:ℝ)(d:ℕ)(hb:0<b)(ha:0<a)(h:b≤a*m)(hc:0≤ C)(he:0≤E)(hd:0≤D) : a⁻¹^d*(C*a)*(D*(E*(m^(d+3))⁻¹)) -- typo E*(m..)^-1
    ≤ b⁻¹^d*C*D*E*a*(m^3)⁻¹:=by
  have hv:0<m:=by nlinarith
  have hh : (a*m)⁻¹^d ≤ b⁻¹^d:=by gcongr
  calc a⁻¹^d*(C*a)*(D*(E*(m^(d+3))⁻¹)) = C*a*D*E*(m^3)⁻¹*((a*m)⁻¹)^d:=by rw [pow_add,inv_pow,inv_pow]; field_simp; ring
       _ ≤ _:= (mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by ring)

variable {H:Source.Hol G}(σ:Survey G H d)(c:Shade.Cut)(B:Hat G d)(p:On.Grade G d){a:ι→ℝ}
variable [L.IsCountablyGenerated](S:Tendsto a L (𝓝 0))(h:∀ᶠ i in L,0<a i)
def lore (q r:Axis)(p:Stamp G)(i b:G.ColorIndex): Tile G:= fun x=> tie G p (glaze q r i b x)
def shore {M:ℕ} (p:Tile G)(Z:Hat G d)(q r:Axis)(X:Litter.Stamp M G.Color) (i b:G.ColorIndex)(v:ℝ)(x:Cover):ℂ:= (Shade.turn q c v x :ℂ)*↑(layer (blast X v) x r i b)*pit (scenic _ (orchestra d v Z)) (p x)
include S h in
theorem bought (q r:Axis)(i b:G.ColorIndex)(p:Tile G)(hp: Book G (d+3) p): Issued L (fun l x=> tick a l d*shore c p B q r X i b (a l) x):=by
  obtain ⟨t,T,C,e,ht,hT,hC,he,H⟩:= Shade.seam_fees q c; obtain ⟨D,hD,K⟩:= blast_layer X T (by linarith) r i b; obtain ⟨E,hE,W⟩:= across d p hp (norm_nonneg B) (show 0≤T by linarith); let f l (x:Cover):= tick a l d*shore c p B q r X i b (a l) x; set P:= t⁻¹^d*C*D*E; have hz:0≤P:=by unfold P; positivity
  apply speeds f h ((near_minor (4*T+1)).const_mul (P*64)) (close_pay P T f hz h ?_) ?_
  · filter_upwards [h,S.eventually (ge_mem_nhds he)] with l hl hh x hx; have hs : Shade.turn q c (a l) x≠0:=fun p=>hx (by unfold f shore; rw [p,zero_mul,zero_mul,mul_zero]); obtain ⟨hr,hv,y⟩:=H _ hl hh _ hs; refine ⟨hv,?_⟩; unfold f shore; simp only [norm_mul,tick,norm_pow,norm_inv,Complex.norm_real,Real.norm_of_nonneg hl.le]; have hm:= W B x _ le_rfl hl.le hv; rw [carry_cost] at hm;

    apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul y (K _ hl.le _ hv) (norm_nonneg _) (by positivity)) hm (norm_nonneg _) (by positivity)) (by positivity : 0≤(a l)⁻¹^d)); simpa only [P,mul_assoc] using hatch t (a l) (area x) C D E d ht hl hr hC hE hD
  filter_upwards [almost_all] with x hx; let z l:= mark (a l) x; have ht:= marks x S h; let A l:= scenic d (orchestra d (a l) B); have H:= swings (X:=A) (P:=p) S h ht hp hx (Drama.flare B S h ht) (by apply Drama.flare B S h (u:=0); simp [show rcast 0=0 from by ext i; simp [rcast], tendsto_const_nhds]
       ); have h := (show Likely L _ from ⟨_,Shade.saw q c S h ht⟩).mul (((approach X r i b S ht).cont Complex.continuous_ofReal).mul H); refine h.congr (Eventually.of_forall fun i=>?_); unfold Playpen.steps f shore tick; push_cast; ring
include S h
lemma post : Likely L fun l=> tick a l d * pit (scenic d (orchestra _ (a l) B)) (tie G (enter0 σ p) (flicker (shellK (Shade.outfit c (a l)) (blast X (a l))))):=by
  have he(q:Mark)(p:Cover→ℂ):Prelude.send q p=∑' i:Cover,q i*p i:=by rw [tsum_eq_sum (s:=q.support)]; exact sends q p; intro i hi; rw [Finsupp.notMem_support_iff.mp hi,zero_mul]
  simp_rw [plume,map_sum,Finset.mul_sum]; refine Likely.sum _ _ fun y _=>Likely.sum _ _ fun q _=>Likely.sum _ _ fun i _=>Likely.sum _ _ fun b _=>?_ ; let Q:=lore q y (enter0 σ p) i b
  refine (bought X c B S h q y i b Q (paper_price _ _ _ _ _ (good_read Stops d (status σ p)))).2.congr (Eventually.of_forall fun l=>?_)
  simp_rw [by_send,show ∀ (v:Contact G)(p:Mark)(f:Cover→Stamp G), pit v (Prelude.send p f)=Prelude.send p (fun x=>pit v (f x)) from fun v p f=>by_send (pit v).toLinearMap p f,map_smul,he,← tsum_mul_left]; unfold Q lore shore Shade.turn; simp [mul_assoc]

lemma canyon: Likely L fun l=> tick a l d *pit (scenic d (orchestra d (a l) B)) (part (G:=G) (grad (blast X (a l))) (fuse σ p c (a l))):=by
  apply (post X σ c B p S h).congr; filter_upwards [(show Tendsto a L (nhdsWithin 0 (Ioi 0)) from tendsto_nhdsWithin_iff.mpr ⟨S,h⟩).eventually (downs σ p c)] with i hi; rw [hi _ _ (scenes ..)]
end YM.XSpace.Prelude
