import YM.WilsonCoeffUV.Root.Gain.RootExtraction
/-! Polynomial pressure at engineering weight ≤ valve. The aperture of vertical. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n c:Side}{U V:Type*}{r h D l j e k:ℕ} {G:Gauge}{F:Labels.Frame G h}{s A X Z D':ℝ}

abbrev Leg G:= YForest G→ℝ
def assay (v:Place.Potential G): Leg G := fun i=> v (Place.seat i.1) (feather i).2 i.2.2
lemma assay_add (u v:Place.Potential G): assay (u+v)=assay u+assay v:=rfl
lemma assay_sub (u v:Place.Potential G): assay (u-v)=assay u-assay v:=rfl
lemma assay_mu (c:ℝ)(u:Place.Potential G): assay (c•u)=c•assay u:=rfl

def Wages (F:Leg G): Prop:= ∃ n:ℕ, ∃ C:ℝ,0≤C∧∀ x, ‖F x‖≤ C*liftCost n x.1
lemma pays_assay (f:Place.Potential G)(p:f∈rangeLt _ k) : Wages (assay f):=by
   obtain ⟨C,h,H⟩:= royalties k _ p; refine ⟨k,‖(coatC G).symm.toContinuousLinearMap‖*C,by positivity,fun x=>?_⟩
   let L:G.Color→L[ℝ] Lawn G.ColorIndex:= (coatC G).symm.toContinuousLinearMap
   let u:= feather x; let a:= verdict f x.1 u.2; exact le_trans (norm_le_pi_norm (L a) x.2.2) ((L.le_opNorm a).trans ((mul_le_mul_of_nonneg_left (H x.1 u.2) (norm_nonneg _)).trans_eq (by ring)))

def pressOn [SMul ℝ V] (P:ChamberTen G V r)(b:Fin r→Leg G)(y:Fin r→YForest G): V:= (∏ i,b i (y i)) • P y
def pluck [NormedAddCommGroup V][NormedSpace ℝ V](P:ChamberTen G V r)(b:Fin r→Leg G): V:= ∑' y, pressOn P b y
variable {P:ChamberTen G V r}{b:Fin r→Leg G}[NormedAddCommGroup V][NormedSpace ℝ V]
omit [NormedSpace ℝ V] in
lemma shelter (b:Fin r→Leg G)(h:∀ i,Wages (b i)): ∃ n:ℕ, ∃ C:ℝ, 0≤C∧ ∀ y, ‖∏ i,b i (y i)‖≤ C*(1+(port_d 0 y):ℝ)^n:=by
    choose n C hx ht using h; refine ⟨∑ i,n i,∏ i,C i,Finset.prod_nonneg fun _ _=> hx _,fun y=>?_⟩
    rw [norm_prod,←Finset.prod_pow_eq_pow_sum,←Finset.prod_mul_distrib]; refine Finset.prod_le_prod (fun _ _=> norm_nonneg _) fun i _=> (ht _ _).trans ?_
    apply mul_le_mul_of_nonneg_left _ (hx i); unfold liftCost; gcongr; exact port_size ..
lemma upon (b:Fin r→ Leg G)(p:∀ i,Wages (b i))(h0:0<s)(V:Type*)[NormedAddCommGroup V][NormedSpace ℝ V]: ∃ T:ℝ,0≤ T∧∀ (P:ChamberTen G V r)(A:ℝ), Twig 0 s A P→ SumBudget (fun y=> ‖pressOn P b y‖) (T*A):=by
   obtain ⟨n,C,h,H⟩:=shelter b p
   let Q:=ceilPoly n (s/2); let B:=tiePay (Hooks G) r (s/2); have he : 0≤ Q:= (ceilPoly_pos ..).le
   have hp:0≤ B:=by
      by_cases h:r=0; · simp [B,tiePay,h]
      exact pow_nonneg (boardPay_nn (by positivity)) r
   refine ⟨C*Q*B,by positivity,fun P A g=>?_⟩; have hx:= shrub V P g h0 n; simp only [zero_mul,Real.exp_zero,mul_one,sub_zero] at hx
   rw [show C*Q*B*A=C*((A*ceilPoly n (s/2))*tiePay (Hooks G) r (s/2)) by unfold Q B; ring]; apply budget_minor (cap_scale hx h) (fun _=>norm_nonneg _); intro y; rw [pressOn,norm_smul]; exact (mul_le_mul_of_nonneg_right (H y) (norm_nonneg _)).trans_eq (mul_assoc ..)
lemma pluck_profit (q:Twig 0 s A P)(e:0<s)(h:∀ i,Wages (b i)): Summable (fun y=> ‖pressOn P b y‖):=by
    obtain ⟨C,-,hv⟩:=upon b h e V; exact (hv _ _ q).2.1

lemma steady_lin (G:Gauge)(h:ℕ): ∃ L: Route G h→L[ℝ]G.Color, ∀ x,L x=steady x:=by
   let L:Route G h→ₗ[ℝ] G.Color := {
       toFun:= Place.steady
       map_add':=steady_add
       map_smul':=fun c x=>by
           unfold Place.steady; simp only [Pi.smul_apply,Finset.smul_sum,RingHom.id_apply]; exact Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=>smul_comm .. }
   exact ⟨L.toContinuousLinearMap,fun _=>rfl⟩
lemma through_sample (f:Snap G h)(p: throughSlot f k) : sampled f∈ rangeLt _ k:=by
   obtain ⟨L,hL⟩:= steady_lin G h
   refine vector_band (v:=fun i x=> sampled f x i) (fun i=>?_)
   have hx:= linear_band L k (rations f p i); simp_rw [hL] at hx; exact hx
lemma gems_pluck (f:Fin r→Snap G h)(P:ChamberTen G (Vote D) r)(p: Twig 0 s A P)(e:0<s)(g: Smooth P)(c:Volume D): latent (arret c P h r) f= pluck P (fun i=> grain (f i)) c:=by
   let F i:= grain (f i)
   rw [gemsRead p e g]; let L:=ContinuousLinearMap.apply ℝ ℝ c; change _= L (∑' y,pressOn P F y); have he i: Wages (F i):= pays_assay (k:=h+1) (sampled (f i)) (through_sample _ (fun i hi=>by omega))
   rw [L.map_tsum (pluck_profit p e he).of_norm]; exact tsum_congr fun y=> mul_comm ..
-- ¡tribunal diagonal→ echo values same weight and slots
structure Hears (F:Labels.Frame G h)(k:ℕ)(M:ℝ)(P:ChamberTen G (Vote D) r): Prop where
   fair : 0≤M
   tell i : weight F i≤k → valence F i=r → ‖echoS F P i‖≤ M

def wallope (w:Multiset Axis) (D:ℕ):= page D (testa D w)
lemma whistled (H:Hol G) (F:Labels.Frame G h)(w: Multiset Axis){a:ℕ}(g:k≤h)(hp:a+w.card≤k){M:ℝ}{P:ChamberTen G (Vote D) r}(z:Hears F k M P)(q:Twig 0 s A P)(hc:0<s)(u:mural P):
    ‖Bell F a r (arret (wallope w D) P _ _)‖≤M:=by
    let T:= arret (wallope w D) P h r; have he : seedTile T a ∈ _:= seed_paint H _ q hc u _ r (show a≤_ from by omega)
    refine (pi_norm_le_iff_of_nonneg z.fair).mpr fun i=>?_; by_cases H' : (a,r)=F.grades i; swap; · rw [show Bell _ _ _ _ _=0 from bell_coral F T a he i H',norm_zero]; exact z.fair
    let j: Alma F:= ⟨(i,⟨w,(show w.card≤_ from by omega)⟩),by change (F.grades i).1+w.card ≤ h; rw [←H']; exact hp.trans g⟩; have hx:weight F j≤k:=by unfold weight weave; rw [show sheet F j=i from rfl,←H']; exact hp
    have hq:valence F j=r:=congr_arg Prod.snd H'.symm
    rw [show Bell _ _ _ _ i=trellis F P j from ?_, trellis_real F H q hc u j,Complex.norm_real]; exact z.tell j hx hq
    unfold trellis; rw [show weave F j=a from congr_arg Prod.fst H'.symm,hq]; rfl

lemma summate {E:Type*}[NormedAddCommGroup E](C D:ℝ)(h:0≤C)(p:‖(0:E)‖≤D): 0≤C*D:=by rw [norm_zero] at p; positivity
lemma poly_pressural (H:Hol G)(F: Labels.Frame G h)(Y:Fin r→Snap G h)(n:Fin r→ℕ)(W:Multiset Axis)(e:k≤h)(hq:(∑ i,n i)+W.card≤k)(p:∀ i, throughSlot (Y i) (n i))(D:ℕ):
    ∃ C:ℝ, 0≤C∧ ∀ (s A M:ℝ) (P:ChamberTen G (Vote D) r), Hears F k M P→0<s→ Twig 0 s A P→mural P→Smooth P→ ‖pluck P (fun i=>assay (sampled (Y i))) (wallope W D)‖≤C*M:=by
    choose C hc hx using fun b:Fin r→Fin (h-1)=> shines F b Y
    refine ⟨∑ b,C b,Finset.sum_nonneg fun _ _=> hc _,fun s A M P z hs q u ht=>?_⟩
    let R:= arret (wallope W D) P h r; let T:=latent R
    have he : T Y=∑ b:Fin r→Fin (_-1), T fun i=> Pi.single (b i) (Y i (b i)) := by
       conv_lhs=>rw [show Y=(fun i=> ∑ j:Fin (_-1),Pi.single j (Y i j)) from funext fun i=> (Finset.univ_sum_single (Y i)).symm]
       exact T.map_sum (fun i j=>Pi.single j (Y i j))
    rw [show pluck P (fun i=>assay (sampled (Y i))) _=T Y from (gems_pluck Y P q hs ht (wallope W D)).symm,he,Finset.sum_mul]; refine (norm_sum_le ..).trans (Finset.sum_le_sum fun b hb=>?_)
    by_cases hp:∀ i:Fin r,(b i).val+2≤ n i
    · have he: Parts.rate b+W.card≤ k:= (Nat.add_le_add_right (Finset.sum_le_sum (fun i _=>hp i)) W.card).trans hq
      exact (hx b R (arret_seal _ P h r q hs) (seed_paint H _ q hs u _ r (show Parts.rate b≤ _ from by omega))).trans (mul_le_mul_of_nonneg_left (whistled H F W e he z q hs u) (hc b))
    push Not at hp; obtain ⟨i,hi⟩:=hp
    let x (i:Fin r):= (Pi.single (b i) (Y i (b i)): Snap G _)
    have he : x i=0:=by unfold x; rw [p i _ hi,Pi.single_zero];
    change ‖T x‖≤ _; rw [T.map_coord_zero i he,norm_zero]; exact mul_nonneg (hc _) z.fair
end YM.WilsonCoeffUV.Cosmos
