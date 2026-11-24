import YM.SchemeConversionRG11.FirstW.Ore.Text
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function MeasureTheory Filter Set Metric Topology Lattice Pert Align Laurent Position Deck SchemeConversionRG11
open scoped BigOperators Classical ContDiff
variable {G:Gauge}{T:Itinerary}{F:Labels.Frames G}{c:ℕ→Side}{Q:Wash}{R r:ℝ} {P:Age G} {W A B:ℕ→Field4 G}
lemma sep_m (v:Cover) {T : Itinerary}{R:ℝ} {x:ℕ}: Jam T R x v→ T.gap x * (size v:ℝ) ≤ 4*R := fun h=> (small_mark T x v).trans (mul_le_mul_of_nonneg_left h (by norm_num))
lemma savesZ (h:Messed T (4*R) 4 W): Scrip T R 6 5 W := by
 obtain ⟨C,hc,H⟩:=h
 let p:ℝ:= C*4^5; have hp:0<p:=by unfold p; positivity
 have he (x : Cover): 1+(size x:ℝ) ≤ 4*stepY x := by
   unfold stepY; linarith only [show (↑(size x):ℝ) ≤ 4*(yard x:ℝ) from by exact_mod_cast size_yard x]
 constructor
 · intro i; refine ⟨p,hp,H.mono fun j hi x hx=>?_⟩
   refine le_trans (hi i [] (by decide) x (sep_m _ hx)) ?_; rw [zpow_ofNat,zpow_ofNat]; rw [List.length_nil,Nat.sub_zero]; refine le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (he x) _) (by have h:=T.positive j; positivity)) ?_; unfold p; norm_num [mul_pow]; ring_nf; apply le_rfl
 · intro i a; refine ⟨C*4^4,by positivity,H.mono fun j hi x hx=>?_⟩; refine le_trans (hi i [a] (by simp) x (sep_m _ hx)) ?_
   rw [show (5:ℤ)-1=4 from rfl,zpow_ofNat,zpow_ofNat,show 4+1-[a].length=4 from rfl]; refine le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (he x) _) (by have h:=T.positive j; positivity)) ?_; apply le_of_eq; rw [mul_pow,show 4+2=6 from rfl]; ring
lemma mess_tapes (k:Labels.Key G)(h:R>0)(hp:Messed T R 4 W): Honey (fun i=> (T.gap i)^(-6:ℤ) * native k (0:Cover) (W i)):=by
 let p (i:ℕ):= (T.gap i)^(-6:ℤ) • W i; have he (x:Edge Cover): Honey (fun i=> p i x):= by
    obtain ⟨C,hc,H⟩:= Messed.known _ h hp x; simp only [p, Pi.smul_apply,zpow_neg,zpow_ofNat]; exact ⟨C,H⟩
 simpa only [p,map_smul,smul_eq_mul] using footprint p k he
lemma isoL (W:Nu G 0)(k:Labels.Key G): native k (0:Cover) W.val=0 := by
 have hw: quietly W.val:= by
   have h:= steady0 (boards 0 (by decide) W) (by rw [boards_val]; exact W.property); rw [boards_val] at h; exact h
 obtain ⟨u,h,e,H⟩:=primitive _ 0 (cabin_stor W.property) hw; rw [←e, letter_T]
lemma vec_pay (T:Itinerary)(i:ℕ)(f:Field4 G→ₗ[ℝ] ℝ)(P:Age G) : f (composeR T 4 P i)=∑ t∈Finset.range (4+1),T.gap i^(t+1)* f (P t i).val:=by
 rw [composeR,map_sum]; apply Finset.sum_congr rfl; intro a _; exact map_smul ..
lemma poly_tapes (k: Labels.Key G)(hp:∀ i≤4, Book (P i)): Helen (fun i=>T.gap i^(-2:ℤ) * native k (0:Cover) (composeR T 4 P i)) := by
 simp only [vec_pay,Finset.mul_sum]; apply collectH; intro i hi
 by_cases ht:i=0; · subst i; simp_rw [isoL]; exact ⟨0,by simp⟩
 have hV := hp _ (Finset.mem_range_succ_iff.mp hi) ((native k (0:Cover)).comp (cabin G i).subtype)
 obtain ⟨u,hu⟩:= hV; refine ⟨_,((T.cutoff.pow (i-1)).mul hu).congr fun j=>?_⟩; simp only [LinearMap.comp_apply,Submodule.subtype_apply]; rw [←mul_assoc,←zpow_natCast,←zpow_natCast,←zpow_add₀ (T.positive j).ne',show (-2:ℤ)+↑(i+1)=(↑(i-1:ℕ):ℤ) from by rw [Nat.cast_sub (by omega : 1 ≤ i)]; omega]
lemma lingering (W:ℕ→ Field4 G)(h:R>0)(hp:Messed T R 4 W)(k:Labels.Key G) : Tendsto (fun i=>T.gap i ^ (-2:ℤ) * native k (0:Cover) (W i)) atTop (𝓝 0) := by
 have he:= Honey.sink (g:=fun i=> T.gap i ^(4:ℕ)) (mess_tapes k h hp) (by simpa only [pow_succ, mul_zero,zero_mul] using T.cutoff.pow 4)
 apply he.congr; intro i; rw [smul_eq_mul, ←mul_assoc,←zpow_natCast,←zpow_add₀ (T.positive i).ne', show ((4:ℕ):ℤ)+ -6=-2 by decide]
lemma bodym (hc:MarkGrid T c)(x y:Who G 6)(ha:fee x=2)(hb:fee y=2){Q:Wash} (r:ℝ)(hQ:Q.rOut<r)
   (hp:Messed T (4*r) 4 W)(h: Deaf T ((closedBall 0 Q.rOut)\{0}: Set E4) (-1) W): Helen (fun i=>T.gap i ^(-4:ℤ)* sectorA (tin G (T.period i)) 1 0 (wheelS G T i Q) x y (W i)):=by
 have hx:=oneM_credits x y ha hb _ (savesZ hp) hQ
 obtain ⟨a,H⟩:=playRoof _ hc Q _ _ ha hb hx (by decide) h
 let q i:= T.gap i ^(-6:ℤ) • W i
 have ht:Honey (fun i=> echoAt 0 x.val (pit T y i) (q i)) := by
   refine stayB _ _ _ (Honey.tint T y) fun j=>?_; have h0:=lt_trans Q.rOut_pos hQ; obtain ⟨C,hc,H⟩:= Messed.known _ (by positivity :0<4*r) hp j; refine ⟨C,H.mono fun i hi=>?_⟩; change ‖q i j‖ ≤ _; simp only [q, Pi.smul_apply,zpow_neg,zpow_ofNat]; exact hi
 have hu:= ht.sink (g:=fun i=> (T.gap i)^(2:ℕ)) (by simpa only [show (0:ℝ)^2=0 by norm_num] using T.cutoff.pow 2)
 refine ⟨_,((H.const_mul 3).add (hu.const_mul 2)).congr fun i=>?_⟩; rw [sector_eq,echoLeg,one_pow,inv_one,one_smul];
 change 3*(T.gap i ^ (-4:ℤ)*_)+2*(T.gap i ^(2:ℕ)*_)=_
 unfold q; simp only [map_smul,smul_eq_mul]; unfold pit; have ht : T.gap i ^(2:ℕ)*T.gap i ^(-6:ℤ)=T.gap i ^(-4:ℤ):=by rw [←zpow_natCast,←zpow_add₀ (T.positive _).ne',show ↑(2:ℕ)+(-6:ℤ)=-4 by decide];
 rw [← mul_assoc (T.gap i ^(2:ℕ)),ht]; ring
lemma helic {U V:Type*} [AddCommGroup U][Module ℝ U] [FiniteDimensional ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V] (f:ℕ→ U→ₗ[ℝ] V) {p:ℕ→U}(h:∀ u,Helen (fun i=>f i u))(he:Book p): Helen (fun i=> f i (p i)):=by
 obtain ⟨I,q,r,H⟩:= Colorish U V p f
 simp_rw [H]; apply collectH; intro i _; obtain ⟨u,hu⟩:= he (q i); obtain ⟨v,hv⟩:= h (r i); exact ⟨_,hu.smul hv⟩
lemma focus {U:Type*}[AddCommGroup U][Module ℝ U][FiniteDimensional ℝ U](f:ℕ→ U→ₗ[ℝ]ℝ){p:ℕ→U} (h:∀ x,Tendsto (fun i=> f i x) atTop (𝓝 0)) (hp:Book p): Tendsto (fun i=> f i (p i)) atTop (𝓝 0):=by
 obtain ⟨I,g,b,H⟩:=Colorish U ℝ p f
 have hv(v:Fin I): Tendsto (fun i=>g v (p i) • f i (b v)) atTop (𝓝 0):= by obtain ⟨x,hx⟩:=hp (g v); simpa only [smul_zero] using hx.smul (h (b v))
 have hx:=tendsto_finsetSum Finset.univ (fun i _=> hv i); simp_rw [Finset.sum_const_zero] at hx; exact hx.congr fun i=>(H i).symm
lemma zero_poly (hc:MarkGrid T c)(x y:Who G 6)(ha:fee x=2)(hb:fee y=2){Q:Wash}(h:∀ i≤4,Book (P i)): Tendsto (fun i=>sectorA (tin G (T.period i)) 1 0 (wheelS G T i Q) x y (composeR T 4 P i)) atTop (𝓝 0) := by
 let J (i:ℕ):= sectorA (tin G (T.period i)) 1 0 (wheelS G T i Q) x y
 have hv (v:ℕ)(hv:v≤4): Tendsto (fun i=> T.gap i ^ (v+1) * J i (P v i).val) atTop (𝓝 0):=by
    let f(i:ℕ) := T.gap i • (J i ∘ₗ (cabin G v).subtype)
    by_cases he:v=0
    · have he1 :∀ u:Nu G v,Tendsto (fun i=> f i u) atTop (𝓝 0) := by
         intro w
         simp only [f,LinearMap.smul_apply,LinearMap.comp_apply,Submodule.subtype_apply,smul_eq_mul,J]; exact glow_small hc x y ha hb Q w.val (stepped (by omega:v≤3) w.property)
      have H:= focus f he1 (h _ hv); simp only [f,LinearMap.smul_apply,LinearMap.comp_apply,Submodule.subtype_apply,smul_eq_mul] at H; rw [show v+1=1 by omega]; simpa only [pow_one] using H
    obtain ⟨u,H⟩:= helic (U:=Nu G v) f (fun w=>by
       have H:= high_t hc Q x y ha hb (boards _ hv w); rw [boards_val] at H; simp only [f, LinearMap.smul_apply,LinearMap.comp_apply,Submodule.subtype_apply,smul_eq_mul,J]; exact H) (h _ hv)
    have hK:= (T.cutoff.pow v).mul H; rw [zero_pow he,zero_mul] at hK; exact hK.congr fun i=>by simp only [f,LinearMap.smul_apply,LinearMap.comp_apply,Submodule.subtype_apply,smul_eq_mul,pow_add,pow_one,mul_assoc]
 change Tendsto (fun i=> J i (composeR T 4 P i)) _ _; simp_rw [vec_pay]; simpa only [Finset.sum_const_zero] using tendsto_finsetSum (Finset.range (4+1)) (fun v h=> hv _ (Finset.mem_range_succ_iff.mp h))
end YM.RG11.FirstW
