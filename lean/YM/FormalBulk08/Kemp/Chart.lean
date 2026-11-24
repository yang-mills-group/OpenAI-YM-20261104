import YM.FormalBulk08.Kemp.Staff

/-! Reexpression at fixed marks. Give semilinearity via actual powerseries
substitution, including arbitrary marked lead. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Kemp
open Reef Lava Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 PowerSeries Bank
open Stationary Lotus Shore Mesa Gorge City Cork Rift Next.Free Flat RG Precision Tree Wine
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G : Gauge} {I J: Type} {η θ A B : ℝ} {l i u j t r D d : ℕ}{K: KernelChoices}{Y T:Anthem D G}{a: Loc G 1} {H U:Pence}{s: Signed}

def stir (H U:Pence)(Z: Anthem D G) : Anthem D G:=fun p=>stamp H U (Z p)
lemma stir_add (H U:Pence)(Y T: Anthem D G) : stir H U (Y+T)= stir H U Y+stir H U T:= by funext p e r v; simp [stir,stamp,Finset.sum_add_distrib]
lemma Wade.stirs (H U:Pence)(h:Wade a Y l): Wade a (stir H U Y) l:= by
    refine ⟨fun p e r he=> ?_,fun p e r=>Agate.sums (Finset.range (e+1)) (fun i _=>(h.2.1 p i r).smul (bill H U e i r)),fun e r=>?_⟩
    · by_contra hp; apply he; unfold stir stamp; refine Finset.sum_eq_zero fun i hi=> ?_; suffices hz:Y p i r=0 by rw [hz, smul_zero]
      by_contra H; have hH:=h.1 p i r H; rw [Finset.mem_range] at hi;unfold Yield at *;omega
    have he (i:ℕ) : ∃ η:ℝ,0<η ∧ LightPay (fame _) η (0,a) (fun x=> bill H U e i r • Y x i r) (‖·‖):= by obtain ⟨s,C,hc,hB,H'⟩:= h.2.2 i r; exact ⟨s,hc,LightPay.amp (V:=edgeL G) (X:=Dawn.Studio D) ⟨C,hB,H'⟩ _⟩
    obtain ⟨s,hs,C,hc,H'⟩:=limelight (Finset.range (e+1)) fun i _=>he i; exact ⟨s,C,hs,hc,H'⟩
lemma banner_eq {p q:Pap I}[Fintype I](h:rancho p=rancho q):p=q:= by
    ext1 e; apply (crema _ (max (coeff e p).totalDegree (coeff e q).totalDegree) ?_).symm.trans ; apply Eq.trans _ (crema (coeff e q) (max (coeff e p).totalDegree (coeff e q).totalDegree) ?_); swap
    · show ∀ i,max (coeff e p).totalDegree (coeff e q).totalDegree < i → _; exact fun i hi=> (marble_eq_zero_iff ..).mpr (MvPolynomial.homogeneousComponent_eq_zero i _ (lt_of_le_of_lt (le_max_right ..) hi))
    · refine Finset.sum_congr rfl fun i _=>?_ ; exact congr_arg (facade i) (congr_fun (congr_fun h e) i)
    exact fun i hi=> (marble_eq_zero_iff ..).mpr (MvPolynomial.homogeneousComponent_eq_zero i _ (lt_of_le_of_lt (le_max_left ..) hi))
lemma banner_stain (hy:Wade a Y l)(H U:Pence)(p n): banner l (stir H U Y p) n=canter H U (wire G n) (banner l (Y p) n) := by
    have h:=hy.stirs H U
    apply banner_eq;funext i k; rw [badge (stir H U Y p) (h.1 _) (h.2.1 _) le_rfl, stamp_book,stir, stamp,stamp]
    rw [banner_sieve (T:=fun j=> bill H U i j k • Y p j k) _ (fun j _=> show Summable (bill H U i j k • Y p j k) from (hy.summable p j k).mul_left (bill H U i j k))]; apply Finset.sum_congr rfl; intro j _; rw [sieve_smul,badge (Y p) (hy.1 _) (hy.2.1 _) le_rfl]
lemma Son.stirs (h: Son Y T l s)(hy: Wade a Y l)(ht:Wade a T l)(hp : H*U=1): Son (stir H U Y) (stir H U T) l s:= by intro n p; rw [banner_stain hy H U,banner_stain ht H U];exact morph H U _ _ (h n p) hp
-- Faithful for held roots via sieve. Useful for comparing renormalized graph definitions
lemma banners_alive (h: Wade a Y l)(ht: Wade a T l)(he:∀ p n, banner l (Y p) n = banner l (T p) n): Y=T:= by -- auto
    funext p e r v; obtain ⟨s,C,hσ,-,H⟩:=h.2.2 e r;obtain ⟨t,B,h',-,U⟩:=ht.2.2 e r; refine tendsto_nhds_unique ((sieve_kalm _ (H p) hσ.le).1 v) (((sieve_kalm _ (U p) h'.le).1 v).congr' (.of_forall fun n=>?_ )); dsimp only;rw [← badge (Y p) (h.1 p) (h.2.1 p) le_rfl,he, badge (T p) (ht.1 _) (ht.2.1 _) le_rfl]
lemma film_worm (H U:Pence)(p:Pence)(I:Type): canter H U I (worm I p)= worm I (p.subst (H*X)):= by
    ext1 n; have hx : coeff 0 (H*X)=0:=by rw [coeff_zero_eq_constantCoeff_apply,map_mul]; simp
    have h:=change_subst (f:=C.comp (MvPolynomial.C (σ:=I) (R:=ℝ))) hx p n
    rw [(steam H U (dict (worm I p) n)).apex]; unfold worm; rw [← pure_map MvPolynomial.C (p.subst _), h.apex,map_sum,map_sum,map_sum]; refine Finset.sum_congr rfl fun j _=> ?_; rw [map_mul,map_pow,canter_X, Wine.glass, show changeBy _ (H*X)=(worm I H)*X from ?_]; swap;· rw [map_mul,pure_map, change_X];rfl
    rw [coeff_map, canter_C,insert_C]; rfl
lemma Clef.stirs (h:Clef a Y l)(hp:H*U=1): Clef a (stir H U Y) l:= by
   refine ⟨⟨fun f g=>?_,fun c p=>?_⟩,h.fare.stirs _ _,h.ward.stirs h.fare h.fare hp⟩
   · funext i r p; unfold stir stamp; rw [h.map_add]; simp [Finset.sum_add_distrib]
   funext i r v; unfold stir stamp; rw [h.map_smul]; simp only [Pi.smul_apply, Finset.sum_apply,smul_eq_mul,Finset.mul_sum]; apply Finset.sum_congr rfl; intro _ _; ring
lemma stir_worm (H U:Pence)(p:Pence)(h: Wade a Y l): stir H U (launch p Y)= launch (p.subst (H*X)) (stir H U Y):= by
   apply banners_alive ((h.launch _).stirs _ _) ((h.stirs _ _).launch _); intro z n; rw [banner_stain (h.launch p),banner_mul h,map_mul,film_worm,banner_mul (h.stirs H U),banner_stain h H U]
end YM.FormalBulk08.Kemp
