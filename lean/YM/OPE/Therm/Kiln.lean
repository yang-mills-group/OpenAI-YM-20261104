import YM.OPE.Therm.Filament
/-!
# Cut exponent, double spin, pre-flag costs

`energy U` leaves will be read literally with the indicated halos, including ALL masks
and trigger reads. Sign is energy, not log-density. Width eventual elsewhere.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Therm.Stove
open Function Filter RG Lattice Wilson MeasureTheory Next Next.Rank Next.Rank.Alarm PathData Cells Push.AbsoluteSums Push.Local
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side}
variable {σ C Λ δ w:ℝ}
local notation "Ex" => Real.exp
local notation "𝒞" => Config G n
variable (R:Rep G n)(r:ℕ)
local notation "B"=>R.p
local notation "F"=>R.path
local notation "β"=>R.beta
local notation "c"=>R.clip
local notation "A"=>R.activities
local notation "U'"=> (Fintype.card PlaqAxes :ℝ)

def rootPiece (i:PlaqAxes)(U:𝒞) := clipped c (B).threshold (G.chord (faceValue U (0,i))) + if kept c (B).threshold 0 U then ‖lakeHead F r i U‖^2/2 else 0
def draft (U:𝒞) := β*((∑ i,(F).baseTerm c B U (0,i))+(atomSeries (F).cubic B U 0+ atomSeries (F).quartic B U 0))+atomSeries (F).loop B U 0+ ease B A U
def flash (U:𝒞) := β*((∑ i, rootPiece R r i U)+(chips r (F).cubic B U+ chips r (F).quartic B U))+ chips r (F).loop B U+ toast r B A U
def sweet (C Λ δ:ℝ) := |β| *(U'*(2*(c).direct+2*(c).linear+2*C^2)+24*C)+4*Λ+δ
def wastage (σ C Λ δ:ℝ) := Ex (-σ*r)*(|β| *(U'* (4*C^2)+24*C)+4*Λ)+ Ex (-(B).supportExponent*r)*δ
private lemma repo (h:R.Lawful σ C Λ δ w)(i:PlaqAxes)(U:𝒞) :
    ‖rootPiece R r i U‖ ≤2*(c).direct+2*(c).linear+2*C^2 ∧ ‖(F).baseTerm c B U (0,i)-rootPiece R r i U‖ ≤ Ex (-σ*r)*(4*C^2) := by -- notation (c).dot likely fails
   let x := G.chord (faceValue U (0,i)); let y := clipped c (B).threshold x; let p := (B).threshold; have hx : 0≤x:= G.chord_nonneg _; have hX : x≤ 2:= G.chord_le_two _; have hp:0<p := (B).threshold_pos; have hP:p≤ 1:= (B).threshold_le; have ht:= (c).quadratic_pos; have hl:=(c).tail_pos
   have hh : ‖y‖ ≤ 2*(c).direct + 2*(c).linear:=by
      unfold y clipped; split
      · rw [Real.norm_of_nonneg (by positivity)]; nlinarith only [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hX 2) ht.le,hl]
      rw [Real.norm_of_nonneg (by change 0 ≤ (c).linear*p*x; positivity)]; have h := mul_le_mul hP hX hx zero_le_one; unfold p at *; linarith only [mul_le_mul_of_nonneg_left h hl.le,ht]
   let z₀:= lakeHead F r i U; let z₁:= (F).ell U (0,i); let w₁:=Ex (-σ*r); obtain ⟨hz,hZ,hT⟩:= rip r F h.paths i U
   have hs : -- simplify
       ‖‖z₁‖^2/2-‖z₀‖^2/2‖≤ w₁*(4*C^2):=by
       have hΔ : |‖z₁‖ - ‖z₀‖| ≤ w₁*(2*C):= (abs_norm_sub_norm_le z₁ z₀).trans hT
       set a:=‖z₁‖; set b:=‖z₀‖; have ha:0≤a:=norm_nonneg _; have hb:0≤b:=norm_nonneg _
       rw [Real.norm_eq_abs,show a^2/2-b^2/2=(a-b)*(a+b)/2 by ring,abs_div,abs_mul,abs_of_nonneg (add_nonneg ha hb)]; norm_num; have h:= mul_le_mul hΔ (add_le_add hz hZ) (add_nonneg ha hb) ((abs_nonneg (a-b)).trans hΔ); change |a-b| *(a+b) ≤ _ at h; linarith only [h]
   by_cases hK: kept c (B).threshold 0 U
   · unfold rootPiece PathData.baseTerm; simp only [hK,↓reduceIte]
     refine ⟨(norm_add_le ..).trans (add_le_add hh ?_),(by rw [add_sub_add_left_eq_sub]; exact hs)⟩
     rw [Real.norm_of_nonneg (by positivity)]; nlinarith only [pow_le_pow_left₀ (norm_nonneg _) hZ 2]
   unfold rootPiece baseTerm; simp only [hK,↓reduceIte,add_zero,sub_self,norm_zero]; exact ⟨hh.trans (le_add_of_nonneg_right (by positivity)),by positivity⟩
private lemma stock (h:R.Lawful σ C Λ δ w) (U:𝒞) :
    ‖flash R r U‖ ≤ sweet R C Λ δ ∧ ‖draft R U-flash R r U‖ ≤ wastage R r σ C Λ δ:=by
   let a:=Ex (-σ*r); let b:= 4*C^2; let v:= ∑ i, rootPiece R r i U
   have h3:= tear r (F).cubic B h.paths.three h.paths.width U
   have h4:= tear r (F).quartic B h.paths.four h.paths.width U
   have h2:= tear r (F).loop B h.paths.two h.paths.width U
   have he:= gentle r B h.labels U
   have hh : |β|=‖β‖ := (Real.norm_eq_abs ..).symm
   constructor
   · have hz : ‖v‖ ≤ U'*(2*(c).direct+2*(c).linear+2*C^2):= ((norm_sum_le ..).trans (Finset.sum_le_sum fun x (_:x∈Finset.univ)=> (repo R r h x U).1)).trans_eq (by simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ])
     unfold sweet flash; apply (norm_add_le ..).trans (add_le_add _ he.2.1); apply (norm_add_le ..).trans (add_le_add _ (by exact h2.2.1.trans_eq (by norm_num))); rw [hh,norm_mul]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); apply (norm_add_le ..).trans (add_le_add hz ((norm_add_le ..).trans _)); have H:= add_le_add h3.2.1 h4.2.1; linarith only [H]
   have hz : ‖(∑ i,(F).baseTerm c B U (0,i))-v‖ ≤ U'*(a*b):= by
      unfold v; rw [← Finset.sum_sub_distrib]; exact ((norm_sum_le ..).trans (Finset.sum_le_sum (fun x (_:x∈Finset.univ)=> (repo R r h x U).2))).trans_eq (by unfold a b; simp)
   have hβ:‖β*((∑ i,(F).baseTerm c B U (0,i))+(atomSeries (F).cubic B U 0+atomSeries (F).quartic B U 0)) - β*(v+(chips r (F).cubic B U + chips r (F).quartic B U))‖ ≤ |β| *(U'*(a*b)+a*(8*C)+a*(16*C)):=by
      rw [← mul_sub,norm_mul,add_sub_add_comm (∑ i, _),add_sub_add_comm (atomSeries (F).cubic _ _ _),add_assoc (U'*_), hh]; refine mul_le_mul_of_nonneg_left ((norm_add_le ..).trans (add_le_add hz ((norm_add_le ..).trans ?_))) (norm_nonneg _); exact (add_le_add h3.2.2 h4.2.2).trans_eq (by unfold a; ring)
   unfold wastage draft flash; rw [add_sub_add_comm _ (ease ..), add_sub_add_comm _ (atomSeries (F).loop _ _ 0)]; exact ((norm_add_le ..).trans (add_le_add ((norm_add_le ..).trans (add_le_add hβ h2.2.2)) he.2.2)).trans_eq (by unfold a b; ring)
lemma flash_local (hq: Turnon c (B).threshold r)(hs:8 ≤ r) (h:R.Lawful σ C Λ δ w): LocalOn (halo (eroom B r + 2*r+8) ({0}: Support n)) (flash R r):=by
   intro U V hp
   let X:= halo (2*r) (({0}: Support n):Support n); have hP : Agrees X U V:=agrees_mono hp (fun x hx=>Corona.halo_mono (by omega) (le_refl _) (show x∈X from hx))
   have h1 (v:ℕ) (hv:v≤2*r): Agrees (halo v ({0}: Support n)) U V:= agrees_mono hP (fun x hx=> Corona.halo_mono hv (le_refl _) hx); have hv:=h1 (r+8) (by omega)
   have ht (i:PlaqAxes) : faceValue U (0,i)=faceValue V (0,i):= by
      refine travel_local _ _ U V (agrees_mono hP fun x hx=>?_); apply halo_spec.mpr; exact ⟨0,Finset.mem_singleton_self _, (Work.E01.sep_touched (0,i) x (List.mem_toFinset.mpr hx)).trans (by omega)⟩
   unfold flash rootPiece
   let hw : Agrees (halo (eroom B r) ({0}: Support n)) U V:= agrees_mono hp fun x hx=> Corona.halo_mono (by omega) (le_refl _) hx
   simp only [ht,province hq (B).threshold_pos hs 0 U V hP,dripping_loc F r _ U V (h1 r (by omega)),chips_local r _ _ U V hv,toast_local r B h.labels.regular U V hw]
lemma flash_meas (h:R.Lawful σ C Λ δ w): Measurable (flash R r):=by
   have hx (i:PlaqAxes): Measurable (rootPiece R r i):= (clip_env B (0,i)).meas.add <| by -- U argument last?
        refine Measurable.ite ((kept_closed c (B).threshold (0 : Site n)).measurableSet) (((lake_meas F i r).norm.pow_const _).div_const _) measurable_const
   exact ((measurable_const.mul ((Finset.measurable_fun_sum _ fun i _=>hx i).add ((chips_meas r _ B).add (chips_meas r _ B)))).add (chips_meas r _ B)).add (toast_meas r B h.labels.regular)
lemma flash_gauge (h:R.Lawful σ C Λ δ w): GaugeInvariant (flash R r) :=by
   intro k U; let V:= Lattice.gauge k U
   have hp (i:PlaqAxes): rootPiece R r i V=rootPiece R r i U:=by unfold rootPiece V; simp only [face_gauge,G.chord_conj,kept_sym,lake_gauge F h.paths,G.norm_adjoint]
   have hc {j:ℕ}(P:ℕ→Atom G j)(h:∀ i,(P i).Invariant): chips r P B V=chips r P B U:= by refine tsum_congr fun i=>?_; unfold ends; split; exact scorn _ B (h i) 0 k U; rfl
   have he: toast r B A V=toast r B A U:=by refine tsum_congr fun i=>?_; unfold ends leaf; split_ifs; exact sails _ _ _ (h.labels.regular.smooth _|>.symmetry) _ _;all_goals rfl
   unfold flash; unfold V at hp hc he; simp_rw [hp,hc (F).cubic (fun i=>(h.paths.invariant i).2.1),hc (F).quartic (fun i=>(h.paths.invariant i).2.2),hc (F).loop (fun i=>(h.paths.invariant i).1), he]
section sym
variable {R r}
def doll (f:𝒞→ℝ)(x:Site n)(U:𝒞):= Branch.avg (fun s:Signed=>f (pull s x U))
lemma doll_rag (f:𝒞→ℝ)(U:𝒞): (∑ x:Site n,doll f x U)= rag f U:=by simp_rw [doll,Branch.avg,smul_eq_mul]; rw [← Finset.mul_sum,Finset.sum_comm];rfl
lemma doll_diff (f g:𝒞→ℝ)(x:Site n)(U:𝒞): doll f x U-doll g x U=doll (fun U=>f U-g U) x U:= by unfold doll; rw [Branch.avg_sub]
lemma doll_turn (f:𝒞→ℝ) (s:Signed)(x y:Site n)(U:𝒞): doll f x (pull s y U)=doll f (affine s y x) U:=by
   apply congr_arg ((Fintype.card Signed:ℝ)⁻¹*·); exact Fintype.sum_equiv (Equiv.mulLeft s) _ _ fun i=> congr_arg f (pull_pull ..)
lemma doll_home (f:𝒞→ℝ) (a:ℕ) (h:LocalOn (halo a ({0}: Support n)) f) (x:Site n) : LocalOn (halo a {x}) (doll f x):=by
   intro U V he; apply congr_arg Branch.avg; ext i; apply h; apply agrees_pull; rw [← halo_map (turnSites i x) (turn_sep i x), Finset.image_singleton]; have hp : turnSites i x 0=x:=by change affine i x 0=x; simp [affine]
   rw [hp]; exact he
lemma doll_invar {f:𝒞→ℝ} (h:GaugeInvariant f) (x:Site n): GaugeInvariant (doll f x) :=by intro k U; unfold doll; simp_rw [pull_gauge]; apply congr_arg Branch.avg; exact funext fun i=>h ..
lemma doll_meas {f:𝒞→ℝ} (h:Measurable f) (x:Site n) : Measurable (doll f x):= measurable_const.mul (Finset.measurable_fun_sum _ fun i _=>h.comp ((continuous_pull ..).measurable))
lemma doll_bound {f:𝒞→ℝ}(he: ∀ U,‖f U‖≤C) (x:Site n)(U): ‖doll f x U‖ ≤ C:= ((Branch.norm_avg _).trans (Branch.avg_mono (g:=fun _:Signed=> C) (fun i => he (pull i x U)))).trans_eq (Branch.avg_const _)
end sym
def haloFee := eroom B r +2*r+8
def energy (x:Site n):= doll (flash R r) x
structure Chart (u a : ℝ) : Prop where
  home x : LocalOn (halo (haloFee R r) {x}) (energy R r x)
  turn s (x y:Site n) U : energy R r x (pull s y U) = energy R r (affine s y x) U
  shoots x : GaugeInvariant (energy R r x)
  paid (x:Site n) U : ‖energy R r x U‖ ≤ u
  bill x : Measurable (energy R r x)
  rate (U : 𝒞) : ‖(R.exponent U-R.scalar)+∑ x, energy R r x U‖ ≤ Fintype.card (Site n) * a
lemma tender (hr:Turnon c (B).threshold r)(hs: 8 ≤ r)(h:R.Lawful σ C Λ δ w) : Chart R r (sweet R C Λ δ) (wastage R r σ C Λ δ) :=by
   refine ⟨doll_home _ _ (flash_local R r hr hs h), doll_turn _ , doll_invar (flash_gauge R r h), doll_bound (fun U=>(stock R r h U).1), doll_meas (flash_meas R r h),fun U=>?_⟩
   have ht: R.exponent U-R.scalar = -∑ x,doll (draft R) x U:=by rw [Rep.exponent,Rep.scalar,doll_rag]; unfold draft; rw [rag_add,rested B h.labels U,Edition.exponent_rag F B c β]; ring
   rw [ht,neg_add_eq_sub, norm_sub_rev,← Finset.sum_sub_distrib]; unfold energy; simp_rw [doll_diff]; exact ((norm_sum_le ..).trans (Finset.sum_le_sum (fun x (_:x ∈ Finset.univ)=>doll_bound (fun U=>(stock R r h U).2) x U))).trans_eq (by simp)
end YM.OPE.Therm.Stove
