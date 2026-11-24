import YM.MSbar.Tree.Torus
import YM.MSbar.Tree.Far
import YM.MSbar.Tree.Line
import YM.Next.RANK.Scars

/-! # Estimate the jet covariance in the leading Wilson cutoff diagrams -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Tree
open Function Set Filter Lattice Laurent Bloch Matrix Exterior
open scoped Topology BigOperators ComplexConjugate Classical ContDiff
open Next.Rank Next.Rank.Radian Next.Rank.CellsInt Next.Rank.Beamer
open Next.Rank.Prayer PhysicalNext.RankCovariance Torus

variable {n : Side} {G : Gauge} {k l : ℕ} (a : Component G k) (b : Component G l)
variable (u v : Cover)
open Further.FreeCovariance.KP
private lemma chart_cost (k : ℕ) (a b : Beamer.Degree G) : ∃ F : E4→ℂ, ∃ B:ℝ, 1≤ B ∧
    (∀ (m : Side) u v, (if a.paint=b.paint then Torus.kernel m u v a.a b.a else 0)=
      (stepsP F m 2 (mapZ (u-v))).re) ∧ Radian.Window F 2 B k chartHeat a b := by
  obtain ⟨A,G',d,ha,he,hL⟩:= Episode.paid _ (j:=4) (show (0:ℝ)<1 from one_pos) le_rfl
  obtain ⟨f,hf⟩:= hL (.top 4)
  obtain ⟨C,hC,h⟩:= window_prices ha he G' k
  let F:= coloredChart f a b; let B:=max 1 C; have hw : Radian.Window F 2 C k chartHeat a b:= h f a b
  refine ⟨F,B,le_max_left ..,?_,⟨hC.trans (le_max_right ..),hw.event, hw.coast.trans (le_max_right ..),hw.meas, hw.cast.coin (le_max_right ..),hw.crest.coin (le_max_right ..)⟩⟩
  intro m u v; unfold F coloredChart; split <;> rename_i H
  · rw [kernel_found, chart_reads,Episode.bridge 1 one_pos le_rfl ha he (.top 4) f hf]
  simp [*,stepsP,scansP]

/-- Straight bridge and image bridge, retaining integer endpoints in native
units. Image does not need to be guessed from a shifted continuum
representative and remains essential at finite torus side. -/
def physical (u v : Cover) (K : Cover → Cover → PlaqAxes → PlaqAxes → ℝ) : Bridge G :=
  fun a b => if a.2.2=b.2.2 then K (u+a.1) (v+b.1) a.2.1 b.2.1 else 0

def straight (m : Side) (u v : Cover) (a : Component G k) (b : Component G l) : ℝ :=
  mourn (gesture (native a)) (gesture (native b)) (physical u v (kernel m))

def imageLine (m : Side) (u v : Cover) (a : Component G k) (b : Component G l) : ℝ :=
  mourn (gesture (native a)) (gesture (native b)) (physical u v (fun x y a b => kernel m x (reflectPos y b) a b))

/-- True equivariant finite-volume answer at order zero for a pair of jets.
No quotient is taken on this top leg space. `r` here INVERSE spacing. -/
def atCut (r : ℝ) (m : Side) (u v : Cover) (a : Component G k) (b : Component G l) :=
    r^(k+l+4) * (straight m u v a b + imageLine m u v a b)

lemma true_cut (r : ℝ) (m : Side) : atCut r m u v a b = r^(k+l+4) * mourn (gesture (native a)) (gesture (native b))
    (physical u v (kernelOrbit m)) := by
  unfold atCut straight imageLine; rw [← map_add]
  congr 2; funext x y; unfold physical kernelOrbit; split_ifs with h <;> simp [h]

private lemma phys_sym (K : Cover → Cover → PlaqAxes → PlaqAxes → ℝ)
    (h : ∀ x y a b, K x y a b = K y x b a) : physical u v (G:=G) K=(fun i j => physical v u K j i) := by
  funext i j; unfold physical; by_cases he:i.2.2=j.2.2
  · rw [if_pos he,if_pos he.symm]; exact h ..
  rw [if_neg he,if_neg (Ne.symm he)]

lemma straight_symm (m : Side) : straight m u v a b= straight m v u b a:= by
  unfold straight; rw [moves _ _ _ (bright_gesture _)]; congr 1
  exact (phys_sym _ _ _ (kernel_symm m)).symm

lemma straight_shift (m : Side) (w : Cover) : straight m (w+u) (w+v) a b = straight m u v a b := by
  unfold straight; congr 1
  funext i j; unfold physical; simp only [kernel, add_assoc,add_sub_add_left_eq_sub]

lemma cut_symm (r : ℝ) (m : Side) : atCut r m u v a b=atCut r m v u b a:= by
  rw [true_cut,true_cut,moves _ _ _ (bright_gesture _), Nat.add_comm k l]; congr 2
  exact (phys_sym _ _ _ (kernelOrbit_symm m)).symm

lemma ahead : ∃ C : ℝ, 0≤ C ∧ ∀ (m:Side) u v,
    let z:=mapZ (u-v)
    1 ≤ ‖z‖ → ‖straight m u v a b- gleam (native a) (native b) z‖ ≤ C* Wall.stature (k+l) z (m.val:ℝ) := by
  let d:= k+l+6; let A:= native a;let W:= native b
  obtain ⟨F,B,hB,hF,hW⟩:= chart_cost d A W
  obtain ⟨T,hT,h⟩:= Radian.intended 2 (by decide) A W chartHeat_pos d le_rfl
  let D:=max 1 (B*T); have hD:1≤D:=le_max_left ..
  obtain ⟨hh,hr,hL⟩:= h F B D hB hW (le_max_right ..)
  obtain ⟨c,hc,hY⟩:= TK A W 2 chartHeat_pos
  refine ⟨c*D,mul_nonneg hc (zero_le_one.trans hD),fun m u v=>?_⟩
  intro z he; specialize hY _ D hD hh hr hL m z he; unfold straight
  rw [seats u v A W m 2 F _ (fun x y=> ?_)]
  · unfold captured; change ‖(stepsP (parade A W F) _ _ (mapZ (u+0-(v+0)))).re-_‖ ≤ _; rw [add_zero,add_zero]; exact hY
  exact hF _ (u+x) (v+y)

lemma kernel_far (i j : Address G) : ∃ C : ℝ,0≤C ∧ ∀ (u v : Cover) (m : Side) (q : Axis),
    (mapZ (u+i.1-reflectPos (v+j.1) j.2.1)) q/m.val ∈ Icc (1/8:ℝ) (3/4) →
      ‖physical u v (fun x y a b=> kernel m x (reflectPos y b) a b) i j‖ ≤ C/m.val:= by
  let a : Beamer.Degree G := ⟨i.2.1,i.2.2,0,0,Fin.elim0⟩; let b : Beamer.Degree G:= ⟨j.2.1,j.2.2,0,0,Fin.elim0⟩
  obtain ⟨F,B,hB,hF,hW⟩:= chart_cost 1 a b
  obtain ⟨C,hC,h⟩:= Far.far_bound hW.nonneg (hW.cast.lips hW.event le_rfl hW.coast)
  refine ⟨C,hC,fun u v m q H =>?_⟩
  let y:=reflectPos (v+j.1) j.2.1
  let p:= stepsP F m 2 (mapZ (u+i.1-y)); change ‖(if a.paint=b.paint then kernel m (u+i.1) y a.a b.a else 0)‖ ≤ _; rw [hF]
  exact (Complex.abs_re_le_norm p).trans (h _ q _ H)

/-- Positions for the regulator. Asking just in coordinate zero already
suffices against every singularity (top-side fractions, not physical units).
Includes the conventional [1/8,1/4]^4 center and any bounded physical
offsets when period is large. -/
def central (m : Side) (x : Cover) : Prop := m.val/9 ≤ mapZ x 0 ∧ mapZ x 0 ≤ 3/10*(m.val:ℝ)

private lemma remains (x y : Address G) : ∀ᶠ M:ℕ in atTop,∀ m : Side, M≤m.val→ ∀ u v, central m u → central m v →
    (mapZ (u+x.1-reflectPos (v+y.1) y.2.1)) 0/m.val ∈ Icc (1/8:ℝ) (3/4):= by
  let Z:= mapZ (x.1+y.1+bumpFace y.2.1) 0
  have ht:Tendsto ((↑):ℕ→ℝ) atTop atTop:= tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_ge_atTop (20*|Z|)] with i hi m hm u v hu hv
  have h : 20*|Z| ≤ (m.val:ℝ):= hi.trans (Nat.cast_le.mpr hm)
  rw [reflectPos,show u+x.1-(-(v+y.1)-bumpFace y.2.1)= (u+v)+(x.1+y.1+bumpFace y.2.1) from by abel]
  rw [Wall.sends_map (u+v),Wall.sends_map u]
  let n:ℝ:=m.val; have hn:0<n:= Bloch.side_pos m
  change _≤(mapZ u 0+mapZ v 0+Z)/n ∧ (mapZ u 0+mapZ v 0+Z)/n ≤ _; rw [div_le_iff₀ hn,le_div_iff₀ hn]; unfold n
  rcases hu with ⟨h₁,h₂⟩; rcases hv with ⟨h₃,h₄⟩; constructor
  · linarith only [neg_le_abs Z,h,h₁,h₃]
  linarith only [le_abs_self Z,h,h₂,h₄]

lemma discounted : ∃ C:ℝ, 0≤C ∧ ∀ᶠ M:ℕ in atTop, ∀ (m : Side), M≤m.val → ∀ u v, central m u → central m v →
    ‖imageLine m u v a b‖ ≤ C/m.val:= by
  obtain ⟨P,hP⟩:= bright_gesture (native a); obtain ⟨Q,hQ⟩:= bright_gesture (native b)
  choose A hA h using (kernel_far (G:=G)); let T (x y):= ‖P x‖*(‖Q y‖*A x y)
  let C:= ∑ i∈P.support,∑ j∈Q.support,T i j
  have he : 0 ≤ C:= Finset.sum_nonneg fun i _=> Finset.sum_nonneg fun j _=> mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (hA i j))
  refine ⟨C,he,?_⟩; filter_upwards [(eventually_all_finset P.support).2 (fun i _=> (eventually_all_finset Q.support).2 (fun j _=> remains i j))] with k hk m hm u v hu hv
  let F := physical (G:=G) u v (fun x y a b => kernel m x (reflectPos y b) a b)
  rw [show imageLine m u v a b = ∑ i∈ P.support,P i * ∑ j ∈ Q.support, Q j*F i j from ?_]; swap
  · change gesture (native a) (fun i=>gesture (native b) (F i))=_
    simp_rw [hQ,hP]; rfl
  unfold C; rw [Finset.sum_div]; refine (norm_sum_le ..).trans (Finset.sum_le_sum fun i hi=>?_)
  rw [norm_mul]; apply le_trans (mul_le_mul_of_nonneg_left (norm_sum_le ..) (norm_nonneg _)); rw [Finset.mul_sum,Finset.sum_div]
  refine Finset.sum_le_sum fun j hj=> ?_
  rw [norm_mul]; unfold T; rw [div_eq_mul_inv, mul_assoc, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); rw [←div_eq_mul_inv]
  exact h i j u v m 0 (hk i hi j hj m hm u v hu hv)

lemma normalized_bound {T : ℝ} (hT : 1 ≤ T) :
    ∃ C:ℝ, 0≤ C ∧ ∀ r:ℝ, T ≤ r → ∀ (m:Side), r^(k+l+6) ≤ (m.val:ℝ) → ∀ u v,
      r/T ≤ ‖mapZ (u-v)‖ → ‖mapZ (u-v)‖ ≤ T*r →
        ‖r^(k+l+4)*straight m u v a b - gleam (native a) (native b) (r⁻¹ • mapZ (u-v))‖ ≤ C/r:= by
  let D:=k+l+4; obtain ⟨B,hB,h⟩:= ahead a b; have he:0<T:=zero_lt_one.trans_le hT
  refine ⟨B*T^(D+1)+B*(1+T),by positivity,fun r hr m hv u v h₁ h₂=>?_⟩
  have hs:1≤r:=hT.trans hr; have hr':= he.trans_le hr
  let z:= mapZ (u-v); have hz:1≤‖z‖:= (one_le_div he|>.2 hr).trans h₁
  have hp:0<‖z‖:= zero_lt_one.trans_le hz; let A:=gleam (native a) (native b)
  have ha : r^D*A z = A (r⁻¹ • z) := by
    let x:=r⁻¹ • z
    rw [show A z=A (r • x) by unfold x; rw [smul_smul,mul_inv_cancel₀ hr'.ne',one_smul]]
    rw [show r^D=amount r (native a)*amount r (native b) from ?_,grown]
    · exact hr'
    · exact (smul_ne_zero (inv_ne_zero hr'.ne') (norm_pos_iff.mp hp))
    unfold amount; rw [← pow_add]; congr 1; change k+l+4=k+2+(l+2); omega
  change ‖r^D*_ - A (r⁻¹ • z)‖ ≤ _
  rw [← ha, ← mul_sub,norm_mul,Real.norm_of_nonneg (pow_nonneg hr'.le _), le_div_iff₀ hr']
  refine le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (h _ _ _ hz) (pow_nonneg hr'.le D)) hr'.le) ?_
  change r^D*(B*(1/‖z‖^(D+1)+(1+‖z‖)/(m.val:ℝ)))*r ≤ _
  have h1 : r^(D+1)/‖z‖^(D+1) ≤ T^(D+1):= by
    rw [←div_pow]; exact pow_le_pow_left₀ (div_nonneg hr'.le hp.le) ((div_le_iff₀ hp).2 ((div_le_iff₀ he).1 h₁|>.trans_eq (mul_comm ..))) _
  have h2 : r^(D+1)* (1+‖z‖)/m.val ≤ 1+T:= by
    rw [div_le_iff₀ (side_pos m)]; refine le_trans ?_ (mul_le_mul_of_nonneg_left hv (by positivity));
    change _ ≤ (1+T)*r^(D+1+1); rw [pow_succ r (D+1)]
    change ‖z‖ ≤ _ at h₂; nlinarith only [mul_le_mul_of_nonneg_left (show 1+‖z‖ ≤(1+T)*r by linarith only [hs,h₂]) (pow_pos hr' (D+1)).le]
  apply le_trans (le_of_eq (b:= B*(r^(D+1)/‖z‖^(D+1))+B*(r^(D+1)*(1+‖z‖)/(m.val:ℝ))) ?_) (add_le_add (mul_le_mul_of_nonneg_left h1 hB) (mul_le_mul_of_nonneg_left h2 hB)); ring
end YM.MSbar.Tree
