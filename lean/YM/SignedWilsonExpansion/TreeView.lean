import YM.SignedWilsonExpansion.TreeLine

/-! Accounting for static tree counterterms in the high heat evolution. -/
noncomputable section
set_option autoImplicit false
namespace YM.SignedWilsonExpansion.TreeView
open Function Filter Set MeasureTheory Finset
open MS MS.Plane MS.Koszul MS.Landau MS.Landau.Detect MS.Port MS.Pearl MS.Rake MS.High
open MS.Logarithm MS.Alps MS.Outlook MS.Emit MS.Plane.Wire MS.Plane.Domain MS.Plane.Flux MS.Heat MS.Latch MS.Book
open HighScale HighRank TreeLine
open scoped Topology BigOperators ContDiff
variable {G : Gauge} {r : ℕ} {d : ℤ} {b : Bool} {F H : Law G} {A D : Reading G}
local notation "Σb" => Branch G Axis
-- off-shell smooth for constructing particular solutions.
def Polish (F : Law G) : Prop := ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (w:Wire Σb E FourP), ContDiff ℝ ∞ (fieldVal F w)
lemma Polish.add (f:Polish F)(h:Polish H): Polish (F+H):=fun E _ _ w=> (f E w).add (h E w)
lemma Polish.sub (f:Polish F)(h:Polish H): Polish (F-H):=fun E _ _ w=> (f E w).sub (h E w)
lemma Polish.smul (f:Polish F)(c:ℂ): Polish (c • F):=fun E _ _ w=> (f E w).const_smul c
lemma Polish.tree {K:Line G}(hf:Polish F)(hh:Polish H)(hw:∀ i j,ContDiff ℝ ∞ (K i j)): Polish (tree parity K F H):= by
  intro E _ _ w; unfold fieldVal Flux.tree; simp only [sail_scatter,attaches,sail_net,sail_degree]; apply round_scat; intro l r h; let Q:=net l
  have hX (i:Σb) : ContDiff ℝ ∞ (fun x:E=> F ((i,-Q x)::sail l x)) := hf E ((i,-Q)::l)
  have hY (i:Σb) : ContDiff ℝ ∞ (fun x:E=> H ((i,Q x)::sail r x)) := hh E ((i,Q)::r)
  simp_rw [neg_neg]
  exact ContDiff.sum fun i _=> ContDiff.sum fun j _=> (((hw i j).comp (-Q).contDiff).mul ((contDiff_const.mul (hX i)).mul (hY j))).add (((hw i j).comp Q.contDiff).mul ((contDiff_const.mul (hX j)).mul (hY i)))
lemma Polish.chi (hf:Polish F)(hh:Polish H)(t:ℝ): Polish (Flux.tree parity (TreeLine.chi G t) F H) := by
  apply Polish.tree hf hh
  intro i j
  have he:= chi_smooth i j
  exact he.comp (f:=fun x:FourP => (t,x)) (contDiff_const.prodMk contDiff_id)


lemma covariant_sub (a:Covariant A b r d)(c:Covariant D b r d): Covariant (A-D) b r d:= fun y t s w h e=> by
    rw [Pi.sub_apply,Pi.sub_apply,a y t s w h e,c y t s w h e]; unfold Port.shift; simp [mul_sub]
lemma covariant_add (a:Covariant A b r d)(c:Covariant D b r d): Covariant (A+D) b r d:= fun y t s w h e=> by
    rw [Pi.add_apply,Pi.add_apply,a y t s w h e,c y t s w h e]; unfold Port.shift; simp [mul_add]
lemma covariant_smul (a:Covariant A b r d)(t:ℂ): Covariant (t • A) b r d:= fun y z s w h e=> by
    rw [Pi.smul_apply,Pi.smul_apply,a y z s w h e]; unfold Port.shift; simp [smul_eq_mul]; ring

def shear (A:ℝ→ Law G) (b:Bool) : Prop := ∀ (s v:ℝ)(w:Legs (Lane4 G)), Course b w → A s w=Port.shift 4 v (A (s-v)) w
lemma shear.cov {K:ℝ→ Law G}(h:shear K b) (r:ℕ): Covariant (K ∘ Prod.snd) b r 4:=fun _ t s w hv _=> h t s w hv
lemma shear.add {K L:ℝ→ Law G}(h:shear K b)(hr:shear L b): shear (K+L) b:=fun s v w hc=> covariant_add (h.cov w.length) (hr.cov w.length) 0 s v w hc rfl
lemma shear.smul {K:ℝ→ Law G}(h:shear K b)(c:ℂ): shear (c • K) b := fun s v w hc=> covariant_smul (h.cov w.length) c 0 s v w hc rfl
lemma shear.tree {K L:ℝ→ Law G}(h:shear K true)(ht:shear L b): shear (fun t=>Flux.tree parity (chi G t) (K t) (L t)) b:= by
    intro s v w hc
    rw [show (4:ℤ)=4+4-4 from rfl,←trees_time (h:=4) (k:=4) (F:=K (s-v)) (H:=L (s-v)) s v]
    dsimp only
    cases b
    · rw [tree_agrees (chi G s) parity _ _ (L s) (show Agrees (K s) _ from fun l a=>h s v l (fun _=> a))]
      have he:= funext fun w=>ht s v w (fun h=>Bool.noConfusion h); rw [he]
    exact agrees_tree (K s) (L s) (chi G s) parity (fun w a=>h s v w (fun _=>a)) (fun w a=>ht s v w (fun _=>a)) w (hc rfl)

lemma shear_form (h: Form F wfield 4 b): shear (fun _=>F) b:=by
    intro s v w hw
    let V:=h ℝ (ray w) (ray_course hw); unfold Port.shift
    have hs:= V.scale (Real.exp v) 1
    rw [ray_dim] at hs; rw [smul_eq_mul,mul_one, fieldVal,fieldVal,ray_sail, ←one_mul (Real.exp v)] at hs
    rw [mul_comm, ← smul_eq_mul,← dilate_line, ray_sail] at hs  -- occurrence? 
    simp only [smul_eq_mul,mul_one] at hs
    dsimp only
    rw [hs]; unfold τ; rw [←Complex.real_smul,smul_smul, ← zpow_add₀ (Real.exp_pos _).ne',show pitch w-4+(4-fieldDim wfield w)=0 from by unfold pitch; omega, zpow_zero,one_smul]

lemma peel_static {P : ℝ → Law G}(hv:∀t,Polish (A t))(hc : Covariant A b r d) (hd : stamp A)
    (hf : ∀ t,Polish (P t))(pc:Covariant (P∘Prod.snd) b r d)
    (hA:∀ (y t:ℝ) (w:Legs (Lane4 G)), Course b w → w.length=r → HasDerivAt (fun t=> A (y,t) w) (D (y,t) w) t)
    (hB:∀ (y t:ℝ) (w:Legs (Lane4 G)), Course b w → w.length=r → HasDerivAt (fun t=> P t w) (D (y,t) w) t) : Static (A-(P∘Prod.snd)) r d b:= by
      refine static_of ?_ (covariant_sub hc pc) (fun E _ _ w h hr t=> (hv t|>.sub (hf t.2)) E w ) (Ready.sub hd (Ready.const P))
      intro y t w h hr
      have hx:= (hA y t w h hr).sub (hB y t w h hr); rw [sub_self] at hx; exact hx
/-- At leading ranks only uncontracted external arms contribute. Equal high parts are enough for tree comparison. -/
lemma tree_peak (K:Line G){n m:ℕ} {F H P Q:Law G}(hf:∀ w, Course true w → m≤w.length → F w=P w)(hh:∀ w, Course b w → n≤w.length → H w=Q w)(hut:Upper true m F)(hot:Upper b n H)
   (w:Legs (Lane4 G))(hr:w.length+2=m+n)(hc:Course b w): tree parity K F H w=tree parity K P Q w:= by
  unfold tree; apply scatter_congr; intro l k split; have hlen:= split_length split; unfold attaches; simp_rw [neg_neg]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>?_
  let L (a:Σb):Legs (Lane4 G):=(a,-net l)::l
  let R (a:Σb):Legs (Lane4 G):=(a,net l)::k
  have hl (a): Course true (L a):=fun _=>by simp [L]
  have he (a): Course b (R a):=fun h=>by simp only [R,net_cons]; rw [split_net split]; exact hc h
  by_cases hv:l.length+1=m
  · rw [ hf _ (hl i) (by simp [L,hv]), hf _ (hl j) (by simp [L,hv]), hh _ (he i) (by simp [R]; omega), hh _ (he j) (by simp [R]; omega)]
  rcases lt_or_gt_of_ne hv with h|h
  · have hu:k.length+1>n:=by omega
    have hx a:= hot (R a) (he a) (by simp only [R,List.length_cons]; omega)
    have hy a:= hh (R a) (he a) (by simp [R]; omega)
    dsimp only [R] at hx hy
    rw [← hy i,← hy j,hx i,hx j]
    ring
  have hx a:= hut (L a) (hl a) (by simp only [L,List.length_cons]; omega)
  have hy a:= hf (L a) (hl a) (by simp [L]; omega)
  dsimp only [L] at hx hy
  rw [← hy i,← hy j,hx i,hx j]; ring

lemma tree_limit {K:ℝ→ Line G}{L:Line G}(A D:ℝ→ Law G)(hk:∀ i j p,Tendsto (fun x=> K x i j p) atBot (𝓝 (L i j p)))(h:∀ w,Tendsto (fun x=> A x w) atBot (𝓝 (F w)))(g:∀ w,Tendsto (fun x=> D x w) atBot (𝓝 (H w)))(l:Legs (Lane4 G)):
    Tendsto (fun x=>tree parity (K x) (A x) (D x) l) atBot (𝓝 (tree parity L F H l)) := by
  let p:=field (P:=FourP) (parity (A:=Axis) (C:=G.ColorIndex))
  have hs (w:List (Lane4 G)) (V:ℝ→Shared (Lane4 G) ℂ) (Q:Shared (Lane4 G) ℂ)(hv:∀ i j, Tendsto (fun x=> V x i j) atBot (𝓝 (Q i j))): Tendsto (fun x=> scatter p w (V x)) atBot (𝓝 (scatter p w Q)):= by
    induction w generalizing V Q with | nil=>exact hv [] [] | cons a l ih=> exact ih _ _ (fun i j=> (hv (a::i) j).add ((hv i (a::j)).const_mul _))
  apply hs l (fun x=> attaches parity (K x) (A x) (D x)) _
  intro i j; unfold attaches; dsimp only; exact tendsto_finsetSum _ (fun x _=> tendsto_finsetSum _ (fun y _=> (((hk ..).mul (((h _).const_mul _).mul (g _)) ).add ((hk ..).mul (((h _).const_mul _).mul (g _)) ))))
lemma tree_dies (F H:Law G) (w:Legs (Lane4 G)): Tendsto (fun t=> tree parity (chi G t) F H w) atBot (𝓝 0):= by
  have he: tree parity (0:Line G) F H w=0:=by
    unfold tree; rw [show attaches parity (0:Line G) F H=0 from funext fun l=> funext fun k=> by simp [attaches] ]; exact map_zero (allocate (field parity) w)
  rw [←he]; exact tree_limit (L:=0) (fun _=>F) (fun _=>H) chi_helper (fun _=>tendsto_const_nhds) (fun _=>tendsto_const_nhds) w
where
  chi_helper(i j:Σb)(p:FourP): Tendsto (fun t=>chi G t i j p) atBot (𝓝 0):=chi_cold ..

lemma charge_limit {D:Law G} {t:ℝ} {w:Legs (Lane4 G)}
    (h:∀ v,Course b v → v.length=w.length→ Tendsto (fun s=>A (t,s) v) atBot (𝓝 (D v)))(hc:Course b w):
    Tendsto (fun s=>natQ (A (t,s)) w) atBot (𝓝 (natQ D w)):= by
  simp_rw [natQ,visit_Z]; apply visit_limit; intro l i k hx; apply tendsto_finsetSum; intro j hj; subst w; exact (h _ (visit_course b l k i hc j) (by simp)).const_mul _

lemma reverse_day (t:ℝ) : Reverse (PlanetD G t) parity := Garment.Wick.reverse_a G t 0
lemma tree_zip_chi {A D:ℝ→ Law G}(t:ℝ)(h:Zip A F t)(hh:Zip D H t): Zip (fun x=>tree parity (chi G x) (A x) (D x)) (tree parity (PlanetD G t) (A t) (D t)+tree parity (chi G t) F (D t)+tree parity (chi G t) (A t) H) t:= tree_zip (p:=parity) chi_reverse (reverse_day t) (fun i j x=> chi_deriv i j x t) h hh

lemma static_prior (F : Static (A-D) r d b)(y:ℝ) (w:Legs (Lane4 G))(hc:Course b w)(hw:w.length=r)
    (h: Tendsto (fun t=> D (y,t) w) atBot (𝓝 0)) :
    Tendsto (fun t=>A (y,t) w) atBot (𝓝 ((A-D) (y,0) w)) := by
  simp_rw [show (fun t:ℝ=>A (y,t) w)=fun t=> D (y,t) w+(A-D) (y,0) w from funext fun t=> by rw [F.time y 0 t w hc hw]; simp]
  simpa only [zero_add] using h.add_const ((A-D) (y,0) w)

abbrev qLine (G:Gauge)(t:ℝ): Line G := (degreeMaster id (spaceD G)).meter t
abbrev qAt (G:Gauge): Line G:= MS.Garment.Wick.D0 G 0
lemma ward_cold (i j:Σb)(p:FourP): Tendsto (fun t=>qLine G t i j p) atBot (𝓝 (qAt G i j p)):= by
  let f (r:ℝ):= choir (C:=G.ColorIndex) (laplace (Landau.low r)) id i j p
  have hf: Continuous f:= by
    unfold f choir; split; swap; · exact continuous_const
    rcases i with ⟨⟨_|i,_|_⟩,c⟩ <;> rcases j with ⟨⟨_|j,_|_⟩,d⟩
    all_goals dsimp only [id,laplace]; first| exact continuous_const| skip
    all_goals simp only [delta,Landau.low,coat, Momentum.scaling]; first|fun_prop|(split_ifs <;> fun_prop)
  have h : f 0=qAt G i j p:= by
    change _=choir (laplace (fun _=>1)) id i j p
    unfold f; rw [show (Landau.low 0:FourP→ℝ)=(fun _=>1) from funext fun p=>by simp [coat,Landau.low,Momentum.sq]]
  exact h ▸ (hf.tendsto 0).comp Real.tendsto_exp_atBot
lemma tree_deriv (t:ℝ)(w:Legs (Lane4 G))(F H:Law G): HasDerivAt (fun t=> tree parity (chi G t) F H w) (tree parity (PlanetD G t) F H w) t:= by
  have ht:= tree_zip_chi (F:=0) (H:=0) t (A:=fun _=>F) (D:=fun _=>H) (fun _=>hasDerivAt_const ..) (fun _=>hasDerivAt_const ..) w
  rw [show tree parity (chi G t) 0 H=0 from map_zero (boulevard parity (chi G t)|>.flip H), show tree parity (chi G t) F 0=0 from map_zero (boulevard parity (chi G t) F),add_zero,add_zero] at ht; exact ht
end YM.SignedWilsonExpansion.TreeView
