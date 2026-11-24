import YM.WilsonCoeffUV.Reclosure.Laurent
/-!
# Null Rays extracted *before* two-leg lifting
Third-degree term also tested, preserving full loop normalization.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank.Mosaic
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Stationary Asymptotics
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{V:Type*}{F:post G 1}{s A:ℝ}{r:ℕ}

-- moments to rays

def splat (p:Corn (Keys 1)): Cover→ℝ:= ∑ i:Axis,p (0,i) • chalk i
lemma broadS {ι:Type*} {Z:ι→Cover→ℝ}(s:Finset ι)(h:∀ i∈s,broad (Z i)): broad (∑ i∈s,Z i):= by
   classical
   induction s using Finset.induction_on with
   | empty=> rw [Finset.sum_empty]; exact broad.const 0
   | @insert i s p ih=> rw [Finset.sum_insert p]; exact (h i (Finset.mem_insert_self ..)).add (ih fun j e=> h j (Finset.mem_insert_of_mem e))
lemma broad_pow {f}(h:broad f)(j:ℕ): broad (f^j):=by induction j with
                                                         | zero=> rw [pow_zero]; exact broad.one
                                                         | succ j ih=> rw [pow_succ]; exact ih.mul h
lemma broad_splat (p:Corn (Keys 1)): broad (splat p):=broadS _ fun _ _=> broad_gain (broad.chalk _) _
lemma tailor_joint (h:Amber terrain s A F)(he:0<s)(u:Hooks G)(i:Axis)(c:G.ColorIndex){ι:Type*}{K:ι→ Cover→ℝ} (P:Finset ι)(hp:∀ i∈ P,broad (K i)): tailor F u i c (∑ j∈P,K j)=∑ j∈ P,tailor F u i c (K j) := by
   classical
   induction P using Finset.induction_on with
   | empty=> rw [Finset.sum_empty,Finset.sum_empty,tailor_zero]
   | @insert x S hx ih=>
      have h' j e:= hp j (Finset.mem_insert_of_mem e)
      rw [Finset.sum_insert hx, Finset.sum_insert hx,tailor_add h he _ _ _ (hp x (Finset.mem_insert_self ..)) (broadS _ h'), ih h']
lemma diag₁ (h:Amber terrain s A F)(he:0<s)(u i c)(hp:∀ a,tailor F u i c (chalk a)=0)(p:Corn (Keys 1)): tailor F u i c (splat p)=0:=by
   unfold splat; rw [tailor_joint h he]; exact Finset.sum_eq_zero fun j _=> by rw [tailor_M,hp,mul_zero]
   exact fun _ _=>broad_gain (broad.chalk _) _
lemma diag₂ (h:Amber terrain s A F)(he:0<s)(u i c)(hp:∀ a b,tailor F u i c (chalk a*chalk b)=0)(p:Corn (Keys 1)): tailor F u i c ((splat p)^2)=0:=by
   let Q a:=p (0,a) • chalk a
   change tailor F u i c ((∑ a,Q a)^2)=0
   have ht a:broad (Q a):=broad_gain (broad.chalk _) _
   rw [pow_two,Finset.sum_mul,tailor_joint h he _ _ _ _ (fun i hi=> (ht i).mul (show broad (∑ i,Q i) from broad_splat p))]; apply Finset.sum_eq_zero; intro j _; rw [Finset.mul_sum,tailor_joint h he _ _ _ _ (fun x _=> (ht j).mul (ht x))]; apply Finset.sum_eq_zero; intro b _
   rw [show Q j * Q b= p (0,j) • (p (0,b) • (chalk j*chalk b)) by funext d; unfold Q; simp only [Pi.smul_apply,Pi.mul_apply,smul_eq_mul]; ring, tailor_M,tailor_M,hp,mul_zero,mul_zero]
-- centered sign identity on cubes.
lemma diag₃ (h:Amber terrain s A F)(he:0<s)(hb:Spin F)(u i c)(p:Corn (Keys 1))(hv:Aware F) : tailor F u i c (splat p^3)=0:=by
   let a:=axisEquiv.symm u.1
   let r:Signed:= ⟨Equiv.refl _,fun _=>true⟩
   let z:= drift r i-drift r a; let b:=splat p; let c':= b z
   have hh (x): b (spill r a i x)= - b x+c':=by
      have h₁ t: chalk t (spill r a i x) = -chalk t x+chalk t z:= by simpa only [r,tSign,Equiv.refl_apply,↓reduceIte,neg_one_mul] using chalk_S r t a i x
      unfold c' b splat; simp only [Finset.sum_apply,Pi.smul_apply,h₁,smul_eq_mul,mul_add,mul_neg,Finset.sum_add_distrib,Finset.sum_neg_distrib]
   have hw : (b^3 : Cover→ℝ) ∘ spill r a i=((-(1:ℝ)) • (b^3)+(3*c') • (b^2))+(-3*c'^2) • b+c'^3 • (1:Cover→ℝ):=by
      funext x; simp only [Function.comp_apply,Pi.pow_apply, Pi.add_apply,Pi.smul_apply,smul_eq_mul,Pi.one_apply,hh x]; ring
   have hx:= rolledT hb r u.2 c a i (b^3)
   have hy : (coord a,u.2)=u:= by simp only [a, ← coord_map,Equiv.apply_symm_apply]
   simp only [hy,tSign,r,Equiv.refl_apply,↓reduceIte] at hx
   have h':broad b:= broad_splat p
   have h1 c:broad (c • (b^3)):= broad_gain (broad_pow h' 3) (c:ℝ)
   have h2 c:broad (c • (b^2)):= broad_gain (broad_pow h' 2) (c:ℝ)
   rw [show (b^3 : Cover→ℝ) ∘ spill _ a i=_ from hw,tailor_add h he _ _ _ (((h1 _).add (h2 _)).add (broad_gain h' _)) (broad_gain broad.one _),tailor_add h he _ _ _ ((h1 _).add (h2 _)) (broad_gain h' _), tailor_add h he _ _ _ (h1 _) (h2 _),tailor_M,tailor_M,tailor_M,tailor_M,(hv u i c).1,diag₁ h he _ _ _ (hv u i c).2.1,diag₂ h he _ _ _ (hv u i c).2.2 p] at hx
   change tailor F u i c (b^3)=0; linarith

section scan

def tuck : Cover ≃ Shift (Keys 1) where
   toFun x p:= x p.2
   invFun x i:= x (0,i)
   left_inv _:= rfl
   right_inv x:= funext fun ⟨i,j⟩=>by fin_cases i; rfl
lemma plantern_two (h:Blue.Smooth F) (x:Cover)(u:Haze G 2) (v:Run 2) : plantern F u v (tuck x)=petals F (v 0,u 0) (axisEquiv.symm (v 1)) (u 1) x:=by
    unfold petals plantern
    rw [← h (Equiv.swap 0 1) (goose (tuck x) u v)]; congr 1; funext i
    fin_cases i
    · simp [stone,goose, feetP, ←coord_map]; rfl
    simp; rfl
lemma pulseZ (x:Cover)(p:Corn (Keys 1))(t:ℝ): mode (axes (t • p)) (tuck x)=Complex.exp ((t:ℂ)*((splat p x:ℂ)*Complex.I)):=by
   unfold mode; rw [show (∑ i:Keys 1,_)= (t:ℂ)*(splat p x:ℂ) from ?_]; congr 1; ring
   rw [Fintype.sum_prod_type,Fintype.sum_unique]; unfold axes splat; rw [Finset.sum_apply]
   push_cast; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; unfold chalk; simp [tuck]; ring

variable {θ:Corn (Keys 1)}
def blaze (p:Corn (Keys 1))(K: post G 1)(u:Hooks G)(i:Axis)(c:G.ColorIndex)(r:ℕ)(x:Cover)(t:ℝ) :ℂ:= mode (axes (t • p)) (tuck x) * (Complex.I * (splat p x:ℂ))^r * (petals K u i c x:ℂ)
def wavesT (p:Corn (Keys 1))(K:post G 1)(u:Hooks G)(i:Axis)(c:G.ColorIndex)(r:ℕ)(b:ℝ):ℂ:=∑' x,blaze p K u i c r x b
lemma blaze_norm (p:Corn (Keys 1))(K:post G 1)(u:Hooks G)(i:Axis)(c:G.ColorIndex)(r:ℕ)(x:Cover)(t:ℝ): ‖blaze p K u i c r x t‖ = ‖(splat p x)^r * petals K u i c x‖:=by unfold blaze; simp [mode_real _ _ (axes_real _)]
lemma waves_attr (h:Amber terrain s A F)(he:0<s)(u i c)(r)(θ:Corn (Keys 1)) : Summable fun x=> ‖(splat θ x)^r * petals F u i c x‖:= by
    have ht := (summable_norm_iff.mpr (tailor_sum h he u i c (splat θ ^r) (broad_pow (broad_splat _) _)))
    simpa only [Pi.pow_apply] using ht
lemma wavesD (h:Amber terrain s A F)(he:0<s)(u i c)(r)(b:ℝ): HasDerivAt (wavesT θ F u i c r) (wavesT θ F u i c (r+1) b) b := by
    have hv := waves_attr h he u i c (r+1) θ
    have ht : HasDerivAt (fun s : ℝ => (s:ℂ)) 1 b := Complex.ofRealCLM.hasFDerivAt.hasDerivAt
    have H x t: HasDerivAt (blaze θ F u i c r x) (blaze θ F u i c (r+1) x t) t:=by
       unfold blaze; simp_rw [pulseZ]; have ht : HasDerivAt (fun s:ℝ=>(s:ℂ)) 1 t:= Complex.ofRealCLM.hasFDerivAt.hasDerivAt
       convert! ((((ht.mul_const ((splat θ x :ℂ)*Complex.I)).cexp).mul_const _).mul_const _) using 1; ring
    have hs: Summable (fun x=>blaze θ F u i c r x b):=by
       apply Summable.of_norm; simp only [blaze_norm]; exact waves_attr h he u i c r θ
    exact hasDerivAt_tsum_of_isPreconnected (g':=fun i t=>_) hv isOpen_univ isPreconnected_univ (fun x t _=> H x t) (fun x t _=> (blaze_norm ..).le) (show b∈ (Set.univ:Set ℝ) from Set.mem_univ _) hs (Set.mem_univ b)
lemma wars (h:Blue.Smooth F)(p:Corn (Keys 1))(i j b): pictures F i j (axes (b • p)) = wavesT p F (j 0,i 0) (axisEquiv.symm (j 1)) (i 1) 0 b:= by
   unfold pictures readable Laurent.read wavesT; rw [← tuck.tsum_eq]; apply tsum_congr; intro x; dsimp only; rw [plantern_two h]; simp [blaze]
lemma cold (h:Amber terrain s A F)(he:0<s)(p:Corn (Keys 1))(u i c)(b:ℕ): iteratedDeriv b (wavesT p F u i c 0) = wavesT p F u i c b:=by
   induction b with
   | zero=> simp
   | succ b ih=> rw [iteratedDeriv_succ,ih]; exact funext fun x=> (wavesD h he u i c b x).deriv
lemma leveled (p:Corn (Keys 1))(u i c)(r:ℕ) : wavesT p F u i c r 0 = Complex.I ^ r * (tailor F u i c (splat p^r):ℂ):= by
   unfold wavesT tailor; rw [Complex.ofReal_tsum,← tsum_mul_left]; apply tsum_congr; intro x; unfold blaze; simp [mul_pow,mul_assoc]
lemma lawZ (h:Amber terrain s A F)(he:0<s)(hp:Blue.Smooth F)(u:Haze G 2)(v:Run 2)(i:ℕ) (ht:∀ j < i,∀ p:Corn (Keys 1), tailor F (v 0,u 0) (axisEquiv.symm (v 1)) (u 1) (splat p^j)=0): Rays i (pictures F u v ∘ axes) := by
   intro p
   let B (b:ℝ):= pictures F u v (axes (b • p)); let H:= (v 0,u 0); let a:= axisEquiv.symm (v 1); let c:= u 1
   have hb : AnalyticAt ℝ B 0:=by
      let q:=pictures F u v; have ht:Firm (hingeZ s 1) (A*hinges s 1) q:= Firm.of_series (wages h he u v) (hinge_paid he 1)
      apply (((ht.analytic_real ((0:ℝ) • p)).contDiffAt (n:=ω)).comp (f:=fun t:ℝ=>t • p) (0:ℝ) ?_).analyticAt
      fun_prop
   have hu: B=wavesT p F H a c 0:= funext fun b=> wars hp p u v b
   have hh j (hj:j < i) : iteratedFDeriv ℝ j B 0=0:= by
       have he' : iteratedDeriv j B 0=0:= by rw [hu,cold h he,leveled,ht _ hj, Complex.ofReal_zero,mul_zero]
       apply norm_eq_zero.mp; rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,he', norm_zero]
   have he := ((rays_jet hb i).2 hh) 1
   simpa only [smul_eq_mul,mul_one, Function.comp_apply] using he
end scan
lemma infer₃ (h:Amber terrain s A F)(he:0<s)(hp:Blue.Smooth F)(u v)(hx:Aware F)(ht:Spin F): Rays 4 (pictures F u v ∘ axes):= by
    apply lawZ h he hp; intro j hj p; let w:=(v 0,u 0); let i:=axisEquiv.symm (v 1); have hh:=hx w i (u 1); interval_cases j
    · rw [pow_zero]; exact hh.1
    · rw [pow_one]; exact diag₁ h he _ _ _ hh.2.1 p
    · exact diag₂ h he _ _ _ hh.2.2 p
    exact diag₃ h he ht w i (u 1) p hx
lemma infer₂ (h:Amber terrain s A F)(he:0<s)(hp:Blue.Smooth F)(u v)(hw:∀ x c,windsL x c F=0)(ht:Spin F): Rays 2 (pictures F u v ∘ axes):= by
    apply lawZ h he hp; intro j hj p; interval_cases j
    · rw [pow_zero]; exact kail h he hw ..
    rw [pow_one]; exact diag₁ h he _ _ _ (fun x=> wick_white ht h he hw ..) p
end YM.WilsonCoeffUV.Bank.Mosaic
