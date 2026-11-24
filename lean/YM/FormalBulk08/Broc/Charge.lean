import YM.FormalBulk08.Broc.Scan

/-! Bridge between unmasked quadratic jets and the Taylor normalized choice,
supplies enough ray vanishing for rank two affine-null beyond a leading base.
License unused at r≥3. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Broc
open Function Filter Lattice RG Laurent Bloch Exterior Wilson
open Reef Lava Gorge Mesa Shore Lotus Orb Wick Series Jets PowerSeries North Cork City
open Stationary hiding shine Rays
open scoped Topology ENNReal Matrix BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}{s:Signed}{r t e E:ℕ}{A σ:ℝ}

def grillD : Cover≃Shift (Keys 1):= ⟨fun v x=>v x.2,fun x i=>x (0,i),fun _=> rfl,fun x=>funext fun ⟨_,_⟩=>congr_arg x (Prod.ext (Subsingleton.elim ..) rfl)⟩
lemma tend_lens (T : Slopes G)(h:Agate T)(a:hue G) (s:Track): pressLens (pixel T) ![a,a] 1 1 s=∑' u:Cover, mode (axes s) u*(hem T 1 1 a a u:ℂ):= by
   unfold pressLens pixel readable Laurent.read; rw [← Equiv.tsum_eq grillD]; refine tsum_congr fun i=> ?_
   have he: allele T (fun j:Fin (1+1)=>((fun _=>coord 1) j,(fun _=>a) j)) (grillD i)=hem T 1 1 a a i:= by
       unfold hem; exact Eq.trans (congr_arg T (funext (fun j:Fin 2=> by fin_cases j <;> rfl) : packSlot _ _= ![(i,coord 1,a),(0,coord 1,a)] ∘ (Equiv.swap 0 1))) (h _ _)
   rw [show ∀ (j:TypeFace 1), ![j,j]=(fun _=> j) from fun a=> by ext1 i;fin_cases i <;> rfl,show ![a,a]=fun _=>a by ext1 i;fin_cases i <;> rfl];change mode (axes (roads s)) (grillD i)*(allele T (fun j:Fin (1+1)=>((fun _=>coord 1) j,(fun _=>a) j)) (grillD i):ℂ)=_;rw [he];congr 1

def align (z:Track): ℝ→L[ℝ] Track:= (ContinuousLinearMap.id ℝ ℝ).smulRight z
lemma tip_S {T:Picture G 1}(h: ∀ i j,Firm σ A (T i j))(a:hue G)(w:Axis)(p:Track): leapTip T p w ![a,a]=(1/2:ℂ)*iteratedDeriv 2 (pressLens T ![a,a] w w ∘ align p) 0 := by
    rw [iteratedDeriv_eq_iteratedFDeriv]; rw [wired (align p) (by rw [map_zero]; exact priceL h _ _ _),map_zero]; norm_num [leapTip,speedy,Tensor.diagonal,Tensor.coeff,Nat.factorial, align, Function.comp_def]
lemma spit (t:ℝ)(p:Cover)(a:Axis): mode (axes (t • (step a : Track))) p= Complex.exp ((t:ℂ)*(Complex.I * (ch a p:ℂ))) := by
    unfold mode; rw [Finset.sum_eq_single a]; congr 1; simp [axes,ch];ring
    · intro v _ hv; simp [axes,hv]; -- v vs a
    simp
lemma peel_mode (t:ℝ)(p:Cover)(a:Axis): HasDerivAt (fun s:ℝ=> mode (axes (s•(step a:Track))) p) (mode (axes (t • (step a:Track))) p *Complex.I*(ch a p:ℂ)) t:= by
    simp_rw [spit]; have hf : HasDerivAt (fun s:ℝ=> (s:ℂ)) 1 t:= Complex.ofRealCLM.hasFDerivAt.hasDerivAt
    convert! (hf.mul_const (Complex.I*(ch a p:ℂ))).cexp using 1; ring
lemma juicy {T:Slopes G}(h:Purse T)(b k:hue G)(f:Cover→ℂ)(a:Axis)(m:ℕ)(hf: f=fun x:Cover=> Complex.I^m*((hem T 1 1 b k x*(ch a x)^m:ℝ):ℂ)) :
    ∀ t, HasDerivAt (fun s:ℝ=> ∑' p:Cover, mode (axes (s•(step a : Track))) p * f p) (∑' p:Cover, mode (axes (t • (step a : Track))) p*(Complex.I*(ch a p:ℂ)*f p)) t := by
    intro t; let W p (s:ℝ):= mode (axes (s•(step a : Track))) p*f p; let r p:= Complex.I*(ch a p:ℂ)*f p; let U p (t:ℝ):= mode (axes (t•(step a : Track))) p*r p
    have he p s: HasDerivAt (W p) (U p s) s:= by convert! ((peel_mode s p a).mul_const (f p)) using 1; unfold U r;ring
    have hp: Summable f:= hf ▸ (((Complex.ofRealCLM).summable (h.sum 1 1 b k ((Pad.ch a).pow m))).mul_left _)
    have hz p s: ‖U p s‖=‖r p‖:= by unfold U; rw [norm_mul,mode_real _ _ (axes_real _), one_mul]
    have hr: r=(fun x=> Complex.I^(m+1)*((hem T 1 1 b k x*(ch a x)^(m+1):ℝ):ℂ)):= by funext x; unfold r;rw [hf];push_cast;ring
    have hR: Summable r:= hr ▸ ((Complex.ofRealCLM.summable (h.sum 1 1 b k ((Pad.ch a).pow (m+1)))).mul_left _)
    have hx: Summable (fun p=> W p 0):= by unfold W;simp [axes_origin,hp]
    exact hasDerivAt_tsum_of_isPreconnected hR.norm isOpen_univ isPreconnected_univ (fun i x _=> he i x) (fun i x _=> (hz i x).le) (Set.mem_univ 0) hx (Set.mem_univ t)
lemma lemon (T: Slopes G)(H:Agate T)(hw:Purse T)(a:hue G):
     2 * leapTip (pixel T) (step 0) 1 ![a,a] = -(value a T:ℂ):= by
    let b (i:Cover):=hem T 1 1 a a i; let c:=ch 0
    let f i:ℂ:= b i; let g i:= Complex.I*(c i:ℂ)*f i; let F (f:Cover→ℂ)(s:ℝ):= ∑' p, mode (axes (s•(step 0:Track))) p * f p
    have hh: deriv (F f)= F g:= funext fun t=>(juicy hw a a f 0 0 (by unfold f b; ext; simp) t).deriv
    have hx:deriv (F g)= F (fun i=> Complex.I*(c i:ℂ)*g i):= funext fun t=> (juicy hw a a g 0 1 (by funext i; unfold g f c b;push_cast;ring) t).deriv
    have hy : pressLens (pixel T) ![a,a] 1 1 ∘ ⇑(align (step 0))= F f:= funext fun t=> tend_lens T H _ _
    obtain ⟨σ,A,hs,h⟩:=hw; rw [tip_S (pitch _ h hs),hy,iteratedDeriv_succ,iteratedDeriv_one, hh, hx, ←mul_assoc]; norm_num
    unfold F; simp_rw [zero_smul,axes_origin,mode_constant,one_mul]; unfold value mir net; rw [Complex.ofReal_tsum,← tsum_neg]; apply tsum_congr; intro x
    change Complex.I*_ *_= -(((b x)*(c x*c x):ℝ):ℂ); unfold g f; push_cast; linear_combination ((c x:ℂ)^2*(b x:ℂ))*Complex.I_mul_I
end YM.FormalBulk08.Broc
