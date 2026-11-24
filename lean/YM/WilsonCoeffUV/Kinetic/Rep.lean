import YM.WilsonCoeffUV.Kinetic.Exact
import YM.Next.STATIONARY.Shape.Scaled
/-!
# Read zero-slope from the path-certified affine input

True Width (not continuity assumption about an orbit).
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank.Mosaic
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Near Stationary PowerSeries Roam Asymptotics
open scoped ContDiff Topology BigOperators
variable {n:Side}{G:Gauge}{s A B:ℝ}{R: PathData G}{p:Clip}{e:ℕ}

abbrev tipLoop (p:Clip)(R:PathData G) : post G 1:= breast R p 2 2
lemma loop_axis (K:R.Bounds p s A B) (n:Side): rye (turnSeries R.loop (m:=n)) 2= lagoon (tipLoop p R) n:=by
    have he:front R p n 2 2= lagoon (tipLoop p R) n:= frontr K 2 1 n; rw [front,Pi.add_apply,Pi.add_apply] at he; unfold sprig at he; rwa [shine_dark (by omega), zero_add,zero_add,shine_lit] at he
lemma skies (K:R.Bounds p s A B)(n:Side): Recorded (pictures (tipLoop p R)) (turnSeries R.loop (m:=n)) 0:=by
    let a:=steep s; have hA:0<a:= by exact div_pos K.width (by norm_num)
    obtain ⟨c,hc⟩:= moon_bill G 2 2 a hA.le
    have H': Amber terrain a _ (tipLoop p R):= frontFee K 2 2 c hc
    let F:=tipLoop p R; let T:=turnSeries R.loop (m:=n)
    refine (record_exact ..).2 ?_; intro v x y
    rw [note_map T]; unfold enlarge; have he:= polar F v x y H' hA
    rw [← he]; congr 2; ext1 i; have hv:= congr_fun (loop_axis K n) i; rw [fiscal_vol] at hv; exact congr_arg ((↑) :ℝ→ℂ) hv
lemma basal (K:R.Bounds p s A B)(u v):
    pictures (tipLoop p R) u v ∘ axes= filing R u v ∘ axes:=by
    let Z :ℕ→Side:=fun i=> ⟨i+1,by omega⟩; have hZ :Tendsto (fun i=> (Z i).val) atTop atTop:= by simpa [Z] using! Filter.tendsto_add_atTop_nat 1
    funext x; obtain ⟨t,y,hp,hy⟩:= fleet Z hZ (axes x) (axes_real x)
    obtain ⟨c,hc⟩:= moon_bill G 2 2 (steep s) (by exact div_nonneg K.width.le (by norm_num))
    have H:=frontFee K 2 2 c hc
    let F i:=turnSeries R.loop (m:=Z i); have ht i: Recorded (pictures (tipLoop p R)) (F i) (cents (Z i)*0):=by rw [mul_zero]; exact skies K _
    have U:=filing_ready R K; have hv i: Recorded (filing R) (F i) (cents (Z i)*0):=by rw [mul_zero]; exact U.2 _
    exact tendsto_nhds_unique (harvest (fun i j=> Firm.of_series (wages (F:=tipLoop p R) (t:=1) H (div_pos K.width (by norm_num)) i j) (hinge_paid (div_pos K.width (by norm_num)) _)) ht tendsto_const_nhds _ _ _ hp hy u v) (harvest (fun i j=>(U.1 i j).1) hv tendsto_const_nhds _ _ _ hp hy u v)
lemma azurF (K:R.Bounds p s A B)(v:G.ColorIndex): azur (tipLoop p R) v=0:=by
    let Z:=tipLoop p R; let X:Haze G 2:=![v,v]; let i:Run 2:= ![coord 1,coord 1]; let T:= pictures Z X i
    have hu:T ∘ axes= filing R X i ∘ axes:=basal K _ _
    have he:Rays 4 (T ∘ axes):=hu.symm ▸ filing_aux R K _ _
    let q : Corn (Keys 1):=Pi.single (0,0) 1
    let f (x:ℝ):=T (axes (x • q))
    obtain ⟨a,H⟩:=moon_bill G 2 2 (steep s) (div_nonneg K.width.le (by norm_num)); have hp:=div_pos K.width (by norm_num:(0:ℝ)<4); have h:=frontFee K 2 2 a H
    have hy:∀ x:ℝ,f x=wavesT q Z (coord 1,v) 1 v 0 x:=by intro x; have H:Blue.Smooth Z:= (frontage K 2).symr 2; have he:= wars H q X i x; simpa only [show i 0=coord 1 from rfl, show i 1=coord 1 from rfl,←coord_map,Equiv.symm_apply_apply] using! he
    have hz : Rays 4 f:= by intro i; have h':= he (i • q); simp_rw [smul_smul] at h'; exact h'
    have hS: AnalyticAt ℝ f 0:=by
        apply AnalyticAt.comp (g:=T ∘ axes) (f:=fun x:ℝ=>x • q) (x:=0) ((Firm.of_series (wages (F:=Z) (t:=1) h hp X i) (hinge_paid hp _)).analytic_real (_:Corn (Keys 1)))
        fun_prop
    have hm:iteratedDeriv 2 f 0=0:=by rw [iteratedDeriv,(rays_jet hS _).1 hz 2 (by omega)]; rfl
    have hx:splat q=chalk 0:=by
        funext x; unfold splat; simp only [Finset.sum_apply]; rw [Finset.sum_eq_single 0]; · simp [q]
        · intro i _ hi; simp [q,hi]
        simp
    rw [funext hy,cold h hp,leveled,hx] at hm; unfold azur; rw [←pow_two, show tailor Z _ _ _ _=0 from ?_,neg_zero];
    simp [*] at hm
    exact hm
lemma pricedR (K:R.Bounds p s A B)(u:G.Simple): readSun (tipLoop p R)=0:=by rw [read_azur _ (colI u),azurF K]
end YM.WilsonCoeffUV.Bank.Mosaic
