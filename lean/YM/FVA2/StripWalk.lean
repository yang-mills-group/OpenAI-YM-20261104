import YM.FVA2.Sparks
import YM.Work.G03
import YangMills.WilsonProof.NativeSupport.YM.MS.Heat.Park
/-!
# Taylor test of a free line observable on radial potentials

`wire` is the continuum FREE HOLONOMY sampling of a plane wave.
Input link logs of the LPT UV symbol are MIDPOINT instead (without this line integral).
Can compare leading jets despite arbitrary engineering weight, by the per-leg factor.
No singular division on lanes with momentum perpendicular to the link.
-/
set_option autoImplicit false
set_option maxHeartbeats 850000
noncomputable section
namespace YM.FVA2.Plate
open Filter Topology Set Function MeasureTheory Maxwell Tensor
open Wilson Lattice MS MS.Native MS.Native.Chart MS.Native.Wilsonian MS.Native.Studio
open MS.Native.Orient MS.Native.Sew MS.Native.Draft MS.Lifting MS.Landau MS.Landau.Detect MS.Koszul MS.Book
open MS.Cylinder MS.Plane MS.Tone MS.Tone.Frame MS.Color
open RG PertExtension MvPolynomial
open Next.Rank Next.Rank.CellsInt Next.Rank.Spindle MS.Theater
open scoped Topology Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G:Gauge}{n k:ℕ} (i j l:Axis)(c:G.ColorIndex)
local notation "E"=>E4
local notation "W"=>Lattice.Cover

def rope (u:Feet G n) (i:Axis)(x:W) : G.Color:= east i (diagonal (u.val i)) (mapZ x)
def corner {V:Type*}[AddCommGroup V] (v:Axis→W→V) (L:PlaqAxes)(x:W): V:= v L.val.1 x+v L.val.2 (x+Lattice.step L.val.1)-v L.val.1 (x+Lattice.step L.val.2)-v L.val.2 x
lemma corner_sub {V:Type*}[AddCommGroup V](A B:Axis→W→V)(L:PlaqAxes)(x:W): corner (A-B) L x=corner A L x-corner B L x:= by unfold corner; simp only [Pi.sub_apply]; abel
lemma corner_scale {V:Type*}[AddCommGroup V][Module ℝ V](A:Axis→W→V)(p:ℝ)(L:PlaqAxes)(x:W): corner (p • A) L x=p • corner A L x:= by simp only [corner, Pi.smul_apply,smul_add,smul_sub]
private lemma rcwd (u v:Feet G n) : rope (u-v) = rope u-rope v := by funext i x; apply congr_fun (east_sub (f:=diagonal (u.val i)) (g:=diagonal (v.val i)) i ((diag_smooth _ 1).continuous) ((diag_smooth _ 1).continuous)) 
private lemma scale_r (u : Feet G n)(p:ℝ): rope (p • u)=p • rope u := by funext i x; apply congr_fun (east_scale ..) -- implicit
lemma rope_g (h:Head G (n+1))(L:PlaqAxes)(x:W): corner (rope (gradS G n h)) L x=0:= by
   let f:= diagonal (h.val ()); have he i x: rope (gradS G n h) i x=f (mapZ (x+Lattice.step i))-f (mapZ x):= by
       rw [ rope, show diagonal ((gradS G n h).val i)= _ from workL (YM.basis i) h (), show Analysis.D (YM.basis i) f= grad i f from rfl, CellsInt.lights f (diag_smooth _ 1) i, mapZ_step ]; rfl
   simp_rw [corner,he]; rw [add_right_comm x (Lattice.step L.val.1)]; abel
lemma clear_grad (u:Feet G n) (L:PlaqAxes)(x:W): corner (rope (carve _ _ u)) L x=corner (rope u) L x:= by rw [carveΩ,rcwd,scale_r,corner_sub,corner_scale,rope_g,smul_zero,sub_zero]
lemma rope_zero_grade (u:Feet G 0) (L:PlaqAxes)(x:W): corner (rope u) L x=0:= by
   rw [← clear_grad,show carve G 0 u=0 from (Submodule.mem_bot ℝ).mp (weightT G ▸ house u)]
   simp [corner,rope,east,Tensor.diagonal]
open Complex (I)
def cost (p:QP)(x:E) : ℂ:= Tone.bill p (Theater.out x)
lemma cost_eq (p:QP)(x:E) : cost p x=Complex.exp (I*(inner ℝ (fixF p) x:ℝ)):= by
   have he : inner ℝ (fixF p) x = Momentum.pairing p (out x):= by rw [real_inner_comm x,EuclideanSpace.inner_eq_star_dotProduct,star_trivial]; rfl
   rw [he]; rfl
private lemma load_smooth (p:QP) : ContDiff ℝ ∞ (fun z:ℝ × E=> cost (z.1 • p) z.2):= by
   simp_rw [cost_eq,map_smul]; exact ContDiff.cexp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (show ContDiff ℝ ∞ (fun z:ℝ × E=> inner ℝ (z.1 • fixF p) z.2) from ContDiff.inner (𝕜:=ℝ) (contDiff_fst.smul contDiff_const) contDiff_snd)))
private lemma load_b (p:QP)(x:E) : ∀ t:ℝ,cost (t • p) x=Complex.exp ((I*(inner ℝ (fixF p) x:ℝ))*t):= by intro t; rw [cost_eq,map_smul, real_inner_smul_left]; push_cast; congr 1; ring
lemma powerSeries_cost (p:QP)(x:E)(k:ℕ) : reading k (fun t:ℝ=> cost (t • p) x)= hitϑ k * ( ↑(amount k * (inner ℝ (fixF p) x)^k):ℂ ):= by
    let c : ℂ:= I*(inner ℝ (fixF p) x:ℝ); let f (t:ℝ):= cost (t • p) x; have he : deriv f=fun x=>c*f x:= by
        funext t; simp_rw [f,load_b]; exact Eq.trans (((Complex.ofRealCLM.hasFDerivAt.hasDerivAt (x:=t)).const_mul c).cexp.deriv) (by dsimp [c]; ring) -- cexp order
    have hh (k:ℕ): iteratedDeriv k f 0= c^k:= by
       induction k with
       | zero=> simp [f,cost]
       | succ k ih=> rw [iteratedDeriv_succ', he, iteratedDeriv_const_mul_field, ih,pow_succ'];
    unfold reading; rw [hh]; simp_rw [c,mul_pow,Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_pow, hitϑ,amount]; ring

def skim (p:QP)(i:Axis)(x:W) : ℂ:= east i (cost p) (mapZ x)
lemma skim_read (p:QP)(i:Axis)(x:W)(k:ℕ): ContDiff ℝ ∞ (fun t:ℝ=>skim (t • p) i x) ∧
   reading k (fun t:ℝ=>skim (t • p) i x)=∫ s:ℝ in 0..1, reading k (fun t:ℝ=>cost (t • p) (mapZ x+s • basis i)):= by
   let f (v:ℝ×ℝ) := cost (v.2 • p) (mapZ x+v.1 • basis i); have he: ContDiff ℝ ∞ f:= (load_smooth p).comp (show ContDiff ℝ ∞ (fun v:ℝ×ℝ=> (v.2,mapZ x+v.1 • basis i)) by fun_prop)
   let μ:Measure ℝ:= volume.restrict (Ioc 0 1); have hQ : MS.Heat.Cour μ := ⟨Icc 0 1,isCompact_Icc,(ae_restrict_mem measurableSet_Ioc).mono fun p hp=>Ioc_subset_Icc_self hp⟩
   let _ : IsFiniteMeasure μ:= inferInstanceAs (IsFiniteMeasure (volume.restrict (Ioc (0:ℝ) 1)))
   have hv := MS.Heat.Lot μ hQ he; simp_rw [skim,east,intervalIntegral.integral_of_le (zero_le_one)]; refine ⟨hv.contDiff,?_⟩
   have h' : iteratedDeriv k (fun t=> ∫ s,f (s,t)∂μ) 0=∫ s,iteratedDeriv k (fun t=> f (s,t)) 0∂μ:=by rw [iteratedDeriv_eq_iteratedFDeriv,hv.identity,ContinuousMultilinearMap.integral_apply (hv.integ _ _)]; simp_rw [← iteratedDeriv_eq_iteratedFDeriv]
   change (Nat.factorial k:ℝ)⁻¹ • iteratedDeriv k (fun t=>∫ s,f (s,t)∂μ) 0 = _; rw [h', ← integral_smul]

lemma walk_read (p:QP)(c d:G.ColorIndex)(k:ℕ) (x:W) (i j:Axis) :
    reading k (fun t:ℝ=> (cl G c d:ℂ) * if i=j then skim (t • p) j x else 0)=
        hitϑ k * ( (rope (speak k i p (cl G c)) j x d:ℝ):ℂ ):= by
   by_cases h : i=j; swap
   · rw [show rope (speak k i p (cl G c)) j x=0 by simp [rope,east,speak, Theater.away _ _ _ (Ne.symm h),Tensor.diagonal]]; simp [reading,h]
   subst j
   let F (x:E):= amount k * (inner ℝ (fixF p) x)^k; let D:= α d
   have hs : diagonal ( (speak k i p (cl G c)).val i )= fun z:E=> F z • cl G c:= by
       funext z; unfold Tensor.diagonal F speak; rw [wearing,Finset.prod_const, Finset.card_univ,Fintype.card_fin]; rw [mul_smul]
   conv_rhs => rw [← α_at (G:=G) d]
   unfold rope; rw [hs]; simp only [east]; -- beware unfolding skim east? dependent
   rw [← (α d).intervalIntegral_comp_comm (f:=fun t:ℝ=> F (mapZ x+t • basis i) • cl G c) (Continuous.intervalIntegrable (μ:=volume) (by unfold F; fun_prop) 0 1)]
   simp only [map_smul,α_at,if_true, read_const, (skim_read p i x k).2]; simp_rw [powerSeries_cost]
   rw [ intervalIntegral.integral_const_mul ]; change _=( hitϑ k ) * ( ↑(∫ s:ℝ in 0..1,F (mapZ x+s • basis i) * cl G c d):ℂ )
   rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal, Complex.ofReal_mul]; unfold F; ring

def delay (p:QP)(i:Axis): ℂ := (Tone.bill p (Tone.Frame.z i))⁻¹ * skim p i 0
@[simp] lemma delay_zero (i:Axis): delay 0 i=1:= by simp [delay,skim,east,cost]
lemma delay_smooth (p:QP)(i:Axis): ContDiff ℝ ∞ (fun t:ℝ=> delay (t • p) i):= ((bankForm p (z i)).inv (fun _=>nonz _ _)).mul (skim_read p i 0 0).1
lemma skim_m (p:QP)(i:Axis)(x:W) : skim p i x= delay p i * Tone.bill p (Tone.embed x+z i):= by
   rw [delay,rightadd]; have h : skim p i x=Tone.bill p (Tone.embed x)*skim p i 0:=by
      unfold skim east; rw [← intervalIntegral.integral_const_mul]; have hx : Theater.out (mapZ x)= embed x:=rfl; simp_rw [cost,map_add,rightadd,hx,show mapZ 0=0 from by ext; simp [mapZ] ]; simp
   nth_rw 1 [h]; field_simp

def credit (a:Beast G)(i:Axis)(c:G.ColorIndex)(p:QP)(j:Axis)(x:W): ℂ:= ((cl G c a.2:ℝ):ℂ)*(if i=j then skim p j x else 0)
lemma credit_eq (a:Beast G)(i:Axis)(c:G.ColorIndex)(p:QP)(x:W)(j:Axis):
  credit a i c p j x=delay p i * Tone.paywave (waveForm p i c) (formAt j a.2 x):= by
   unfold credit; rw [ show paywave (waveForm p i c) (formAt j a.2 x)= _ from please (x,j) i c a.2 p ]; by_cases ht:i=j; swap; · simp [ht,matchA] -- if
   subst j; simp [skim_m,matchA,cl]; by_cases h:a.2=c <;> simp [h]
lemma pay_tr (p:QP)(x:W)(k:G.ColorIndex)(i j:Axis)(c:G.ColorIndex)(y:W): paywave (waveForm p i c) (formAt j k (x+y))= Tone.bill p (Tone.embed x)*paywave (waveForm p i c) (formAt j k y):=by
   unfold paywave; simp only [bornv,formAt,emb_add, add_assoc,waveForm,rightadd]; ring
lemma beacon_read (a:Beast G)(i:Axis)(c:G.ColorIndex)(p:QP):
    delay p i * beacon a (waveForm p i c)=corner (credit a i c p) a.1.plaq a.1.offset:= by
   let x:= a.1.offset; let s:= a.1.plaq; let k:= a.2; let u:=waveForm p i c; let g(x:Edge W):= paywave u (formAt x.2 k x.1)
   have hh : shine s x k u=corner (fun j x=> paywave u (formAt j k x)) s x:= by
       unfold corner; rw [ shine,frontPiece ]; dsimp only [u]; simp_rw [pay_tr] -- Pow test?
       have hF : front s= ![(0,s.val.1),(step s.val.1,s.val.2),(step s.val.2,s.val.1),(0,s.val.2)]:= by funext j; fin_cases j <;> simp [front,loadC,idRail]
       rw [hF]
       change Tone.bill p (embed x) * (g (0,s.val.1)+g (step s.val.1,s.val.2)-g (step s.val.2,s.val.1)-g (0,s.val.2))=_
       have hx (i:Axis): g (x,i) = Tone.bill p (embed x)*g (0,i):= by unfold g; dsimp; convert pay_tr p x k _ _ _ 0 using 1; rw [add_zero]; -- name add_zero
       change _= g (x,s.val.1)+bill _ _*g (step s.val.1,s.val.2)-bill _ _ * g (step s.val.2,s.val.1)-g (x,s.val.2); rw [hx,hx]; ring
   rw [show beacon a _= _ from hh]; simp only [corner,credit_eq]; ring

lemma credit_curve (a:Beast G)(i:Axis)(c:G.ColorIndex)(p:QP)(k:ℕ) :
    reading k (fun t:ℝ=> delay (t • p) i * beacon a (waveForm (t • p) i c))= hitϑ k * ( (corner (rope (speak k i p (cl G c))) a.1.plaq a.1.offset a.2:ℝ):ℂ ):= by
   have hh j x : ContDiff ℝ ∞ (fun t:ℝ=>credit a i c (t • p) j x):= by unfold credit; by_cases h:i=j; simp only [h,if_true]; exact contDiff_const.mul (skim_read p j x 0).1; simp [h]; exact contDiff_const
   have ht j x: reading k (fun t:ℝ=> credit a i c (t • p) j x)=_:= walk_read p c a.2 k x i j
   have hr (f g:ℝ→ℂ)(hf:ContDiff ℝ ∞ f)(hg:ContDiff ℝ ∞ g) : reading k (fun t=> f t-g t)= reading k f-reading k g:=by obtain he:= (read_add (f:=f) (g:=fun t=> (-1)*g t) (j:=k) hf (contDiff_const.mul hg)); rw [ read_const ] at he; simpa only [neg_one_mul,sub_eq_add_neg] using he
   simp_rw [beacon_read]; unfold corner; simp_rw [hr _ _ ((ContDiff.add (hh ..) (hh ..)).sub (hh ..)) (hh ..),hr _ _ ((hh ..).add (hh ..)) (hh ..), read_add (hh ..) (hh ..),ht]; simp only [PiLp.add_apply,PiLp.sub_apply]; push_cast; ring
end YM.FVA2.Plate
