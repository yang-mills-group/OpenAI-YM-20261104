import YangMills.WilsonProof.NativeSupport.YM.MS.Menus.Glyph
/-!
# Tune data for every order-at-label

Charges polynomial in log at each order, not necessarily power-counting choices.
 Marks allowed at this level include exact shifts at any t power with given log family. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Menus
open Function Filter Set Finset Plane Koszul Cylinder Lab Taylor Lattice Native Bare Focus Landau Momentum Orient Draft Sew Native.Chart Tone Tone.Frame
open Color Lifting Local Local.Physical Submodule Logarithm High Ghost
open Book Convolve Program Flux Native.Wilsonian Native.Studio Paint
open Complex (I)
open scoped Topology ContDiff
variable {G:Gauge}{B: Deck G} (V : LitBook B)(p:Team) {d:ℕ}
-- order-k part of exact primitive
structure Power (G:Gauge) where
   input : ℝ→ Dot G Cover
   polyn : Ready input
   actual (i:ℝ): Tuned (input i) (-1)
   calm (i:ℝ): Colorless (input i)
   allowance : ℕ -- upper rank
   ranks (i:ℝ): Limit (input i).val allowance
instance : Zero (Power G):= ⟨{input:=0, polyn:=Ready.zero, actual:=fun _=>Tune.zero, calm:=fun _ _=>map_zero _, allowance:=0, ranks:=fun _ _ _=>rfl}⟩
structure Tact (B:Deck G)(d:ℕ) where
    register : Glyph B d → Polynomial ℝ
    proof : Power G
abbrev Acts (B:Deck G)(d:ℕ):=ℕ→ Tact B d
instance : Zero (Tact B d):=⟨⟨0,0⟩⟩

variable (A:Acts B d)
-- lattice physical series and accompanying exact

def oil (A:Acts B d)(j:Glyph B d) (i:ℕ)(x:ℝ):ℂ:= (((A i).register j).eval x:ℝ)
def rent (x:ℝ) (i:ℕ): Dot G Cover:= ∑ g:Glyph B d, ∑ d∈antidiagonal i, oil A g d.1 x • Glyph.preamble V p g x d.2
def prim (x:ℝ)(i:ℕ): Dot G Cover:= (A i).proof.input x
def motto (x:ℝ): T (Dot G Cover):= actB (Spectrum G) (prim A x)+blocks (Spectrum G) (style G p x) (prim A x)
def score (x:ℝ): T (Dot G Cover):= rent V p A x + motto p A x
lemma sky (k:ℕ)(x:ℝ): motto p A x k= (Spectrum G).Lap ((A k).proof.input x) + (∑ i∈antidiagonal k,(Spectrum G).touch (style G p x i.1) ((A i.2).proof.input x)):=rfl
lemma markSense (x:ℝ) : score V p A x= rent V p A x+ steadyE (Spectrum G) (style G p x) (prim A x):= rfl
lemma steady (k:ℕ) (P:Acts B d) (H:∀ i, i≤ k→ A i=P i) (x:ℝ): score V p A x k=score V p P x k := by
    simp_rw [score,Pi.add_apply,sky,rent, H k k.le_refl]
    apply congr_arg₂ (·+·)
    · apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j hj; unfold oil; rw [H j.1 (by obtain h:=mem_antidiagonal.mp hj; omega)]
    congr 1; apply Finset.sum_congr rfl; intro j hj; rw [H j.2 (by obtain h:=mem_antidiagonal.mp hj; omega)]
lemma poses (x:ℝ)(i:ℕ): Tuned (rent V p A x i) 0:= Tune.sum _ fun g _=> Tune.sum _ fun j _=> (Glyph.pre_c V p g x j.2).cash _ (show star (oil A g j.1 x)=_ from by simp [oil])
lemma appears (x:ℝ)(i:ℕ): Colorless (rent V p A x i):= Colorless.csum _ fun g _=> Colorless.csum _ fun j _=> (Glyph.pre_lit V p g x j.2).smul _
lemma rentReady (i:ℕ): Ready (fun x=> rent V p A x i):= value_sum _ (fun j _=> value_sum _ (fun k _=> pc_ready (c:=oil A j k.1) ⟨_,Ready.got _,rfl⟩ (Glyph.pre_ready V p j k.2)))
lemma rentLimit (x:ℝ)(i:ℕ): Limit (rent V p A x i).val (i+d):= by unfold rent; simp_rw [sum_stack]; exact Limit.sum _ (fun g _=> Limit.sum _ (fun k hk=> ((Glyph.pre_cost V p g x k.2).smul _).up (by obtain he:= Finset.mem_antidiagonal.mp hk; have hv:= Glyph.memory g; omega)))

lemma colorRoot (x:ℝ)(i:ℕ): Colorless (motto p A x i):= by
   rw [sky]; apply Colorless.add; · exact fun u=> by rw [originLap,(A i).proof.calm x]
   exact Colorless.csum _ (fun j _ u=> by rw [rootLap,(A j.2).proof.calm x,(core_circle G p).settled j.1 x u])
lemma pretty (x:ℝ)(i:ℕ): Tuned (motto p A x i) 0:= by
    rw [sky]; apply Tune.add; · exact (Tune.lapped (Spectrum G) charged ((A i).proof.actual x))
    exact Tune.sum _ (fun j _=> Tune.touch (Spectrum G) charged ((core_circle G p).actual j.1 x) ((A j.2).proof.actual x))
private abbrev X0 (G: Gauge):= Dot G Cover
private def Xreal (V:X0 G→ₗ[ℂ] X0 G→ₗ[ℂ] X0 G) : X0 G →ₗ[ℝ] X0 G→ₗ[ℝ] X0 G where
   toFun x:= (V x).restrictScalars ℝ
   map_add' x y:= LinearMap.ext (fun z=>by simp)
   map_smul' c F:= by
       apply LinearMap.ext; intro z; change V (c • F) z= c • V F z; rw [show c • F=(c:ℂ) • F from rfl,map_smul,LinearMap.smul_apply]; rfl
lemma flows (i:ℕ): Ready (fun x=> motto p A x i):= by
    simp_rw [sky]; refine Ready.add_point (Ready.linear (f:= (A i).proof.input) ((A i).proof.polyn) ((Spectrum G).Lap.restrictScalars ℝ)) (value_sum _ (fun j _=>?_)); exact Ready.pair (Xreal ((Spectrum G).touch (P:=Cover))) ((core_circle G p).tag j.1) (A j.2).proof.polyn

def fringe (i:ℕ): ℕ:= Finset.sup (Finset.Iic i) fun j=> (A j).proof.allowance
lemma rangeFr (i j:ℕ)(hi : j ≤ i)(x:ℝ): Limit ((A j).proof.input x).val (fringe A i):= (A j).proof.ranks x|>.up (Nat.cast_le.mpr (Finset.le_sup (f:=fun j=>(A j).proof.allowance) (Finset.mem_Iic.mpr hi)))
lemma stuff (x:ℝ)(i:ℕ): Limit (motto p A x i).val (i+ (fringe A i)):= by -- syntax
    rw [sky]; refine Limit.add (by exact (lapLimit (rangeFr A i i i.le_refl x)).up (by omega)) ?_; rw [sum_stack]; exact Limit.sum _ (fun j hj=> (rootLimit (style_limit p x G j.1) (rangeFr A i j.2 (by obtain h:=Finset.mem_antidiagonal.mp hj; omega) x)).up (by obtain h:=Finset.mem_antidiagonal.mp hj; omega))
lemma range (x:ℝ)(i:ℕ): Limit (score V p A x i).val (i+d+fringe A i):= Limit.add ((rentLimit V p A x i).up (by omega)) ((stuff p A x i).up (by omega))
lemma decor : Circle G (score V p A) false 0 where
    stance0 _ _ h:= False.elim (Bool.noConfusion h)
    actual i x:= (poses V p A x i).add (pretty p A x i)
    settled i x:=(appears V p A x i).add (colorRoot p A x i)
    tag i:= (rentReady V p A i).add (flows p A i)
    room i:=⟨i+d+fringe A i,fun x=>by exact_mod_cast (range V p A x i)⟩
end YM.MS.Menus
