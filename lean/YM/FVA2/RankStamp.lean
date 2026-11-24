import YM.FVA2.WilsonSource
import YM.FormalOPE.RG10.FiniteTop
/-!
# Shift (preclude even hidden negative powers)
Before coupling reexpression. Held at given period and horizon, true with any translations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Source
open Filter Topology Set PowerSeries Function
open PertExtension PertExtension.Series PertExtension.Series.Radial PertExtension.Chart
open FormalOPE.RG10 FormalOPE.RG10.MultiGauge FormalOPE.RG10.BlockGauge Trans Wilson TreeBasis FormalOPE.RG10.MultiGauge.Splice
open Lattice MS MS.Native MS.Native.Chart MS.Native.Wilsonian MS.Native.Studio MS.Native.Orient MS.Native.Sew MS.Local MS.Landau MS.Menus MS.Koszul MS.Book MS.Cylinder MS.Plane MS.Cylinder.Lab MS.Cylinder.Taylor
open MS.Tone MS.Color MS.Orbit MS.Puff MS.Puff.Engine MS.Swirl MS.Orbit.LogReal Based MeasureTheory PairCoords Boson Modes
open scoped Topology Classical ContDiff Matrix.Norms.Frobenius
local notation "W"=>Lattice.Cover
variable {G:Gauge} {n: Side}{d h:ℕ}{F: Dot G Lattice.Cover} {f:Weights G} (hv:Brand F f)
local notation "Fκ"=>Wilson.Field G n
local notation "Pκ"=> (LMap G n)

section
variable {U A:Type} {v:ℤ} {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
lemma FromShade (X: Cyl U ℂ)(h:From X.val v)(T:A→U→ℂ): From (shade T X) v:= by
    intro l he; rw [← enough l (F:=shade T X) rfl,← mod_ink (h:= (l.length:ℤ)), show model (l.length:ℤ) X=0 from ?_,map_zero]; rfl
    apply Subtype.ext; ext k; by_cases hk:(k.length:ℤ)=l.length; exact (enough k hk).trans (h k (by omega)); exact strange k hk
omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private lemma replicate_mot (v:E) (l:List Unit): Boson.mot (fun _:Unit=>v) l=fun _=>v:= by
    funext i; induction l with| nil=>exact Fin.elim0 i | cons j l ih=> exact Fin.lastCases (motive:=fun i=>Fin.snoc (α:=fun _=>E) (Boson.mot (fun _:Unit=>v) l) v i=v) (by simp) (fun i=> by rw [Fin.snoc_castSucc]; exact ih i) i
lemma jet_down {f:E→ℝ} (h:germ f)(x:E) (he:From (ink (fun _:Unit=>x) f) d) (i:ℕ)(hi:i<d): jet f i x=0:= by
    let l:= List.replicate i (); have ht:l.length=i:= List.length_replicate
    let z(v:ℕ):=(iteratedFDeriv ℝ v f 0) (fun _=> x)
    have hb:z i=0:= by obtain hx:=entry (fun _:Unit=>x) f h l; rw [he l (by omega), replicate_mot ] at hx; apply Complex.ofReal_injective; rw [← ht]; exact hx.symm -- zero cast
    exact mul_eq_zero_of_right _ hb
end
variable (x:Site n)

abbrev intoTree (G:Gauge)(n:Side) : Wilson.Field G n →L[ℝ] City G (Site n):= ( Trans.coverL G n ∘ₗ TreeBasis.enter G (staple n)).toContinuousLinearMap
def outTree (G:Gauge)(n:Side): Orb.Dir G n →L[ℝ] City G (Site n):= intoTree G n ∘L (accountBasis G n).symm.toContinuousLinearMap
lemma tree_read : Wilson.treed (put f x) = ((put f x) ∘ nation) ∘ intoTree G n:= by
    ext v; unfold Wilson.treed; simp only [Function.comp_apply]; rw [Trans.assemble_exp]; rfl
lemma orbit_read : (Orb.restrictedO (put f x)) ∘ expLinks G (Orb.Cotree n)= ((put f x) ∘ nation) ∘ outTree G n := by
    have hx:treed (put f x)=_ := observe_tree (put f x); rw [tree_read x] at hx; funext v; change _=(((put f x) ∘ nation) ∘ intoTree _ _) _; rw [hx]; change _=(Orb.restrictedO (put f x)) (expLinks _ _ (accountBasis G n ((accountBasis G n).symm v))); rw [ContinuousLinearEquiv.apply_symm_apply]; rfl
include hv
lemma tree_honest : Wilson.Honest (put f x):= by unfold Wilson.Honest; rw [tree_read]; apply ContDiffAt.comp _ _ (intoTree G n).contDiff.contDiffAt; rw [map_zero]; exact (hv.pays n x).born
lemma ticket_tree : Orb.PreTest (put f x):= by
    refine ⟨ fun g _ u=> putInvariant x hv.go g u, ⟨ (put_cont x hv.clean).comp Orb.continuous_links,?_⟩, put_cont x hv.clean ⟩; rw [orbit_read]; apply ContDiffAt.comp _ _ (outTree G n).contDiff.contDiffAt; rw [map_zero]; exact (hv.pays n x).born.of_le le_top
lemma treeGauge : Wilson.Physical (put f x):= fun t _ U => (congr_arg _ (Wilson.descends t U)).trans (putInvariant x hv.go _ _)

lemma pos_jet : ContDiffAt ℝ ω (put f x ∘ nation) 0:= (hv.pays n x).born
lemma travelFrom (hl : From F.val d) : From (Native.reads ((put f x) ∘ nation)) d:= by rw [← pinArt x hv]; exact FromShade (shown n F) (FromShade F hl _) _

def gamma (U:City G (Site n))(i:Branch G Axis)(x:Site n):ℝ:=match i with | ((some j,false),k)=> U (x,j) k|_=>0
omit hv in
lemma onSpace (U:City G (Site n)) : U= ∑ j:Pos G n, gamma U (j.1) j.2 • Native.direction j := by
    simp only [Fintype.sum_prod_type,Fintype.sum_option,gamma,direction,smul_zero,Finset.sum_const_zero,zero_add,Fintype.sum_bool]
    apply Eq.trans (Native.frame U).symm; simp_rw [Fintype.sum_prod_type,projector_k]; rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun j _=> Finset.sum_comm

lemma below (hl:From F.val d)(i:ℕ)(hi:i<d): jet ( (put f x) ∘ nation) i =0:= by
    funext u; apply jet_down (d:=d) (pos_jet hv x) u _ i hi
    rw [Taylor.scale_pos (V:=direction) («W»:=fun _:Unit=>u) (T:=fun (_:Unit) j=> gamma u j.1 j.2) (fun _=> onSpace u) (pos_jet hv x)]; exact FromShade _ (travelFrom hv x hl) _

lemma orbit_min (hl:From F.val d) (i:ℕ)(hi:i<d) : jet ((Orb.restrictedO (put f x)) ∘ expLinks G (Orb.Cotree n)) i=0:= by
    funext u; rw [ orbit_read, GermLaplace.jet_pull (outTree G n) _ ((pos_jet hv x).of_le le_top), below hv x hl i hi ]; rfl
omit hv in
lemma slice_read : Wilson.slice (plan G n) (put f x)= (put f x ∘ nation) ∘ LMap G n:= PairCoords.costing _
lemma slice_min (hl:From F.val d) (i:ℕ)(hi:i<d): jet (Wilson.slice (plan G n) (put f x)) i=0:= by
    funext u; rw [ slice_read (f:=f) x, GermLaplace.jet_pull (LMap G n) _ ((pos_jet hv x).of_le le_top), below hv x hl i hi ]; rfl

def stamp (hl:From F.val d): InversionTop.Stamp G n where
     stencil:= put f x
     test := ticket_tree hv x
     slots:= d
     cleared k hk:=by funext i; rw [row,InversionTop.raw,InversionTop.lift,InversionTop.into_coeff, PowerSeries.coeff_mk, orbit_min hv x hl _ hk ]; rfl
-- direct ticket and rental factor equation (full conditional data comes separately)
omit hv in
def seated (d:ℕ) (a:Weights G) : Ticket Fκ := MultiGauge.Stack.drop d (MultiGauge.Stack.rise (Wilson.slice (plan G n) (put a x)))
lemma roster (hl:From F.val d): X^d*seated x d f=MultiGauge.Stack.rise (Wilson.slice (plan G n) (put f x)):= by
    unfold seated; apply MultiGauge.Stack.recover; intro i hi; rw [MultiGauge.Stack.rise,coeff_mk]; apply Subtype.ext; exact slice_min hv x hl i hi

variable {U J:Type}(m:Module.Basis U ℝ (Wilson.Field G n))(b:Module.Basis J ℝ (Param G n))
omit hv in
lemma placedModel (k:ℤ) : Based.place G n x (Book.model k F)= mask k (Based.place G n x F):= by
    unfold Based.place; simp only [LinearMap.comp_apply,shown,Lab.Shift,transport, mod_ferry]; rfl

def chargedSeed (d:ℕ) (F:Dot G W): SpecB (Pos G n):= pointL ℕ (Based.place G n x) (Book.levels d F)
lemma charged_seat (d:ℕ) : seriesPlug (mkPlug m b) (chargedSeed x d F)= Score.bore m (seated x d f):= by
    funext i; change plug (mkPlug m b) (Based.place G n x _) = _; unfold seated; rw [Score.bore, sharp_coe,MultiGauge.Stack.drop, coeff_mk]; change plug _ (Based.place G n x (Book.model (i+d) F))= _; rw [ placedModel, PairCoords.cap_stem,pinArt x hv,pin_read m b (pos_jet hv x),← slice_read (f:=f) x, MultiGauge.Stack.rise, coeff_mk,Nat.add_comm d i]; simpa only [Nat.cast_add] using (masked (bell m) _ (slice_hot (plan G n) (treeGauge hv x) (tree_honest hv x)) (i+d))
end YM.FVA2.Source
