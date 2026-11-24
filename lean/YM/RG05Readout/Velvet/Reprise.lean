import YM.RG05Readout.Velvet.Arrivals
import YM.Contact.Stencil
/-! Center integral of cut-combined raw product on ANY alignment
 width. Uses full shop.Support measure.Factors maintain native translation
 EXACT positive rectangle.Room. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Velvet
open Function MeasureTheory Set Filter Topology Pulse Native Address Many Lattice Wilson Extraction WithLp Nuclear Bay Cells Harvest Halls
open RG MergeProof Flatten PhysicalNext.Repeat Legato Dash Extraction.Lease Petals Push.RelayDifference
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
set_option quotPrecheck false
variable {G:Gauge}{C:Family G}{v j:ℕ}{q R η:ℝ}
local notation "δ"=> C.S.a
variable (D:Poem C j) {s:Fin v→ℕ}{Ψ:Wave (Fin v)} (h:Sky Ψ R η)
open Chalice Poem
variable (he:0<q)(hp:R*q<C.S.a j/2)
local notation "H"=> telegram D h he hp
local notation "I"=> Fin v
local notation "V"=> Points v
local notation "Z"=> Points D.n
local notation "E"=> Points (v+D.n)
variable (S:YM.Table C.book)(hS:S.Hierarchy) (x:(i:Fin v)→C.label (s i))
def fleet (s:Fin v→ℕ)(x:∀ i,C.label (s i))(D:Poem C j):=Fin.append (fun i:I=>(⟨s i,x i⟩:C.book.Token)) D.token
local notation "X"=> fleet s x D
local notation "F!"=> fun (x:Points (v+D.n))=> S.read x X
local notation "T"=> integrated H s D.token x S
local notation "g!"=> D.opening
local notation "P"=> pluck D
local notation "Q"=> pad Ψ g! q
local notation "p!"=> ∏ _i:Fin v,(q:ℂ)⁻¹^4
include hS
lemma ripple_t : T=∫ u:V,∫ y:Z,blurb D Ψ q (u,y)*F! (ribbon u y):=by
   let R:= stripe v D.n; let f:=fun u:E=> H u * S.read u X; let e:=R.symm.toHomeomorph.toMeasurableEquiv; have he':MeasurePreserving e:=MeasurePreserving.symm (e:=e.symm) (stitches (m:=v) (n:=D.n)) -- def implicit
   have hf : Integrable f:= Test.smearing H (S.smooth_read hS.smooth X).continuousOn; have h': Integrable (f∘e):= (he'.integrable_comp_emb e.measurableEmbedding).2 hf
   rw [show T=∫ x:E,f x from rfl, ← he'.integral_comp e.measurableEmbedding f]; change (∫ x: _ , (f∘ e) x ∂volume.prod volume)=_; rw [integral_prod _ h']; change _=∫ u:V, ∫ y:Z,_; refine integral_congr_ae (Eventually.of_forall (fun u=>integral_congr_ae (Eventually.of_forall (fun y=>?_)))); unfold f; exact congr_arg₂ (·*·) (telegram_read h D he hp _ _) rfl -- orientation
-- Parametric retreat with center normalization and radius.Remote support.
omit hS in
lemma reprise_sub (u:V):
   (∫ y:Z,blurb D Ψ q (u,y)*F! (ribbon u y))=∫ z:E4,∫ y:Z, (D.opening.val z * pattern Ψ (overturn q z u) * P y) * S.read (ribbon u y) X:=by
   let f(y:Z):=P y * S.read (ribbon u y) X
   let t(z:E4):= D.opening.val z * pattern Ψ (overturn q z u); let r:= (pattern (molten Ψ q (boxC D)) u)
   have he': r= ∫ z:E4,t z:=by simp only [t, ← shaped (Ψ:=Ψ)]; exact glow_point ..
   calc
    _ = ∫ y:Z, r*f y:=by unfold blurb r f; simp only [mul_assoc]
    _ = ∫ z:E4,t z*(∫ y:Z,f y):=by rw [integral_const_mul,integral_mul_const,he']
    _ = _:=by unfold t f; simp_rw [← integral_const_mul, mul_assoc]
omit hS in
/-- continuous on genuine supports, no modification of K off diagonal. -/
lemma mul_joint {X_ Y:Type}[TopologicalSpace X_][NormedAddCommGroup Y][NormedSpace ℂ Y] (F:X_→ℂ)(V₁:X_→Y)(hF:Continuous F)(hV:∀ x∈tsupport F,ContinuousAt V₁ x): Continuous (fun x=>F x • V₁ x):=by
   apply continuous_iff_continuousAt.mpr; intro x; by_cases hx:x∈tsupport F; exact hF.continuousAt.smul (hV x hx)
   apply continuousAt_const.congr (f:=fun _=> (0:Y)) -- check
   filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with i hi; rw [show F i=0 from hi,zero_smul]
local notation "G!"=> tsupport (D.opening.val)
local notation "Y!"=> Points v × (E4 × Points D.n)
noncomputable def wool (Ψ:Wave (Fin v))(D:Poem C j)(q:ℝ)(y:Points v × (E4 × Points D.n)):= (D.opening.val y.2.1 * pattern Ψ (overturn q y.2.1 y.1) * pluck D y.2.2)
local notation "W"=> wool Ψ D q
variable {y₀:Points v ×(E4×Points D.n)}
omit hS
include he h
lemma wool_pad : tsupport (wool Ψ D q)⊆ pad Ψ D.opening q ×ˢ (tsupport (D.opening.val) ×ˢ rim D):=by
   apply closure_minimal _ ((padSmall (q:=q) (boxC D) h.park).prod ((boxC D).prod (rimSmall D))).isClosed; rintro ⟨u,z,y⟩ hx
   change D.opening.val z* _ * _ ≠0 at hx; have hv := left_ne_zero_of_mul hx; have hZ:z∈ G!:=subset_closure (left_ne_zero_of_mul hv); have he': overturn q z u ∈ scoreHull Ψ:= patterned_sub (subset_closure (right_ne_zero_of_mul hv)); exact ⟨⟨(z,overturn q z u),⟨hZ,he'⟩, unturned he _ _⟩,⟨hZ,pluck_mem D (subset_closure (right_ne_zero_of_mul hx))⟩⟩
omit h he
lemma begin_cont : Continuous (fun p:E4× Points v=>beginAt q p.fst p.snd):=by unfold beginAt; exact Continuous.add ((bag v).symm.continuous.comp (continuous_pi fun _=> continuous_fst)) (continuous_snd.const_smul q)
lemma wool_cont : Continuous (wool Ψ D q):=by
   let t(p:Y!):=p.2.1; have ht:Continuous t:=continuous_fst.comp continuous_snd
   let B(x:E4):Points v:=points (fun _=>x); have hb:Continuous B:=(bag v).symm.continuous.comp (continuous_pi fun _=> continuous_id)
   let A(x:Y!):=overturn q (t x) x.1; have hv:Continuous A:=(Continuous.sub continuous_fst (hb.comp ht)).const_smul q⁻¹
   have he: Continuous (pattern Ψ):=(Pulse.lit Ψ 0|>.continuous).comp (bag v).continuous
   exact Continuous.mul (((Pulse.lit («E»:=E4) g! 0|>.continuous).comp ht).mul (he.comp hv)) ((pluckSmooth D).continuous.comp (continuous_snd.comp continuous_snd))
include hS h hp he
noncomputable def fleece (Ψ:Wave (Fin v))(q:ℝ)(y:Points v ×(E4×Points D.n)):ℂ:= wool Ψ D q y * S.read (ribbon y.1 y.2.2) X
local notation "C!"=>fleece D S x Ψ q
lemma fleeced : Integrable (fleece D S x Ψ q):=by
   let f(y:Y!):= S.read (ribbon y.1 y.2.2) X
   have hv: ∀ x∈tsupport W, ContinuousAt f x:=by
      intro t ht; obtain ⟨hq,h1,h2⟩:=wool_pad D h he ht -- implicit
      have hξ:= enclave h D he hp hq h2
      refine (ContinuousAt.comp (g:=F!) (((S.smooth_read hS.smooth X).continuousOn _ hξ).continuousAt ((conf_open _).mem_nhds hξ)) ((Continuous.comp (stripe v D.n).symm.continuous (continuous_fst.prodMk (continuous_snd.comp continuous_snd))).continuousAt))
   have hx: Continuous (C!):=mul_joint W f (wool_cont D) hv
   apply hx.integrable_of_hasCompactSupport; exact (show HasCompactSupport W from ((padSmall (q:=q) (boxC D) h.park).prod ((boxC D).prod (rimSmall D))).of_isClosed_subset isClosed_closure (wool_pad D h he)).mul_right -- lemma?
local notation "M!"=> ∏ _i:I,(q:ℂ)⁻¹ ^4
omit hS h hp in
lemma floatT (u:E4)(F : V→ℂ) : (∫ x:V,F (beginAt q u x))=(∏ _i:I,(q:ℂ)⁻¹ ^4)*(∫ x:V,F x):=by
   let v':V:= points (fun _=>u); let g(x:V):=F (v'+x)
   have hv:(∫ x:V,F (beginAt q u x))=(∫ x:V,g (q • x)):=rfl
   have ht:(∫ x:V,g x)=∫ x:V,F x:=integral_add_left_eq_self ..
   rw [hv,MeasureTheory.Measure.integral_comp_smul_of_nonneg volume _ q (hR:= he.le),ht,Contacts.rank_relative_sq, Complex.real_smul,Finset.prod_const,Finset.card_univ,Fintype.card_fin,← pow_mul]; push_cast; rw [←inv_pow]
-- choose integral over product directly. y family.Margin not smeared hull.Scalar insertion right below.
def cardReading (q:ℝ)(Ψ:Wave (Fin v)) (t: E4 × Points D.n) (u:Points v) :ℂ := (D.opening.val t.1 * pluck D t.2 * pattern Ψ u) * S.read (ribbon (beginAt q t.1 u) t.2) X
local notation "C0"=>cardReading D S x q Ψ
lemma melody : p! * T=∫ z:E4×Points D.n,∫ u:V,C0 z u:= by
   let f:= fleece D S x Ψ q; let μ:= (volume : Measure (Points v)); let ν:= (volume:Measure E4).prod (volume :Measure (Points D.n))
   have hf: Integrable f (μ.prod ν):= fleeced D h he hp S hS x
   have ht :(∫ z, f z ∂μ.prod ν) = T:=by
       rw [ripple_t, integral_prod _ hf]; swap; exact hS
       apply integral_congr_ae;filter_upwards [hf.prod_right_ae] with u hu; exact (integral_prod _ hu).trans (reprise_sub D S x u).symm
   rw [← ht, integral_prod_symm _ hf, ← integral_const_mul]; refine integral_congr_ae (Eventually.of_forall (fun y=> ?_)); let w(u:Points v):= f (u,y); dsimp only; rw [show _*(∫ u,f (u,y)∂μ) = ∫ u:V,w (beginAt q y.1 u) from (floatT he y.1 w).symm]; apply integral_congr_ae; filter_upwards with i; unfold w f fleece wool cardReading; dsimp only; rw [turned he]; ring
end YM.RG05Readout.Velvet
