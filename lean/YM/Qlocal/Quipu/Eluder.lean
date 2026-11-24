import YM.Qlocal.Quipu.Needle
import YM.Qlocal.Quipu.Verge
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Quipu.Eluder
open AllOrder AllOrder.Ink Floe
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace Laplace.SigmaP Ker Ker.Start
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response Ink Ink.Method Ink.Money GaussianScore Module
open Tree Wilson PhysicalNext Repeat Lapis ConnectedActivityE6 Blaze Precision Push Pressure Next.Fluctuations Next.SectorChange MeasureTheory
open Kinetic.Port
open Bloch hiding direct
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
open Turbin Sonnet Marker Kinetic Primitives.GCC.Anchor
variable {ι α :Type}[Fintype α][DecidableEq α][Fintype ι] {G:Gauge} {n:Side} {k N :ℕ} {a b r :ℝ}{R:Marker.Census α}
local notation "J"=> ι⊕α
local notation "E"=> rule J n
local notation "A"=> rule ι n
local notation "B"=> rule α n
local notation "Λ"=> Leaf n J
-- extend wall across both legs. χ preserves quiet.𝒮
variable (x:rule ι n)(o:α→Site n) (Z:R.Mode)
protected noncomputable def χ (R:Marker.Census α) (x: rule ι n)(o:α → Site n) : Leaf n (ι⊕α) → Poly R
 | ⟨z,.inl v⟩ => algebraMap ℝ (Poly R) (x (z,v))
 | ⟨z,.inr v⟩ => viewed R o (z,v)
-- syntax opaque step.L
local notation "θ"=> (Eluder.χ R x o)
local notation "X"=> θ -- parse potential coll.
noncomputable abbrev θwall (R:Marker.Census α) (o:α→Site n)(F:rule (ι⊕α) n→ℝ) (x:rule ι n):= wall (Eluder.χ R x o) F
variable (i:Leaf n (ι⊕α))
variable {f g:rule (ι⊕α) n→ℝ} (w:α)
abbrev away (Z:R.Mode)(w:α):= Primitives.GCC.Anchor.diff Z ({w}:Finset α)
omit [Fintype α] in
lemma slide (u:Poly R): (u * Poly.send (R.fire w) 1).part Z = if w∈Z.val then u.part (away Z w) else 0:= by rw [mul_comm,mul_at_part]; simp only [one_mul, Census.fire, singleton_subset_iff]
omit [Fintype α] in
lemma idle (u:Poly R)(x:ℝ)(Z:R.Mode): (u*algebraMap ℝ (Poly R) x).part Z=u.part Z * (x:ℂ):= by rw [mul_comm u,← Algebra.smul_def, mul_comm (u.part Z)]; rfl
-- derivative basis selector only marker. Basis.Constant.Mirror.
abbrev loc (ι:Type)(o:α→ Site n)(w:α) : Leaf n (ι⊕α):=(o w,Sum.inr w)
local notation "q"=> bolt (loc ι o w) -- `bolt` classical stack
local notation "S"=> away Z w
local notation "T"=> wall θ
abbrev ξ (i:Λ): E →L[ℝ] ℝ:= ContinuousLinearMap.proj (φ:=fun _ : Leaf n (ι⊕α)=>ℝ) i
private lemma kinetic : diff' (q) (ξ i) = @ite _ (i=loc ι o w) (Classical.propDecidable _) (fun _=>1) (fun _=>0):= by
 letI : DecidableEq (Leaf n (ι⊕α)):= fun a b=> Classical.propDecidable _
 ext v; simp_rw [diff', (ξ i).fderiv]; split
 next he=> change bolt (loc ι o w) i= _; rw [he,bolt,Pi.single_eq_same]
 next he=> change bolt (loc ι o w) i=_; unfold bolt; exact Pi.single_eq_of_ne he 1
local notation "L"=> (ξ i)
abbrev Prob (x:A)(v:α)(o:α→Site n)(F:E→ℝ)(B0:Marker.Census α): Prop:= ∀ Z:B0.Mode,v∈ Z.val→ (wall (Eluder.χ B0 x o) F).part Z = (wall (Eluder.χ B0 x o) (diff' (bolt (loc ι o v)) F)).part (away Z v)
set_option quotPrecheck false
variable (p:Ch (Leaf n (ι⊕α)))
lemma money (h:Plausible f) : (wall (Eluder.χ R x o) f).part R.quiet= ↑(f (mingle x 0)):= by
 obtain ⟨p,rfl⟩:= sold h
 clear h; induction p using MvPolynomial.induction_on with
 | C x=> rw [guide_const,sky_c]; exact (Poly.part_send ..).trans (if_pos rfl)
 | add a b i j=> rw [guide_add,pours_a _ (bill a) (bill b), Poly.part_plus,i,j,Pi.add_apply,Complex.ofReal_add] -- type F. add ∀.
 | mul_X p j hi=>
    let l:= guide p; let H:=guide (MvPolynomial.X j); rw [guide_mul,pours_m _ (bill p) (bill ..),guide_col,sky_x, Poly.quiet_mul,hi,Pi.mul_apply,Complex.ofReal_mul]; rcases j with ⟨i,v|v⟩; · exact congr_arg (((guide p (mingle x 0):ℝ):ℂ)*·) ((Poly.part_send ..).trans (if_pos rfl))
    simp only [Eluder.χ, viewed]; split
    next he=> have hx : R.quiet ≠ R.fire v:= by intro H; have hg:= congr_arg (fun z:R.Mode=> z.val) H; simp [Census.quiet,Census.fire] at hg
              rw [Poly.part_send, if_neg hx]; change _= _*(↑(0:ℝ):ℂ); rw [Complex.ofReal_zero]
    change _*(0:Complex) = _*↑(0:ℝ); rw [Complex.ofReal_zero]
lemma times_c (hf:Plausible f)(hp:Prob x w o f R)(he:w∈Z.val) : (T (f * ↑(L))).part Z=(T (diff' (q) (f*↑(L)))).part S:= by
 let s:= S; let y:=loc ι o w; let u:= T f; let k:=q; have hL:Plausible (ξ i) := Plausible.line (ξ i).toLinearMap; have h0 : T (ξ i)= θ i:= Turbin.sky_x ..; let v:= T (diff' k f)
 rw [pours_m _ hf hL,mults hf hL, pours_a _ ((hf.ds _).mul hL) (hf.mul (hL.ds _)), pours_m _ (hf.ds _) hL, pours_m _ hf (hL.ds _), Poly.part_plus,h0,kinetic]; split
 next hg=>
    have heq: θ i=Poly.send (R.fire w) 1:= by rw [hg,Eluder.χ, viewed, if_pos rfl]
    rw [sky_c, heq,map_one,mul_one, slide, slide,if_pos he,if_neg (show w∉s.val from fun h=> (mem_sdiff.mp h).2 (mem_singleton_self w)),zero_add]
 next hg=>
    rw [sky_c,map_zero,mul_zero, Poly.part_nil,add_zero]
    have hv:=(hp Z he);
    rcases i with ⟨i,v'|v'⟩ <;> simp_rw [Eluder.χ]
    · rw [idle,idle]; exact congr_arg (·*_) hv
    simp only [viewed]; split
    next hg'=>
       have hz: v'≠w:= by rintro H; exact hg (Prod.ext (by simpa [H] using hg') (congr_arg Sum.inr H))
       have hx : v'∈Z.val ↔ v'∈s.val:= ⟨fun h=> mem_sdiff.mpr ⟨h,fun h=>hz (mem_singleton.mp h)⟩, fun h=>(mem_sdiff.mp h).1⟩; rw [slide,slide]
       by_cases hv':v'∈ Z.val; swap; · rw [if_neg hv',if_neg (mt hx.mpr hv')]
       rw [if_pos hv',if_pos (hx.mp hv'),hp (away Z v') (show w∈(away Z v').val from mem_sdiff.mpr ⟨he,fun h=> hz.symm (mem_singleton.mp h)⟩)]; apply congr_arg; apply Subtype.ext; ext; simp only [away, Primitives.GCC.Anchor.diff]; rename_i z; change z∈ (Z.val\{v'})\{w} ↔ z∈(Z.val\{w})\{v'}; simp_rw [Finset.mem_sdiff]; tauto
    next hx=> rw [mul_zero,mul_zero,Poly.part_nil,Poly.part_nil]
-- The estimate below applies to each plausible polynomial.
lemma owns (hp:Plausible f): Prob x w o f R := by
 obtain ⟨p,hp⟩:= Turbin.sold hp; rw [← hp]; clear hp;
 induction p using MvPolynomial.induction_on with
 | C c => intro Z he;
          rw [guide_const,sky_c, dift]; erw [sky_c, map_zero, Poly.part_nil]; refine (Poly.part_send ..).trans (if_neg ?_); rintro H; simp_rw [H] at he; exact notMem_empty _ he
 | add a b i j=>
    intro Z he; have hu:= bill a; have hv:=bill b; rw [guide_add,pours_a _ hu hv, adds hu hv, pours_a _ (hu.ds _) (hv.ds _), Poly.part_plus,Poly.part_plus,i Z he,j Z he]
 | mul_X p j hi=>
    intro Z he; rw [guide_mul,guide_col]; exact times_c x o Z j w (bill p) hi he
end YM.Qlocal.Quipu.Eluder
