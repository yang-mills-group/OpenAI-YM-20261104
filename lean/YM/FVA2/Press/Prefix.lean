import YM.FVA2.Press.Lead
/-!
# Physical A-only cover polynomials on a panel, and their MS cylinder jets
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Press
open Function Set Filter Finset MeasureTheory Lattice Wilson RG Labels Source Source.Drops Bid Work XSpace
open MS MS.Koszul MS.Cylinder Lab MS.Native MS.Native.Sew MS.Book MS.Local.Physical MS.Rake MS.Lifting MS.Theater
open scoped BigOperators Topology ContDiff Classical Matrix.Norms.Frobenius
variable {G:Gauge} {d:ℕ} {H:Hol G} (A:XSpace.Survey G H d)
local notation "T" => Fin A.size
local notation "J" => Local A
local notation "E" => tilt A
local notation "V" => CoverConfig G
local notation "B" => GaugePanel G A.size
local notation "X" => Edge Cover
local notation "P" => Labels.Pol G
local notation "ζ" => Subtype.val (p:=fun x:X=>x∈ knots A)
variable (p: Labels.Pol G)

-- keep real evaluation (for Stencil.obs) and complex linear extension (for proofs)
def wheel (p:Labels.Pol G) (U:CoverConfig G) := read (expand d (A.recover (mapped A.looks U))) p
def window (p:Labels.Pol G) : tilt A → ℂ := wheel A p ∘ pad A
def pigment (p:Labels.Pol G) : tilt A→ ℝ:= fun v=> (window A p v).re
def front (p:Labels.Pol G): tilt A→ℝ:= fun v=> (window A p v).im
lemma style (F : Labels.Frame G d) (K : SectionData F)(h:A.Represents F K)(v: Labels.Label G d)(U:CoverConfig G): K.evaluate (F.coords v) U=wheel A v.val U:= h.2.2 ..
lemma colored (h:p∈Labels.invariantSpace G) : Lattice.GaugeInvariant (wheel A p):= by
 intro u x; change read (expand d (A.reading _)) _=_; rw [ A.reading_gauge, show ∀ y: Snap G d, expand d (Cast (u 0) y)=Labels.colored (u 0) (expand d y) from ?_ ]; exact h ..
 intro y; ext1 i; by_cases H:i<d-1<;> simp [expand,H,Cast,Labels.colored]
lemma hot (F:Labels.Pol G) : ContDiff ℝ ω (window A F) := (Work.G05.snap_read_smooth d F ω).comp (A.recover_smooth.comp (lamp_smooth A))
lemma pigment_hot : ContDiff ℝ ω (pigment A p) := Complex.reCLM.contDiff.comp (hot A p)
lemma front_hot : ContDiff ℝ ω (front A p) := Complex.imCLM.contDiff.comp (hot A p)

def dot (p:Labels.Pol G) := Sew.art (fun i: Local A=> i.val) (pigment A p)
def sat (p:Labels.Pol G) := dot A p+ Complex.I • Sew.art (fun i:Local A=>i.val) (front A p)
lemma add_art {f g: tilt A → ℝ} (h:ContDiffAt ℝ ω f 0)(k:ContDiffAt ℝ ω g 0) : Sew.art ζ (f+g)= Sew.art ζ f + Sew.art ζ g:= by rw [ Sew.art,MS.Cylinder.Taylor.ink_add _ h k,map_add,map_add]; rfl
lemma smul_art {f:tilt A →ℝ}(p:ℝ)(h:ContDiffAt ℝ ω f 0): Sew.art ζ (p • f)= (p:ℂ) • Sew.art ζ f:= by rw [Sew.art,Taylor.ink_smul _ h,map_smul,map_smul]; rfl
lemma times_art {f g: tilt A→ℝ}(h:ContDiffAt ℝ ω f 0)(k:ContDiffAt ℝ ω g 0): Sew.art ζ (f*g)= couple Draft.DotFlip (Sew.art ζ f) (Sew.art ζ g):= by
 let v : Sector (Local A × G.ColorIndex):= fun _=>false; unfold Sew.art; rw [← ferry_pair (q:=Draft.DotFlip) (p:=v) (knot ζ) (fun _=>rfl)]; congr 1; apply Subtype.ext; exact MS.Cylinder.Taylor.ink_mul _ (fun _ h=>  (by contradiction)) h k
lemma art_zero : Sew.art ζ (0:E→ℝ)=0:= by rw [Sew.art,MS.Cylinder.Taylor.ink_zero,map_zero,map_zero]
lemma art_one : Sew.art ζ (1:E→ℝ)= Cylinder.piece (1:ℂ):= by
 unfold Sew.art; rw [show MS.Cylinder.Taylor.ink priv (1:E→ℝ)= coin (A:=Local A × G.ColorIndex) (1:ℂ) from ?_]; · exact coin_settled ..
 exact Taylor.ink_const _ _

lemma sat_add (f g:P): sat A (f+g)=sat A f+sat A g:= by
 unfold sat dot; rw [show pigment A (f+g)= pigment A f+ pigment A g from funext (fun x=> by simp only [pigment,window,wheel, comp_apply, map_add, Complex.add_re,Pi.add_apply]), show front A (f+g)=front A f +front A g from funext (fun x=> by simp only [front,window,wheel,comp_apply,map_add,Complex.add_im,Pi.add_apply]), add_art A (pigment_hot A f).contDiffAt (pigment_hot A g).contDiffAt, add_art A (front_hot A f).contDiffAt (front_hot A g).contDiffAt, smul_add ]; abel
lemma sat_zero : sat A 0=0:= add_right_cancel (b:=sat A 0) (by simp only [←sat_add A,zero_add] )
lemma sat_real (h:Labels.conjPol p=p) : sat A p=dot A p:= by
 unfold sat; rw [show front A p=0 from ?_, art_zero, smul_zero, add_zero]
 funext x; have he:= (Labels.conj_value p (expand d (A.recover (mapped A.looks (pad A x))))); rw [h] at he; exact (Complex.conj_eq_iff_im.mp he.symm)
lemma sat_X (i:Key G): sat A (MvPolynomial.X i)= Integration.mounted A i:= by
 rw [sat_real A _ (by simp [Labels.conjPol])]; unfold dot; rw [show pigment _ (MvPolynomial.X i)=Integration.box A i from funext (?_ : ∀ x, pigment A (MvPolynomial.X i) x=Integration.box A i x)]; · rfl
 intro x; unfold pigment window wheel; rw [comp_apply, Labels.read, MvPolynomial.aeval_X]; rfl
lemma sat_l (i: Key G)(p:P): sat A (MvPolynomial.X i*p)= couple Draft.DotFlip (Integration.mounted A i) (sat A p):= by
 let f:= Integration.box A i
 have he (x:E) : window A (MvPolynomial.X i*p) x = ↑(f x)* window A p x:= by unfold window wheel; rw [comp_apply, map_mul]; unfold Labels.read; rw [MvPolynomial.aeval_X]; rfl
 have hh: pigment A (MvPolynomial.X i*p)=f* pigment A p:= by funext x; simp only [pigment,he,Complex.mul_re, Complex.ofReal_re,Complex.ofReal_im, Pi.mul_apply,zero_mul,sub_zero]
 have hi: front A (MvPolynomial.X i*p)=f*front A p:= by funext x; simp only [front,he,Complex.mul_im, Complex.ofReal_re,Complex.ofReal_im, Pi.mul_apply,zero_mul,add_zero]
 rw [sat,dot,hh,hi,times_art A (Integration.hot A i).contDiffAt (pigment_hot A p).contDiffAt,times_art A (Integration.hot A i).contDiffAt (front_hot A p).contDiffAt]; unfold sat; rw [map_add, map_smul];rfl
lemma sat_constant (x:ℂ): sat A (MvPolynomial.C x)= x • Cylinder.piece (1:ℂ):= by
 unfold sat dot; rw [show pigment _ _=x.re • (1:E→ℝ) from ?_,show front _ _=x.im •(1:E→ℝ) from ?_, smul_art A x.re (f:=1) contDiffAt_const,smul_art A x.im (f:=1) contDiffAt_const,art_one,smul_smul,←add_smul];
 · rw [mul_comm Complex.I, Complex.re_add_im]
 · funext y; simp [front,window,wheel, Labels.read]
 funext y; simp [pigment,window,wheel, Labels.read]
end YM.FVA2.Press
